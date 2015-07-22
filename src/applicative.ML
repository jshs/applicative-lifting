signature APPLICATIVE =
sig
  type tvar = indexname * sort;
  type sign =
   {pure: term * tvar,
    ap: term * tvar * tvar,
    tycon: typ * tvar,
    sort: sort}
  val lift_type: sign -> typ -> typ
  val pure: sign -> typ -> term
  val ap: sign -> typ * typ -> term
  val lift: sign -> term -> term
  val apply: sign -> typ * typ -> term * term -> term
  val mk_sign: Proof.context -> term * term -> sign

  type laws =
   {identity: thm,
    composition: thm,
    homomorphism: thm,
    interchange: thm}
  type afun;
  val sign_of: afun -> sign;
  val laws_of: afun -> laws;
  val mk_afun: Proof.context -> sign * laws -> afun
  val add_C_comb: thm -> afun -> afun
  val add_generic: afun -> Context.generic -> Context.generic
  val add_global: afun -> theory -> theory
  val get: Context.generic -> term -> afun

  val normalform_conv: Proof.context -> afun -> conv
  val normalize_eq_conv: Proof.context -> afun option -> conv
  val normalize_eq_tac: Proof.context -> int -> tactic
  val lifting_nf_tac: Proof.context -> int -> tactic

  type tterm
  val analyze_expressions: Proof.context -> afun -> term * term -> tterm * tterm
  val consolidate: Proof.context -> afun -> tterm * tterm -> int list list
  val eliminate: Proof.context -> afun -> tterm -> int list * term -> tterm * thm
  val generalized_nf: Proof.context -> afun -> term * term -> thm * thm
end;

structure Applicative : APPLICATIVE =
struct

type tvar = indexname * sort;

type sign =
 {pure: term * tvar,
  ap: term * tvar * tvar,
  tycon: typ * tvar,
  sort: sort};

fun lift_type {tycon = (tycon, v), ...} T = Term_Subst.instantiateT [(v, T)] tycon;
fun pure {pure = (pure, v), ...} T = Term_Subst.instantiate ([(v, T)], []) pure;
fun ap {ap = (ap, v1, v2), ...} (T1, T2) = Term_Subst.instantiate ([(v1, T1), (v2, T2)], []) ap;
fun lift sign t = pure sign (Term.fastype_of t) $ t;
fun apply sign T (t1, t2) = ap sign T $ t1 $ t2;

(* TODO user-friendly error messages *)
fun mk_sign ctxt (raw_pure, raw_ap) =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun closed_poly_term t =
      let val poly_t = singleton (Variable.polymorphic ctxt) t;
      in if null (Term.add_vars (singleton
          (Variable.export_terms (Variable.auto_fixes t ctxt) ctxt) t) [])
        then if null (Term.hidden_polymorphism poly_t)
          then poly_t
          else error "Additional type variables"
        else error "Free variables"
      end;

    val pure = closed_poly_term raw_pure;
    val (pure_argT, afT) = Term.dest_funT (Term.fastype_of pure);
    val tvar as (_, sort) = Term.dest_TVar pure_argT;
    val _ = if null (subtract (op =) (Term.add_tvars pure []) [tvar])
      then ()
      else error "Additional polymorphic type variables";

    val ap = closed_poly_term raw_ap;
    val (ap_argT1, (ap_argT2, ap_resT)) = Term.fastype_of ap
        |> Term.dest_funT
        ||> Term.dest_funT;
    val idx = Variable.maxidx_of ctxt + 1;
    val matcher1 = Sign.typ_match thy (afT, ap_argT2) Vartab.empty;
    val ap_tvar1 = case Type.lookup matcher1 tvar of
        SOME v => Term.dest_TVar v
      | NONE => (("'a", idx), sort);
    val matcher2 = Sign.typ_match thy (afT, ap_resT) Vartab.empty;
    val ap_tvar2 = case Type.lookup matcher2 tvar of
        SOME v => Term.dest_TVar v
      | NONE => (("'b", idx), sort);
    (* TODO check sorts of ap_tvar{1,2} *)
    val _ = if ap_argT1 = Term_Subst.instantiateT [(tvar, TVar ap_tvar1 --> TVar ap_tvar2)] afT
      then ()
      else error "Incompatible types";
  in
   {sort = sort, pure = (pure, tvar), ap = (ap, ap_tvar1, ap_tvar2), tycon = (afT, tvar)}
  end;


type laws =
 {identity: thm,
  composition: thm,
  homomorphism: thm,
  interchange: thm};

type nf_rules =
 {leaf: thm,
  merge: thm,
  swap: thm,
  rotate: thm,
  pure_rotate: thm};

type combinators =
 {I: thm,
  B: thm,
  C: thm option,
  K: thm option,
  W: thm option,
  S: thm option};

type afun =
 {sign: sign,
  laws: laws,
  nf_rules: nf_rules,
  combinators: combinators};

val sign_of = #sign;
val laws_of = #laws;

fun basic_combinators (i, b) = {I = i, B = b, C = NONE, K = NONE, W = NONE, S = NONE};
fun has_C (comb: combinators) = is_some (#C comb);
fun has_K (comb: combinators) = is_some (#K comb);
fun has_W (comb: combinators) = is_some (#W comb);

fun consts_of {sign = {pure, ap, ...}, ...} = (#1 pure, #1 ap);
val afun_ord = prod_ord Term_Ord.fast_term_ord Term_Ord.fast_term_ord o apply2 consts_of;

structure Data = Generic_Data
(
  type T = afun Ord_List.T;
  val empty = [];
  val extend = I;
  val merge = Ord_List.merge afun_ord;
);

fun mk_afun ctxt (sign, laws) =
  let
    val leaf_rule = Thm.symmetric (#identity laws RS eq_reflection)
        |> Raw_Simplifier.rewrite_rule ctxt [@{thm Applicative.id_unfold}];
    val merge_rule = #homomorphism laws RS eq_reflection;
    val swap_rule = #interchange laws RS eq_reflection;
    val rotate_rule = Thm.symmetric (#composition laws RS eq_reflection)
        |> Raw_Simplifier.rewrite_rule ctxt [@{thm Applicative.comp_unfold}];

    val ([t1, t2, t3, gvar, fvar, xvar], ctxt') = Variable.variant_fixes
        ["'a", "'b", "'c", "g", "f", "x"] ctxt;
    val T1 = TFree (t1, #sort sign);
    val T2 = TFree (t2, #sort sign);
    val T3 = TFree (t3, #sort sign);
    val g = Free (gvar, T2 --> T3);
    val f = Free (fvar, lift_type sign (T1 --> T2));
    val x = Free (xvar, lift_type sign T1);
    val lhs = ap sign (T2, T3) $ lift sign g $ (ap sign (T1, T2) $ f $ x);
    val comp_g = Abs ("f", T1 --> T2, Abs ("x", T1, g $ (Bound 1 $ Bound 0)));
    val rhs = ap sign (T1, T3) $ (ap sign (T1 --> T2, T1 --> T3) $ lift sign comp_g $ f) $ x;
    val prop = Logic.mk_equals (lhs, rhs);
    (* FIXME refine tactic *)
    val tac = HEADGOAL (Raw_Simplifier.rewrite_goal_tac ctxt' [rotate_rule, merge_rule] THEN'
        rtac reflexive_thm);
    val rule = Goal.prove ctxt' [] [] prop (K tac);
    val pure_rotate_rule = singleton (Variable.export ctxt' ctxt) rule;

    val rules = {leaf = leaf_rule, merge = merge_rule, swap = swap_rule, rotate = rotate_rule,
      pure_rotate = pure_rotate_rule};

    val combinators = basic_combinators (leaf_rule, rotate_rule);
  in {sign = sign, laws = laws, nf_rules = rules, combinators = combinators} end;

fun add_C_comb thm {sign, laws, nf_rules, combinators = {I, B, C = _, K, W, S}} =
    {sign = sign, laws = laws, nf_rules = nf_rules, combinators =
      {I = I, B = B, C = SOME (Thm.symmetric thm), K = K, W = W, S = S}};

val add_generic = Data.map o Ord_List.insert afun_ord;
fun add_global af = Context.theory_map (add_generic af);

fun mk_op_pattern t (0, _) = t
  | mk_op_pattern t (n, i) =
    let val v = Var ((Name.uu, i + 1), dummyT)
    in mk_op_pattern (t $ v) (n - 1, i + 1) end;

fun get context t =
  let
    val thy = Context.theory_of context;
    fun pat t n = mk_op_pattern t (n, maxidx_of_term t);
    fun matches af = Pattern.matches thy (pat (af |> #sign |> #ap |> #1) 2, t) orelse
        Pattern.matches thy (pat (af |> #sign |> #pure |> #1) 1, t);
    fun lookup afs = (case find_first matches afs of
        SOME x => x
      | NONE => raise TERM ("Applicative.get", [t]));
  in lookup (Data.get context) end;


(** normal form conversion **)

(* FIXME possibly broken if pure/ap are beta-redexes *)

val clean_name = perhaps (perhaps_apply [try Name.dest_skolem, try Name.dest_internal]);

(* based on term_name from Pure/term.ML *)
fun term_to_vname (Const (x, _)) = Long_Name.base_name x
  | term_to_vname (Free (x, _)) = clean_name x
  | term_to_vname (Var ((x, _), _)) = clean_name x
  | term_to_vname _ = Name.uu;

fun rename_rewr_conv mk_map rule ct =
  let val rule' = Drule.rename_bvars (mk_map (Thm.term_of ct)) rule
  in Conv.rewr_conv rule' ct end;

fun rename_rr_conv v = rename_rewr_conv (fn t =>
    (case t of
        _ $ (_ $ t') => [(v, term_to_vname t')]
      | _ => raise TERM ("rename_rr_conv", [t])));

fun dest_type thy {tycon = (tycon, tv), ...} ty =
  let val env = Sign.typ_match thy (tycon, ty) Vartab.empty
    handle Type.TYPE_MATCH => raise TYPE ("dest_type", [ty, tycon], []);
  in the (Type.lookup env tv) end;

fun apply' thy sign ts =
  let val Ts = fst ts |> Term.fastype_of |> dest_type thy sign |> dest_funT;
  in apply sign Ts ts end;

(* XXX hack *)
fun dest_pure thy {pure = (pure, tv), ...} t =
  let
    val i = maxidx_of_term (pure $ t);
    val v = ((Name.uu, i + 1), TVar tv);
    val (_, env) = Pattern.match thy (pure $ Var v, t) (Vartab.empty, Vartab.empty)
      handle Pattern.MATCH => raise TERM ("dest_pure", [t, pure]);
  in the (Envir.lookup1 env v) end;

(* XXX hack *)
fun dest_ap thy {ap = (ap, tv1, tv2), ...} t =
  let
    val i = maxidx_of_term (ap $ t);
    val v1 = ((Name.uu, i + 1), TVar tv1 --> TVar tv2);
    val v2 = ((Name.uu, i + 2), TVar tv1);
    val (_, env) = Pattern.match thy (ap $ Var v1 $ Var v2, t) (Vartab.empty, Vartab.empty)
      handle Pattern.MATCH => raise TERM ("dest_ap", [t, ap]);
  in (the (Envir.lookup1 env v1), the (Envir.lookup1 env v2)) end;

fun normalform_conv ctxt {sign, nf_rules, ...} =
  let
    val thy = Proof_Context.theory_of ctxt;

    val leaf_conv = rename_rewr_conv (fn t => [("x", term_to_vname t)]) (#leaf nf_rules);
    val merge_conv = Conv.rewr_conv (#merge nf_rules);
    val swap_conv = Conv.rewr_conv (#swap nf_rules);
    val rotate_conv = rename_rr_conv "x" (#rotate nf_rules);
    val pure_rotate_conv = rename_rr_conv "x" (#pure_rotate nf_rules);
    fun normalize_pure_nf ct =
      ((pure_rotate_conv then_conv Conv.arg1_conv normalize_pure_nf) else_conv merge_conv) ct;
    val normalize_nf_pure = swap_conv then_conv normalize_pure_nf;
    fun normalize_nf_nf ct =
      ((rotate_conv then_conv
        Conv.arg1_conv (Conv.arg1_conv normalize_pure_nf then_conv normalize_nf_nf)) else_conv
      normalize_nf_pure) ct;

    fun normalize ct =
      let val t = Thm.term_of ct
      in if can (dest_ap thy sign) t
        then (Conv.arg1_conv normalize then_conv Conv.arg_conv normalize then_conv
            normalize_nf_nf) ct
        else if can (dest_pure thy sign) t
          then Conv.all_conv ct
          else leaf_conv ct
      end;
  in normalize end;

(* TODO support meta eq *)
fun normalize_eq_conv ctxt af ct =
  let
    val context = Context.Proof ctxt;
    val (lhs, rhs) = Thm.term_of ct |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
      handle TERM _ => raise CTERM ("no conversion", [ct]);
    (* XXX nice combinators? *)
    val af' = case af of
        SOME a => a
      | NONE => case try (get context) lhs of
            SOME a => a
          | NONE => get context rhs handle TERM _ => raise CTERM ("no conversion", [ct]);
    val nf_conv = normalform_conv ctxt af';
  in HOLogic.Trueprop_conv (Conv.arg1_conv nf_conv then_conv Conv.arg_conv nf_conv) ct end;

(* ignores local premises *)
fun normalize_eq_tac ctxt = CONVERSION (Conv.params_conv ~1 (fn ctxt =>
    Conv.concl_conv ~1 (normalize_eq_conv ctxt NONE)) ctxt);

fun lifting_nf_tac ctxt = normalize_eq_tac ctxt THEN'
  TRY o (REPEAT_ALL_NEW (rtac refl ORELSE' cong_tac ctxt) THEN'
    REPEAT o rtac ext);


datatype tterm = Atom of term | Var of int * int * term | App of tterm * tterm;

fun fold_atterms f (App (s, t)) = fold_atterms f s #> fold_atterms f t
  | fold_atterms f a = f a;

val cons_tterm_vars = fold_atterms (fn Var (i, j, _) => cons (i, j) | _ => I);

fun occurs_any v (App (s, t)) = occurs_any v s orelse occurs_any v t
  | occurs_any v (Var (i, _, _)) = exists (fn x => i = x) v
  | occurs_any _ _ = false;

fun term_of_tterm comb tt =
  let
    fun tm_of (Atom t) = t
      | tm_of (Var (_, _, t)) = t
      | tm_of (App (tt1, tt2)) = comb (tm_of tt1) (tm_of tt2);
  in tm_of tt end;

fun analyze_expressions ctxt af (t1, t2) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val sign = #sign (af: afun);
    fun generalize t (i, j, table) = case Termtab.lookup table t of
        SOME k => (Var (i, k, t), (i + 1, j, table))
      | NONE => (Var (i, j, t), (i + 1, j + 1, Termtab.insert (op =) (t, j) table));
    fun analyze t state = case try (dest_ap thy sign) t of
        SOME (t1, t2) => state |> analyze t1 ||>> analyze t2 |>> App
      | NONE => if can (dest_pure thy sign) t
            then (Atom t, state)
            else generalize t state;
  in (0, 0, Termtab.empty) |> analyze t1 ||>> analyze t2 |> fst end;

fun consolidate ctxt af (tt1, tt2) =
  let
    val combs = #combinators (af: afun);
    fun merge_adjacent ([], _) [] = []
      | merge_adjacent (vs, d) [] = [(vs, d)]
      | merge_adjacent ([], _) ((v, d)::xs) = merge_adjacent ([v], d) xs
      | merge_adjacent (vs, d) ((v', d')::xs) = if d = d'
          then merge_adjacent (v'::vs, d) xs
          else (vs, d) :: merge_adjacent ([v'], d') xs;
    fun align _ [] = []
      | align (v, d) ((v', d')::xs) = if d = d' then [v @ v'] else v' :: align (v, d) xs;
    fun merge ([], ys) = map fst ys
      | merge (xs, []) = map fst xs
      | merge (((v1, d1)::xs), ((v2, d2)::ys)) = if d1 = d2
          then (v1 @ v2) :: merge (xs, ys)
          else case (align (v2, d2) xs, align (v1, d1) ys) of
              (vs as (_::_), []) => vs @ merge (xs, ys)
            | ([], vs as (_::_)) => vs @ merge (xs, ys)
            | _ => v1 :: v2 :: merge (xs, ys);
    fun same ([], []) = []
      | same ([], _) = error "consolidate"  (* TODO *)
      | same (_, []) = error "consolidate"
      | same (((v1, d1)::xs), ((v2, d2)::ys)) = if d1 = d2
          then (v1 @ v2) :: same (xs, ys)
          else error "consolidate";
    val vars = (cons_tterm_vars tt1 [], cons_tterm_vars tt2 [])
        |> has_C combs ? apply2 (sort (fn ((_, a), (_, b)) => int_ord (a, b)))
        |> apply2 (if has_W combs then merge_adjacent ([], 0) else map (apfst single))
        |> (if has_K combs then merge else same);
  in vars end;

fun rewr_subst_ap ctxt sign rewr thm1 thm2 =
  let
    val thy = Proof_Context.theory_of ctxt;
    val Ts = thm1 |> Thm.lhs_of |> Thm.typ_of_cterm |> dest_type thy sign |> dest_funT;
    val ap_inst = Thm.cterm_of ctxt (ap sign Ts);
    val rule1 = Drule.binop_cong_rule ap_inst thm1 thm2;
    val rule2 = Conv.rewr_conv rewr (Thm.rhs_of rule1);
  in Thm.transitive rule1 rule2 end;

fun squash_atoms ctxt {sign, nf_rules, ...} tt =
  let
    fun squash (Atom t) = SOME (Thm.reflexive (Thm.cterm_of ctxt t))
      | squash (Var _) = NONE
      | squash (App (tt1, tt2)) = case squash tt1 of
          NONE => NONE
        | SOME thm1 => case squash tt2 of
            NONE => NONE
          | SOME thm2 => SOME (rewr_subst_ap ctxt sign (#merge nf_rules) thm1 thm2);
  in squash tt end;

fun eliminate ctxt af tt (v, v_tm) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val combs = #combinators (af: afun);
    val nf_rules = #nf_rules af;
    fun mk_ap t1 t2 = apply' thy (#sign af) (t1, t2);
    val rewr_subst_ap = rewr_subst_ap ctxt (#sign af);
    fun extract_comb n thm = Atom (thm |> Thm.rhs_of |> funpow n Thm.dest_arg1 |> Thm.term_of);
    fun refl_step tt = (tt, Thm.reflexive (Thm.cterm_of ctxt (term_of_tterm mk_ap tt)));
    fun comb2_step def (tt1, thm1) (tt2, thm2) =
      let val thm = rewr_subst_ap def thm1 thm2;
      in (App (App (extract_comb 3 thm, tt1), tt2), thm) end;
    val B_step = comb2_step (#B combs);
    fun swap_B_step (tt1, thm1) thm2 =
      let
        val thm3 = rewr_subst_ap (#swap nf_rules) thm1 thm2;
        val thm4 = Thm.transitive thm3 (Conv.rewr_conv (#B combs) (Thm.rhs_of thm3));
      in (App (App (extract_comb 3 thm4, extract_comb 1 thm3), tt1), thm4) end;
    fun I_step tm =
      let val thm = Conv.rewr_conv (#I combs) (Thm.cterm_of ctxt tm)
      in (extract_comb 1 thm, thm) end;
    fun K_step tt tm =
      let
        val ct = Thm.cterm_of ctxt tm;
        val thm = Drule.instantiate' [SOME (Thm.ctyp_of_cterm ct)] [SOME ct]
          (Conv.rewr_conv (#K combs |> the) (term_of_tterm mk_ap tt |> Thm.cterm_of ctxt))
      in (App (extract_comb 2 thm, tt), thm) end;
    fun elim (Atom _) = error "assertion"
      | elim (Var (i, _, t)) = if exists (fn x => x = i) v then I_step t else error "assertion"
      | elim (App (t1, t2)) = (case (occurs_any v t1, occurs_any v t2) of
            (false, false) => error "assertion"
          | (false, true) => B_step (refl_step t1) (elim t2)
          | (true, false) => (case squash_atoms ctxt af t2 of
                SOME thm => swap_B_step (elim t1) thm
              | NONE => comb2_step (#C combs |> the) (elim t1) (refl_step t2))
          | (true, true) => error "unimplemented");
  in if occurs_any v tt
    then elim tt
    else K_step tt v_tm
  end;

fun generalized_nf ctxt af ts =
  let
    val tts = analyze_expressions ctxt af ts;
    val vs = consolidate ctxt af tts;
    fun elim_all tt [] = squash_atoms ctxt af tt |> the
      | elim_all tt (v::vs) =
          let
            val (tt', rule1) = eliminate ctxt af tt (v, Term.dummy); (* FIXME *)
            val rule2 = elim_all tt' vs;
            val ((ct1, _), ct3) = rule1 |> Thm.rhs_of |> Thm.dest_comb |>> Thm.dest_comb;
            val rule3 = Thm.combination (Thm.combination (Thm.reflexive ct1) rule2) (Thm.reflexive ct3);
          in Thm.transitive rule1 rule3 end;
  in (elim_all (fst tts) vs, elim_all (snd tts) vs) end;

end;
