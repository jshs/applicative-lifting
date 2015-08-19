signature APPLICATIVE =
sig
  type tvar = indexname * sort;
  type var = indexname * typ;
  type sign =
   {pure: term * tvar,
    ap: term * tvar * tvar,
    tycon: typ * tvar,
    sort: sort}
  type axioms =
   {identity: thm,
    composition: thm,
    homomorphism: thm,
    interchange: thm,
    flip: thm option,
    const: thm option,
    duplicate: thm option}
  type afun;
  val mk_sign: Proof.context -> term * term -> sign;
  val mk_afun: Proof.context -> sign * axioms -> afun
  val add_generic: afun -> Context.generic -> Context.generic
  val add_global: afun -> theory -> theory
  val get: Context.generic -> term -> afun

  val liftT: afun -> typ -> typ
  val pure: afun -> typ -> term
  val lift: afun -> term -> term
  val ap: afun -> typ * typ -> term
  val apply: theory -> afun -> term * term -> term
  val dest_type: theory -> afun -> typ -> typ
  val dest_pure: theory -> afun -> term -> term
  val dest_ap: theory -> afun -> term -> term * term

  val normalform_conv: Proof.context -> afun -> conv
  val normalize_eq_tac: Proof.context -> afun option -> int -> tactic
  val lifting_nf_tac: Proof.context -> afun option -> int -> tactic
  val general_normalform_conv: Proof.context -> afun -> cterm * cterm -> thm * thm
  val general_normalize_eq_tac: Proof.context -> afun option -> int -> tactic
  val general_lifting_tac: Proof.context -> afun option -> int -> tactic
end;

structure Applicative : APPLICATIVE =
struct

type tvar = indexname * sort;
type var = indexname * typ;

type sign =
 {pure: term * tvar,
  ap: term * tvar * tvar,
  tycon: typ * tvar,
  sort: sort};

type axioms =
 {identity: thm,
  composition: thm,
  homomorphism: thm,
  interchange: thm,
  flip: thm option,
  const: thm option,
  duplicate: thm option};

type rules =
 {I: thm,
  B: thm,
  C: thm option,
  K: thm option,
  W: thm option,
  merge: thm,
  swap: thm,
  B_pure: thm};

datatype afun = AFun of
 {sign: sign,
  axioms: axioms,
  rules: rules};

fun rep_afun (AFun af) = af;
val sign_of_afun = #sign o rep_afun;
val axioms_of_afun = #axioms o rep_afun;
val rules_of_afun = #rules o rep_afun;
fun terms_of_afun af =
  let val {pure = (pure, _), ap = (ap, _, _), ...} = sign_of_afun af
  in (pure, ap) end;

val afun_ord = prod_ord Term_Ord.fast_term_ord Term_Ord.fast_term_ord o apply2 terms_of_afun;

fun has_rule f = is_some o f o rules_of_afun;


(* Term construction and destruction *)

fun liftT_sign {tycon = (tycon, v), ...} T = Term_Subst.instantiateT [(v, T)] tycon;
fun pure_sign {pure = (pure, v), ...} T = Term_Subst.instantiate ([(v, T)], []) pure;
fun lift_sign sign t = pure_sign sign (Term.fastype_of t) $ t;
fun ap_sign {ap = (ap, v1, v2), ...} (T1, T2) =
  Term_Subst.instantiate ([(v1, T1), (v2, T2)], []) ap;

val liftT = liftT_sign o sign_of_afun;
val pure = pure_sign o sign_of_afun;
val lift = lift_sign o sign_of_afun;
val ap = ap_sign o sign_of_afun;

fun dest_type thy af T =
  let
    val {tycon = (tycon, v), ...} = sign_of_afun af;
    val env = Sign.typ_match thy (tycon, T) Vartab.empty
      handle Type.TYPE_MATCH => raise TYPE ("dest_type", [T, tycon], []);
  in the (Type.lookup env v) end;

fun dest_pure thy af t =
  let
    val {pure = (pure, vT), ...} = sign_of_afun af;
    val i = maxidx_of_term (pure $ t);
    val v = ((Name.uu, i + 1), TVar vT);
    val (_, env) = Pattern.match thy (pure $ Var v, t) (Vartab.empty, Vartab.empty)
      handle Pattern.MATCH => raise TERM ("dest_pure", [t, pure]);
  in the (Envir.lookup1 env v) end;

fun dest_ap thy af t =
  let
    val {ap = (ap, vT1, vT2), ...} = sign_of_afun af;
    val i = maxidx_of_term (ap $ t);
    val v1 = ((Name.uu, i + 1), TVar vT1 --> TVar vT2);
    val v2 = ((Name.uu, i + 2), TVar vT1);
    val (_, env) = Pattern.match thy (ap $ Var v1 $ Var v2, t) (Vartab.empty, Vartab.empty)
      handle Pattern.MATCH => raise TERM ("dest_ap", [t, ap]);
  in (the (Envir.lookup1 env v1), the (Envir.lookup1 env v2)) end;

fun apply thy af (t1, t2) =
  let val funT = dest_type thy af (Term.fastype_of t1)
  in ap af (dest_funT funT) $ t1 $ t2 end;


(* Registration *)

structure Data = Generic_Data
(
  type T = afun Ord_List.T;
  val empty = [];
  val extend = I;
  val merge = Ord_List.merge afun_ord;
);

fun mk_sign ctxt (raw_pure, raw_ap) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val show_term = quote o Syntax.string_of_term ctxt;

    fun closed_poly_term t =
      let val poly_t = singleton (Variable.polymorphic ctxt) t;
      in case Term.add_vars (singleton
          (Variable.export_terms (Variable.auto_fixes t ctxt) ctxt) t) [] of
          [] => (case (Term.hidden_polymorphism poly_t) of
              [] => poly_t
            | _ => error ("Hidden type variables in term " ^ show_term t))
        | _ => error ("Locally free variables in term " ^ show_term t)
      end;

    val pure = closed_poly_term raw_pure;
    val (pure_argT, afT) = Term.dest_funT (Term.fastype_of pure)
      handle TYPE _ => error "Bad type for pure";
    val af_var as (_, sort) = Term.dest_TVar pure_argT
      handle TYPE _ => error "Bad type for pure";
    val _ = null (subtract (op =) (Term.add_tvars pure []) [af_var]) orelse
      error ("Locally free type variables in term " ^ show_term raw_pure);

    val ap = closed_poly_term raw_ap;
    val (ap_argT1, (ap_argT2, ap_resT)) = Term.fastype_of ap
        |> Term.dest_funT
        ||> Term.dest_funT
      handle TYPE _ => error "Bad type for application";
    val idx = Variable.maxidx_of ctxt + 1;
    val matcher1 = Sign.typ_match thy (afT, ap_argT2) Vartab.empty
      handle Type.TYPE_MATCH => error "Incompatible types";
    val ap_var1 = case Type.lookup matcher1 af_var of
        SOME v => (Term.dest_TVar v handle TYPE _ => error "Incompatible types")
      | NONE => (("'a", idx), sort);
    val matcher2 = Sign.typ_match thy (afT, ap_resT) Vartab.empty
      handle Type.TYPE_MATCH => error "Incompatible types";
    val ap_var2 = case Type.lookup matcher2 af_var of
        SOME v => (Term.dest_TVar v handle TYPE _ => error "Incompatible types")
      | NONE => (("'b", idx), sort);
    val _ =
      (ap_argT1 = Term_Subst.instantiateT [(af_var, TVar ap_var1 --> TVar ap_var2)] afT) orelse
      error "Incompatible types";
    val sort' = foldl1 (Sign.inter_sort thy) [sort, snd ap_var1, snd ap_var2];
  in
   {sort = sort', pure = (pure, af_var), ap = (ap, ap_var1, ap_var2), tycon = (afT, af_var)}
  end;

fun mk_afun ctxt (sign, axioms) =
  let
    fun comb_intro thm = Thm.symmetric (thm RS eq_reflection);

    val I_intro = comb_intro (#identity axioms);
    val B_intro = comb_intro (#composition axioms);

    val merge_rule = #homomorphism axioms RS eq_reflection;
    val swap_rule = #interchange axioms RS eq_reflection;

    val ([t1, t2, t3, gvar, fvar, xvar], ctxt') = Variable.variant_fixes
      ["'a", "'b", "'c", "g", "f", "x"] ctxt;
    val T1 = TFree (t1, #sort sign);
    val T2 = TFree (t2, #sort sign);
    val T3 = TFree (t3, #sort sign);
    val g = Free (gvar, T2 --> T3);
    val f = Free (fvar, liftT_sign sign (T1 --> T2));
    val x = Free (xvar, liftT_sign sign T1);
    val lhs = ap_sign sign (T2, T3) $ lift_sign sign g $ (ap_sign sign (T1, T2) $ f $ x);
    val comp_g = Abs ("f", T1 --> T2, Abs ("x", T1, g $ (Bound 1 $ Bound 0)));
    val rhs = ap_sign sign (T1, T3) $ (ap_sign sign (T1 --> T2, T1 --> T3) $
      lift_sign sign comp_g $ f) $ x;
    val prop = Logic.mk_equals (lhs, rhs);
    val tac = HEADGOAL (Raw_Simplifier.rewrite_goal_tac ctxt' [B_intro, merge_rule] THEN'
      rtac reflexive_thm);
    val rule = Goal.prove ctxt' [] [] prop (K tac);
    val B_pure_rule = singleton (Variable.export ctxt' ctxt) rule;

    val rules =
     {I = I_intro, B = B_intro,
      C = Option.map comb_intro (#flip axioms),
      K = Option.map comb_intro (#const axioms),
      W = Option.map comb_intro (#duplicate axioms),
      merge = merge_rule, swap = swap_rule, B_pure = B_pure_rule};
  in AFun {sign = sign, axioms = axioms, rules = rules} end;

val add_generic = Data.map o Ord_List.insert afun_ord;
fun add_global af = Context.theory_map (add_generic af);

fun get context t =
  let
    fun comb_vars t (0, _) = t
      | comb_vars t (n, i) =
        let val v = Var ((Name.uu, i + 1), dummyT)
        in comb_vars (t $ v) (n - 1, i + 1) end;
    fun op_pattern t n = comb_vars t (n, maxidx_of_term t);

    val thy = Context.theory_of context;
    fun matches af =
      let val (pure, ap) = terms_of_afun af
      in Pattern.matches thy (op_pattern ap 2, t) orelse
        Pattern.matches thy (op_pattern pure 1, t) end;
  in case find_first matches (Data.get context) of
      SOME af => af
    | NONE => raise TERM ("Applicative.get", [t]) end;


(* Reasoning with applicative functors *)

(** Utilities **)

val clean_name = perhaps (perhaps_apply [try Name.dest_skolem, try Name.dest_internal]);

(* based on term_name from Pure/term.ML *)
fun term_to_vname (Const (x, _)) = Long_Name.base_name x
  | term_to_vname (Free (x, _)) = clean_name x
  | term_to_vname (Var ((x, _), _)) = clean_name x
  | term_to_vname _ = Name.uu;

fun binop_par_conv cvs ct =
  let
    val ((binop, arg1), arg2) = Thm.dest_comb ct |>> Thm.dest_comb;
    val (th1, th2) = cvs (arg1, arg2);
  in Drule.binop_cong_rule binop th1 th2 end;

(* TODO handle HOL equalities only, due to head_cong_tac -- user can invoke atomize if needed *)
fun any_eq_conv cv ct = case Thm.term_of ct of
    Const (@{const_name Pure.eq}, _) $ _ $ _ => cv ct
  | Const (@{const_name HOL.Trueprop}, _) $ (Const (@{const_name HOL.eq}, _) $ _ $ _) =>
      HOLogic.Trueprop_conv cv ct
  | _ => raise CTERM ("any_eq_conv", [ct]);

val eq_par_conv = any_eq_conv o binop_par_conv;

fun auto_afun_conv cvs ctxt af (ct1, ct2) =
  let val af' = case af of
      SOME x => x
    | NONE => (case try (get (Context.Proof ctxt)) (Thm.term_of ct1) of
          SOME x => x
        | NONE => (case try (get (Context.Proof ctxt)) (Thm.term_of ct2) of
              SOME x => x
            | NONE => raise CTERM ("auto_afun_conv", [ct1, ct2])));
  in cvs ctxt af' (ct1, ct2) end;

(* ignores local premises *)
fun auto_afun_eq_tac cvs ctxt af = Subgoal.FOCUS (fn {context, ...} =>
  CONVERSION (eq_par_conv (auto_afun_conv cvs context af)) 1) ctxt;

fun head_cong_tac ctxt = TRY o (REPEAT_ALL_NEW (rtac refl ORELSE' cong_tac ctxt) THEN'
  REPEAT o rtac ext);


(** Normal form conversion **)

fun rename_rewr_conv mk_map rule ct =
  let val rule' = Drule.rename_bvars (mk_map (Thm.term_of ct)) rule
  in Conv.rewr_conv rule' ct end;

fun rename_rr_conv v = rename_rewr_conv (fn t =>
    (case t of
        _ $ (_ $ t') => [(v, term_to_vname t')]
      | _ => raise TERM ("rename_rr_conv", [t])));

fun normalform_conv ctxt af =
  let
    val thy = Proof_Context.theory_of ctxt;
    val rules = rules_of_afun af;

    val leaf_conv = rename_rewr_conv (fn t => [("x", term_to_vname t)]) (#I rules);
    val merge_conv = Conv.rewr_conv (#merge rules);
    val swap_conv = Conv.rewr_conv (#swap rules);
    val rotate_conv = rename_rr_conv "x" (#B rules);
    val pure_rotate_conv = rename_rr_conv "x" (#B_pure rules);
    fun normalize_pure_nf ct =
      ((pure_rotate_conv then_conv Conv.arg1_conv normalize_pure_nf) else_conv merge_conv) ct;
    val normalize_nf_pure = swap_conv then_conv normalize_pure_nf;
    fun normalize_nf_nf ct =
      ((rotate_conv then_conv
        Conv.arg1_conv (Conv.arg1_conv normalize_pure_nf then_conv normalize_nf_nf)) else_conv
      normalize_nf_pure) ct;

    fun normalize ct =
      let val t = Thm.term_of ct
      in if can (dest_ap thy af) t
        then (Conv.arg1_conv normalize then_conv Conv.arg_conv normalize then_conv
            normalize_nf_nf) ct
        else if can (dest_pure thy af) t
          then Conv.all_conv ct
          else leaf_conv ct
      end;
  in normalize end;

val normalize_eq_tac =
  let fun conv ctxt af (ct1, ct2) = (normalform_conv ctxt af ct1, normalform_conv ctxt af ct2)
  in auto_afun_eq_tac conv end;

fun lifting_nf_tac ctxt af = normalize_eq_tac ctxt af THEN' head_cong_tac ctxt;


(** Generalized unlifting **)

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

fun analyze_terms ctxt af (t1, t2) =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun generalize t (i, j, table, insts) = case Termtab.lookup table t of
        SOME k => (Var (i, k, t), (i + 1, j, table, insts))
      | NONE => (Var (i, j, t), (i + 1, j + 1, Termtab.insert (op =) (t, j) table, t :: insts));
    fun analyze t state = case try (dest_ap thy af) t of
        SOME (t1, t2) => state |> analyze t1 ||>> analyze t2 |>> App
      | NONE => if can (dest_pure thy af) t
            then (Atom t, state)
            else generalize t state;
    val get_insts = rev o #4;
  in (0, 0, Termtab.empty, []) |> analyze t1 ||>> analyze t2 ||> get_insts end;

fun consolidate ctxt af ((tt1, tt2), insts) =
  let
    fun merge_adjacent ([], _) [] = []
      | merge_adjacent (vs, d) [] = [(vs, d)]
      | merge_adjacent ([], _) ((v, d)::xs) = merge_adjacent ([v], d) xs
      | merge_adjacent (vs, d) ((v', d')::xs) = if d = d'
          then merge_adjacent (v'::vs, d) xs
          else (vs, d) :: merge_adjacent ([v'], d') xs;
    fun align _ [] = NONE
      | align (v, d) ((v', d')::xs) = if d = d'
          then SOME [(v @ v', d)]
          else Option.map (cons (v', d')) (align (v, d) xs);
    (* TODO select by least insertions *)
    fun merge ([], ys) = ys
      | merge (xs, []) = xs
      | merge (((v1, d1)::xs), ((v2, d2)::ys)) = if d1 = d2
          then (v1 @ v2, d1) :: merge (xs, ys)
          else case (align (v2, d2) xs, align (v1, d1) ys) of
              (SOME vs, NONE) => vs @ merge (xs, ys)
            | (NONE, SOME vs) => vs @ merge (xs, ys)
            | _ => (v1, d1) :: (v2, d2) :: merge (xs, ys);
    fun unbalanced vs = error ("Unbalanced opaque term(s) " ^
      commas_quote (map (Syntax.string_of_term ctxt o nth insts o snd) vs));
    fun mismatch (d1, d2) = error ("Mismatched opaque terms " ^
      quote (Syntax.string_of_term ctxt (nth insts d1)) ^ " and " ^
      quote (Syntax.string_of_term ctxt (nth insts d2)));
    fun same ([], []) = []
      | same ([], vs) = unbalanced vs
      | same (vs, []) = unbalanced vs
      | same (((v1, d1)::xs), ((v2, d2)::ys)) = if d1 = d2
          then (v1 @ v2, d1) :: same (xs, ys)
          else mismatch (d1, d2);
    val vars = (cons_tterm_vars tt1 [], cons_tterm_vars tt2 [])
        |> has_rule #C af ? apply2 (sort (fn ((_, a), (_, b)) => int_ord (a, b)))
        |> apply2 (if has_rule #W af then merge_adjacent ([], 0) else map (apfst single))
        |> (if has_rule #K af then merge else same);
  in vars end;

fun rewr_subst_ap ctxt af rewr thm1 thm2 =
  let
    val thy = Proof_Context.theory_of ctxt;
    val Ts = thm1 |> Thm.lhs_of |> Thm.typ_of_cterm |> dest_type thy af |> dest_funT;
    val ap_inst = Thm.cterm_of ctxt (ap af Ts);
    val rule1 = Drule.binop_cong_rule ap_inst thm1 thm2;
    val rule2 = Conv.rewr_conv rewr (Thm.rhs_of rule1);
  in Thm.transitive rule1 rule2 end;

fun squash_atoms ctxt af tt =
  let
    val {merge, ...} = rules_of_afun af;
    fun squash (Atom t) = SOME (Thm.reflexive (Thm.cterm_of ctxt t))
      | squash (Var _) = NONE
      | squash (App (tt1, tt2)) = case squash tt1 of
          NONE => NONE
        | SOME thm1 => case squash tt2 of
            NONE => NONE
          | SOME thm2 => SOME (rewr_subst_ap ctxt af merge thm1 thm2);
  in squash tt end;

exception ASSERT of string;

fun eliminate ctxt af tt (v, v_tm) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val rules = rules_of_afun af;

    fun mk_ap t1 t2 = apply thy af (t1, t2);
    val rewr_subst_ap = rewr_subst_ap ctxt af;
    fun extract_comb n thm = Atom (thm |> Thm.rhs_of |> funpow n Thm.dest_arg1 |> Thm.term_of);
    fun refl_step tt = (tt, Thm.reflexive (Thm.cterm_of ctxt (term_of_tterm mk_ap tt)));
    fun comb2_step def (tt1, thm1) (tt2, thm2) =
      let val thm = rewr_subst_ap def thm1 thm2;
      in (App (App (extract_comb 3 thm, tt1), tt2), thm) end;
    val B_step = comb2_step (#B rules);
    fun swap_B_step (tt1, thm1) thm2 =
      let
        val thm3 = rewr_subst_ap (#swap rules) thm1 thm2;
        val thm4 = Thm.transitive thm3 (Conv.rewr_conv (#B rules) (Thm.rhs_of thm3));
      in (App (App (extract_comb 3 thm4, extract_comb 1 thm3), tt1), thm4) end;
    fun I_step tm =
      let val thm = Conv.rewr_conv (#I rules) (Thm.cterm_of ctxt tm)
      in (extract_comb 1 thm, thm) end;
    fun W_step s1 s2 =
      let
        val (App (App (tt1, tt2), tt3), thm1) = B_step s1 s2;
        val thm2 = Conv.rewr_conv (#B rules) (Thm.rhs_of thm1 |> funpow 2 Thm.dest_arg1);
        val thm3 = squash_atoms ctxt af tt3 |> the;
        val (tt4, thm4) = swap_B_step (App (App (extract_comb 3 thm2, tt1), tt2), thm2) thm3;
        val var = Thm.rhs_of thm1 |> Thm.dest_arg;
        val thm5 = rewr_subst_ap (#W rules |> the) thm4 (Thm.reflexive var);
        val thm6 = Thm.transitive thm1 thm5;
      in (App (extract_comb 2 thm6, tt4), thm6) end;
    fun S_step s1 s2 =
      let
        val (App (App (tt1, tt2), tt3), thm1) = comb2_step (#C rules |> the) s1 s2;
        val thm2 = Conv.rewr_conv (#B rules) (Thm.rhs_of thm1 |> Thm.dest_arg1);
        val var = Thm.rhs_of thm1 |> Thm.dest_arg;
        val thm3 = rewr_subst_ap (#W rules |> the) thm2 (Thm.reflexive var);
        val thm4 = Thm.transitive thm1 thm3;
        val tt = App (extract_comb 2 thm4, App (App (extract_comb 3 thm2, App (tt1, tt2)), tt3));
      in (tt, thm4) end;
    fun K_step tt tm =
      let
        val ct = Thm.cterm_of ctxt tm;
        val T = Term.fastype_of tm |> dest_type thy af |> Thm.ctyp_of ctxt;
        val thm = Drule.instantiate' [SOME T] [SOME ct]
          (Conv.rewr_conv (#K rules |> the) (term_of_tterm mk_ap tt |> Thm.cterm_of ctxt))
      in (App (extract_comb 2 thm, tt), thm) end;
    fun unreachable _ = raise ASSERT "eliminate: assertion failed";
    fun elim (Atom _) = unreachable ()
      | elim (Var (i, _, t)) = if exists (fn x => x = i) v then I_step t else unreachable ()
      | elim (App (t1, t2)) = (case (occurs_any v t1, occurs_any v t2) of
            (false, false) => unreachable ()
          | (false, true) => B_step (refl_step t1) (elim t2)
          | (true, false) => (case squash_atoms ctxt af t2 of
                SOME thm => swap_B_step (elim t1) thm
              | NONE => comb2_step (#C rules |> the) (elim t1) (refl_step t2))
          | (true, true) => if has_rule #C af
              then S_step (elim t1) (elim t2)
              else W_step (elim t1) (elim t2));
  in if occurs_any v tt
    then elim tt
    else K_step tt v_tm
  end;

fun rename_boundvars vs insts thm =
  let
    fun rename [] t = t
      | rename (v::vs) (Abs (_, T, t)) = Abs (term_to_vname (nth insts v), T, rename vs t)
      | rename _ t = t;
    fun rename_pure t = Term.dest_comb t ||> rename (rev vs) |> (op $);
    val prop' = Thm.prop_of thm |> Logic.dest_equals ||> rename_pure |> Logic.mk_equals;
  in Thm.renamed_prop prop' thm end;

fun general_normalform_conv ctxt af cts =
  let
    val ts = apply2 Thm.term_of cts;
    val (tts, insts) = analyze_terms ctxt af ts;
    val vs = consolidate ctxt af (tts, insts);
    fun elim_all tt [] = squash_atoms ctxt af tt |> the |> rename_boundvars (map snd vs) insts
      | elim_all tt ((v, d)::vs) =
          let
            val (tt', rule1) = eliminate ctxt af tt (v, nth insts d);
            val rule2 = elim_all tt' vs;
            val ((ct1, _), ct3) = rule1 |> Thm.rhs_of |> Thm.dest_comb |>> Thm.dest_comb;
            val rule3 = Thm.combination (Thm.combination (Thm.reflexive ct1) rule2) (Thm.reflexive ct3);
          in Thm.transitive rule1 rule3 end;
  in (elim_all (fst tts) vs, elim_all (snd tts) vs) end;

val general_normalize_eq_tac = auto_afun_eq_tac general_normalform_conv;

fun general_lifting_tac ctxt af = general_normalize_eq_tac ctxt af THEN' head_cong_tac ctxt;

end;
