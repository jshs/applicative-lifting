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
  val add_generic: afun -> Context.generic -> Context.generic
  val add_global: afun -> theory -> theory
  val get: Context.generic -> term -> afun

  val normalform_conv: Proof.context -> afun -> conv
  val normalize_eq_conv: Proof.context -> afun option -> conv
  val normalize_eq_tac: Proof.context -> int -> tactic
  val lifting_nf_tac: Proof.context -> int -> tactic
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

type afun =
 {sign: sign,
  laws: laws,
  nf_rules: nf_rules};

val sign_of = #sign;
val laws_of = #laws;

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
  in {sign = sign, laws = laws, nf_rules = rules} end;

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

end;
