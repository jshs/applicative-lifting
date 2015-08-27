signature APPLICATIVE =
sig
  type afun
  val afun_of_generic: Context.generic -> string -> afun
  val afun_of: Proof.context -> string -> afun
  val afuns_of_term_generic: Context.generic -> term -> afun list
  val afuns_of_term: Proof.context -> term -> afun list
  val afuns_of_typ_generic: Context.generic -> typ -> afun list
  val afuns_of_typ: Proof.context -> typ -> afun list
  val applicative_cmd: binding -> string -> string -> string list -> local_theory -> Proof.state
  val add_unfold_attrib: string option -> attribute

  val name_of_afun: afun -> binding
  val terms_of_afun: afun -> term * term
  val unfolds_of_afun: afun -> thm list
  val lift_type: afun -> typ list -> typ -> typ
  val pure: afun -> typ list -> typ -> term
  val lift: afun -> typ list -> term -> term
  val ap: Proof.context -> afun -> typ -> term
  val lift_comb: Proof.context -> afun -> term * term -> term
  val dest_type: Proof.context -> afun -> typ -> typ * typ list
  val dest_pure: Proof.context -> afun -> term -> term
  val dest_comb: Proof.context -> afun -> term -> term * term

  val applicative_unfold_tac: Proof.context -> afun -> int -> tactic
  val normalform_conv: Proof.context -> afun -> conv
  val normalize_eq_tac: Proof.context -> afun -> int -> tactic
  val general_normalform_conv: Proof.context -> afun -> cterm * cterm -> thm * thm
  val general_normalize_eq_tac: Proof.context -> afun -> int -> tactic
  val unfold_wrapper_tac: Proof.context -> afun option -> int -> tactic
  val normalize_wrapper_tac: Proof.context -> afun option -> int -> tactic
  val lifting_wrapper_tac: Proof.context -> afun option -> int -> tactic
end;

structure Applicative : APPLICATIVE =
struct

(** General utilities **)

fun filter_flag [] = []
  | filter_flag ((flag, x)::xs) = if flag then x :: filter_flag xs else filter_flag xs;

fun pick (x::xs) = (x, xs)
  | pick _ = raise List.Empty;

fun pick_if false xs = (NONE, xs)
  | pick_if true (x::xs) = (SOME x, xs)
  | pick_if true _ = raise List.Empty;

fun mk_TFrees Ss ctxt = Variable.invent_types Ss ctxt |>> map TFree;
val mk_TFrees' = mk_TFrees oo replicate;
val mk_TFrees_of_vars = mk_TFrees o map (#2 o Term.dest_TVar);

fun mk_Free name typ ctxt = Variable.variant_fixes [name] ctxt
  |>> (fn name' => Free (name', typ)) o the_single;


(** Internal representation **)

type sign =
 {pure: term,
  ap: term,
  T: typ * typ,  (* variable, type pattern *)
  params: typ list,
  sort: sort};

fun map_sign f1 f2 f3 f4 f5 {pure, ap, T, params, sort} =
  {pure = f1 pure, ap = f2 ap, T = f3 T, params = f4 params, sort = f5 sort};

fun morph_sign phi = map_sign (Morphism.term phi) (Morphism.term phi) (apply2 (Morphism.typ phi))
  (map (Morphism.typ phi)) I;

type axioms =
 {identity: thm,
  composition: thm,
  homomorphism: thm,
  interchange: thm,
  flip: thm option,
  const: thm option,
  duplicate: thm option};

fun map_axioms f {identity, composition, homomorphism, interchange, flip, const, duplicate} =
  {identity = f identity, composition = f composition, homomorphism = f homomorphism,
    interchange = f interchange, flip = Option.map f flip, const = Option.map f const,
    duplicate = Option.map f duplicate};

val morph_axioms = map_axioms o Morphism.thm;

type facts =
 {I_intro: thm,
  B_intro: thm,
  C_intro: thm option,
  K_intro: thm option,
  W_intro: thm option,
  merge: thm,
  swap: thm,
  B_pure: thm};

fun map_facts f {I_intro, B_intro, C_intro, K_intro, W_intro, merge, swap, B_pure} =
  {I_intro = f I_intro, B_intro = f B_intro, C_intro = Option.map f C_intro,
    K_intro = Option.map f K_intro, W_intro = Option.map f W_intro, merge = f merge, swap = f swap,
    B_pure = f B_pure};

val morph_facts = map_facts o Morphism.thm;

datatype afun = AFun of
 {name: binding,
  sign: sign,
  axioms: axioms,
  facts: facts,
  unfolds: thm list};

fun rep_afun (AFun af) = af;
val name_of_afun = #name o rep_afun;
val sign_of_afun = #sign o rep_afun;
val axioms_of_afun = #axioms o rep_afun;
val unfolds_of_afun = #unfolds o rep_afun;
val facts_of_afun = #facts o rep_afun;
fun terms_of_afun af = let val {pure, ap, ...} = sign_of_afun af in (pure, ap) end;

fun has_fact f = is_some o f o facts_of_afun;

fun map_afun f1 f2 f3 f4 f5 (AFun {name, sign, axioms, facts, unfolds}) =
  AFun {name = f1 name, sign = f2 sign, axioms = f3 axioms, facts = f4 facts,
    unfolds = f5 unfolds};

fun morph_afun phi =
  map_afun (Morphism.binding phi) (morph_sign phi) (morph_axioms phi) (morph_facts phi)
    (map (Morphism.thm phi));

(* FIXME is this (i.e. Thm.transfer) really needed? *)
val transfer_afun = morph_afun o Morphism.transfer_morphism;

fun add_unfolds thms = map_afun I I I I (union Thm.eq_thm_prop thms);

fun join_afuns _ (af1, af2) = if pointer_eq (af1, af2)
  then raise Same.SAME
  else add_unfolds (unfolds_of_afun af2) af1;


(** Term construction and destruction **)

fun lift_type_sign {T = (var, tycon), params, ...} insts baseT =
  Term.typ_subst_atomic ((var, baseT) :: (params ~~ insts)) tycon;

fun pure_sign {pure, params, ...} insts baseT =
  let val (var, _) = Term.fastype_of pure |> Term.dest_funT;
  in Term.subst_atomic_types ((var, baseT) :: (params ~~ insts)) pure end;

fun lift_sign sign insts t = Term.betapply (pure_sign sign insts (Term.fastype_of t), t);

fun ap_sign ctxt {ap, ...} funT =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (pat, _) = Term.fastype_of ap |> Term.dest_funT;
    val tyenv = Sign.typ_match thy (pat, funT) Vartab.empty
      handle Type.TYPE_MATCH => raise TYPE ("ap_sign", [funT, pat], []);
  in Envir.subst_term_types tyenv ap end

fun comb_sign ctxt sign (t1, t2) =
  Term.betapplys (ap_sign ctxt sign (Term.fastype_of t1), [t1, t2]);

val lift_type = lift_type_sign o sign_of_afun;
val pure = pure_sign o sign_of_afun;
val lift = lift_sign o sign_of_afun;
fun ap ctxt = ap_sign ctxt o sign_of_afun;
fun lift_comb ctxt = comb_sign ctxt o sign_of_afun;

fun pure_pattern af =
  let
    val {pure, ...} = sign_of_afun af;
    val (argT, _) = Term.fastype_of pure |> Term.dest_funT;
    val var = ((Name.uu, Term.maxidx_of_term pure + 1), argT);
  in (Term.betapply (pure, Var var), var) end;

fun ap_pattern af =
  let
    val {ap, ...} = sign_of_afun af;
    val (arg1T, (arg2T, _)) = Term.fastype_of ap |> Term.dest_funT ||> Term.dest_funT;
    val i = Term.maxidx_of_term ap;
    val var1 = ((Name.uu, i + 1), arg1T);
    val var2 = ((Name.uu, i + 2), arg2T);
  in (Term.betapplys (ap, [Var var1, Var var2]), (var1, var2)) end;

fun patterns_of_afun af = [#1 (pure_pattern af), #1 (ap_pattern af),
  (Net.encode_type o #2 o #T o sign_of_afun) af];

fun dest_type ctxt af T =
  let
    val thy = Proof_Context.theory_of ctxt;
    val {T = (var, tycon), params, ...} = sign_of_afun af;
    val tyenv = Sign.typ_match thy (tycon, T) Vartab.empty
      handle Type.TYPE_MATCH => raise TYPE ("dest_type", [T, tycon], []);
  in (the (Type.lookup tyenv (Term.dest_TVar var)),
    map (the o Type.lookup tyenv o Term.dest_TVar) params) end;

fun dest_pure ctxt af t =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (pat, var) = pure_pattern af;
    val (_, env) = Pattern.match thy (pat, t) (Vartab.empty, Vartab.empty)
      handle Pattern.MATCH => raise TERM ("dest_pure", [t, pat]);
  in the (Envir.lookup1 env var) end;

fun dest_comb ctxt af t =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (pat, vars) = ap_pattern af;
    val (_, env) = Pattern.match thy (pat, t) (Vartab.empty, Vartab.empty)
      handle Pattern.MATCH => raise TERM ("dest_ap", [t, pat]);
  in apply2 (the o Envir.lookup1 env) vars end;


(** Registration **)

(* Context data *)

(* FIXME carefully verify context storage *)
(* FIXME needs tests, especially around theory merging *)

structure Data = Generic_Data
(
  type T = afun Symtab.table * (string * term list) Item_Net.T;
  val empty = (Symtab.empty, Item_Net.init (op = o apply2 #1) #2);
  val extend = I;
  val merge = fn ((a1, b1), (a2, b2)) => (Symtab.join join_afuns (a1, a2), Item_Net.merge (b1, b2));
);

fun undeclared name = error ("Undeclared applicative functor " ^ quote name);

fun afun_of_generic context name = case Symtab.lookup (#1 (Data.get context)) name of
    SOME af => transfer_afun (Context.theory_of context) af
  | NONE => undeclared name;

val afun_of = afun_of_generic o Context.Proof;

fun update_afun name f context = if Symtab.defined (#1 (Data.get context)) name
  then Data.map (apfst (Symtab.map_entry name f)) context
  else undeclared name;

fun afun_names_of context = map #1 o Item_Net.retrieve_matching (#2 (Data.get context));

fun afuns_of_term_generic context = map (afun_of_generic context) o afun_names_of context;
val afuns_of_term = afuns_of_term_generic o Context.Proof;

fun afuns_of_typ_generic context = afuns_of_term_generic context o Net.encode_type;
val afuns_of_typ = afuns_of_typ_generic o Context.Proof;

(* FIXME pervasive? *)
fun register_afun name af =
  let fun decl phi = Data.map (fn (afuns, net) =>
    if Symtab.defined afuns name
    then error ("Duplicate declaration of applicative functor " ^ quote name)
    else
      let val af' = morph_afun phi af;
      in (Symtab.update (name, af') afuns, Item_Net.update (name, patterns_of_afun af') net) end);
  in Local_Theory.declaration {syntax = false, pervasive = false} decl end;


(* Declaration *)

fun mk_sign ctxt (raw_pure, raw_ap) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val show_term = quote o Syntax.string_of_term ctxt;
    fun bad_types _ = error "Bad type(s)";

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
    val (var as (_, pure_sort), tycon) = Term.fastype_of pure |> Term.dest_funT |>> Term.dest_TVar
      handle TYPE _ => bad_types ();
    val params = subtract (op =) [var] (Term.add_tvars pure []);

    val ap = closed_poly_term raw_ap;
    val i = Term.maxidx_of_term pure;
    val ap_var1 = ((Name.uu, i + 1), []);
    val ap_var2 = ((Name.uu, i + 2), []);
    fun lift T = Term_Subst.instantiateT [(var, T)] tycon;
    val ap_pat = lift (TVar ap_var1 --> TVar ap_var2) --> lift (TVar ap_var1) -->
      lift (TVar ap_var2);
    val tyenv = Sign.typ_match thy (ap_pat, Term.fastype_of ap) Vartab.empty
      handle Type.TYPE_MATCH => bad_types ();
    val ((ap_var1', ap_sort1), (ap_var2', ap_sort2)) =
      apply2 (Term.dest_TVar o the o Type.lookup tyenv) (ap_var1, ap_var2)
      handle
          Option.Option => bad_types ()
        | TYPE _ => bad_types ();
    val _ = ap_var1' <> ap_var2' orelse bad_types ();
    (* FIXME check additional type params *)

    val sort = foldl1 (Sign.inter_sort thy) [pure_sort, ap_sort1, ap_sort2];
    val _ = Sign.of_sort thy (Term.aT sort --> Term.aT sort, sort) orelse
      error ("Sort constraint " ^ quote (Syntax.string_of_sort ctxt sort) ^
        " not closed under function types");
  in
   {pure = pure, ap = ap, T = (TVar var, tycon), params = map TVar params, sort = sort}
  end;

fun mk_afun ctxt (name, sign, axioms) =
  let
    fun comb_intro thm = Thm.symmetric (thm RS eq_reflection);
    val B_intro = comb_intro (#composition axioms);
    val merge_rule = #homomorphism axioms RS eq_reflection;

    val (([T1, T2, T3], Ts), ctxt') = ctxt
      |> mk_TFrees' 3 (#sort sign)
      ||>> mk_TFrees_of_vars (#params sign);
    val (((g, f), x), ctxt'') = ctxt'
      |> mk_Free "g" (T2 --> T3)
      ||>> mk_Free "f" (lift_type_sign sign Ts (T1 --> T2))
      ||>> mk_Free "x" (lift_type_sign sign Ts T1);
    val comb = comb_sign ctxt'' sign;
    val lhs = comb (lift_sign sign Ts g, comb (f, x));
    val B_g = Abs ("f", T1 --> T2, Abs ("x", T1, Term.betapply (g, Bound 1 $ Bound 0)));
    val rhs = comb (comb (lift_sign sign Ts B_g, f), x);
    val prop = Logic.mk_equals (lhs, rhs);
    val B_pure_tac = HEADGOAL (Raw_Simplifier.rewrite_goal_tac ctxt'' [B_intro, merge_rule] THEN'
      rtac reflexive_thm);
    val B_pure = singleton (Variable.export ctxt'' ctxt)
      (Goal.prove ctxt'' [] [] prop (K B_pure_tac));

    val facts =
     {I_intro = comb_intro (#identity axioms),
      B_intro = B_intro,
      C_intro = Option.map comb_intro (#flip axioms),
      K_intro = Option.map comb_intro (#const axioms),
      W_intro = Option.map comb_intro (#duplicate axioms),
      merge = merge_rule,
      swap = #interchange axioms RS eq_reflection,
      B_pure = B_pure};
  in AFun {name = name, sign = sign, axioms = axioms, facts = facts, unfolds = []} end;

fun mk_comb_prop comb sign ctxt =
  let
    val comb_tfrees = Term.add_tfrees comb [];
    val ((Ts, Us), ctxt') = ctxt
      |> mk_TFrees' (length comb_tfrees) (#sort sign)
      ||>> mk_TFrees_of_vars (#params sign);
    val comb' = Term.subst_atomic_types (map TFree comb_tfrees ~~ Ts) comb;
    val (bound_names, bound_Ts) = split_list (Term.strip_abs_vars comb');
    val (var_names, ctxt'') = Variable.variant_fixes bound_names ctxt';
    val vars = map (fn (var, T) => Free (var, lift_type_sign sign Us T)) (var_names ~~ bound_Ts);
    val lift_map = rev vars;

    fun list_comb t [] = t
      | list_comb t (x::xs) = list_comb (comb_sign ctxt'' sign (t, x)) xs;

    fun lift_term (Bound i) = nth lift_map i
      | lift_term (s $ t) = comb_sign ctxt'' sign (lift_term s, lift_term t)
      | lift_term t = raise TERM ("mk_comb_prop", [t]);

    val lhs = list_comb (lift_sign sign Us comb') vars;
    val rhs = lift_term (Term.strip_abs_body comb');
    val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in fold Logic.all lift_map prop end;

val mk_id_prop = mk_comb_prop @{term "\<lambda>x. x"};
val mk_comp_prop = mk_comb_prop @{term "\<lambda>g f x. g (f x)"};
val mk_flip_prop = mk_comb_prop @{term "\<lambda>f x y. f y x"};
val mk_const_prop = mk_comb_prop @{term "\<lambda>x y. x"};
val mk_duplicate_prop = mk_comb_prop @{term "\<lambda>f x. f x x"};

fun mk_homomorphism_prop sign ctxt =
  let
    val (([T1, T2], Us), ctxt') = ctxt
      |> mk_TFrees' 2 (#sort sign)
      ||>> mk_TFrees_of_vars (#params sign);
    val ((f, x), ctxt'') = ctxt'
      |> mk_Free "f" (T1 --> T2)
      ||>> mk_Free "x" T1;
    val lhs = comb_sign ctxt'' sign (lift_sign sign Us f, lift_sign sign Us x);
    val rhs = lift_sign sign Us (f $ x);
    val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in Logic.all f (Logic.all x prop) end;

fun mk_interchange_prop sign ctxt =
  let
    val (([T1, T2], Us), ctxt') = ctxt
      |> mk_TFrees' 2 (#sort sign)
      ||>> mk_TFrees_of_vars (#params sign);
    val ((f, x), ctxt'') = ctxt'
      |> mk_Free "f" (lift_type_sign sign Us (T1 --> T2))
      ||>> mk_Free "x" T1;
    val lhs = comb_sign ctxt'' sign (f, lift_sign sign Us x);
    val T_x = Abs ("f", T1 --> T2, Bound 0 $ x);
    val rhs = comb_sign ctxt'' sign (lift_sign sign Us T_x, f);
    val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in Logic.all f (Logic.all x prop) end;

fun applicative_cmd name pure ap flags lthy =
  let
    (* FIXME *)
    val (C, K, W) = fold (fn ident => fn (C, K, W) =>
      if ident = "C" then (true, K, W)
      else if ident = "K" then (C, true, W)
      else if ident = "W" then (C, K, true)
      else error ("Unknown combinator " ^ ident)) flags (false, false, false);
    val raw_pure = Syntax.read_term lthy pure;
    val raw_ap = Syntax.read_term lthy ap;

    val sign = mk_sign lthy (raw_pure, raw_ap);
    (* FIXME fix variables here, then reuse in each mk_*_prop (à la BNF_Def) *)
    val basic_props = [mk_id_prop, mk_comp_prop, mk_homomorphism_prop, mk_interchange_prop];
    val extra_props = filter_flag [(C, mk_flip_prop), (K, mk_const_prop), (W, mk_duplicate_prop)];
    val props = map (fn mk_prop => mk_prop sign lthy) (basic_props @ extra_props);

    fun after_qed thmss lthy =
      let
        val ((((id_thm, comp_thm), hom_thm), interchange_thm), extra_thms) = flat thmss
          |> pick
          ||>> pick
          ||>> pick
          ||>> pick;
        val (((flip_thm), const_thm), duplicate_thm) = extra_thms
          |> pick_if C
          ||>> pick_if K
          ||>> pick_if W
          |> #1;
        val axioms = {identity = id_thm, composition = comp_thm, homomorphism = hom_thm,
          interchange = interchange_thm, flip = flip_thm, const = const_thm,
          duplicate = duplicate_thm};
        val af = mk_afun lthy (name, sign, axioms);
      in register_afun (Local_Theory.full_name lthy name) af lthy end;
      (* TODO default name from type *)
  in Proof.theorem NONE after_qed (map (fn t => [(t, [])]) props) lthy
    |> Proof.refine (Method.primitive_text (Library.K I))
    |> Seq.hd end;


(* Unfolding *)

fun add_unfold_thm name thm context =
  let
    val (lhs, _) = Thm.prop_of thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
      handle TERM _ => error "Not an equation";
    val name' = case name of
        SOME n => n
      | NONE => case afun_names_of context (Net.encode_type (Term.fastype_of lhs)) of
          (n::_) => n
        | [] => error "Unable to determine applicative functor instance";
    val _ = afun_of_generic context name';
    (* TODO check equation *)
    (* FIXME could also use Local_Defs.meta_rewrite_rule or unfold_tac *)
    val thm' = thm RS @{thm eq_reflection};
  in update_afun name' (add_unfolds [thm']) context end;

fun add_unfold_attrib name = Thm.declaration_attribute (add_unfold_thm name);

(* TODO deletion? *)


(** Reasoning with applicative functors **)

(* Utilities *)

val clean_name = perhaps (perhaps_apply [try Name.dest_skolem, try Name.dest_internal]);

(* based on term_name from Pure/term.ML *)
fun term_to_vname (Const (x, _)) = Long_Name.base_name x
  | term_to_vname (Free (x, _)) = clean_name x
  | term_to_vname (Var ((x, _), _)) = clean_name x
  | term_to_vname _ = "x";

fun afun_of_eq ctxt t =
  let val (lhs, _) = t |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;
  in (case afuns_of_typ ctxt (Term.fastype_of lhs) of
      (af::_) => af
    | [] => raise TERM ("afun_of_eq", [t])) end;

fun AUTO_AFUN ctxt af tac i st = case af of
    SOME af' => tac af' i st
  | NONE => tac (afun_of_eq ctxt (Logic.nth_prem (i, Thm.prop_of st))) i st
      handle TERM _ => Seq.empty;

fun binop_par_conv cv ct =
  let
    val ((binop, arg1), arg2) = Thm.dest_comb ct |>> Thm.dest_comb;
    val (th1, th2) = cv (arg1, arg2);
  in Drule.binop_cong_rule binop th1 th2 end;

fun hol_eq_par_conv cv ct = case Thm.term_of ct of
    Const (@{const_name HOL.eq}, _) $ _ $ _ => binop_par_conv cv ct
  | _ => raise CTERM ("hol_eq_par_conv", [ct]);

fun hol_eq_conv_tac cv = CONVERSION (HOLogic.Trueprop_conv (hol_eq_par_conv cv));

fun head_cong_tac ctxt = TRY o (REPEAT_ALL_NEW (rtac refl ORELSE' cong_tac ctxt)) THEN'
  REPEAT o rtac ext;


(* Unfolding of lifted constants *)

fun applicative_unfold_tac ctxt af = Raw_Simplifier.rewrite_goal_tac ctxt (unfolds_of_afun af);


(* Normal form conversion *)

fun rename_rewr_conv mk_map rule ct =
  let val rule' = Drule.rename_bvars (mk_map (Thm.term_of ct)) rule
  in Conv.rewr_conv rule' ct end;

fun rename_rr_conv v = rename_rewr_conv (fn t =>
    (case t of
        _ $ (_ $ t') => [(v, term_to_vname t')]
      | _ => raise TERM ("rename_rr_conv", [t])));

fun normalform_conv ctxt af =
  let
    val rules = facts_of_afun af;

    val leaf_conv = rename_rewr_conv (fn t => [("x", term_to_vname t)]) (#I_intro rules);
    val merge_conv = Conv.rewr_conv (#merge rules);
    val swap_conv = Conv.rewr_conv (#swap rules);
    val rotate_conv = rename_rr_conv "x" (#B_intro rules);
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
      in if can (dest_comb ctxt af) t
        then (Conv.arg1_conv normalize then_conv Conv.arg_conv normalize then_conv
            normalize_nf_nf) ct
        else if can (dest_pure ctxt af) t
          then Conv.all_conv ct
          else leaf_conv ct
      end;
  in normalize end;

val normalize_eq_tac = hol_eq_conv_tac o apply2 oo normalform_conv;


(* Generalized unlifting *)

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
    fun generalize t (i, j, table, insts) = case Termtab.lookup table t of
        SOME k => (Var (i, k, t), (i + 1, j, table, insts))
      | NONE => (Var (i, j, t), (i + 1, j + 1, Termtab.insert (op =) (t, j) table, t :: insts));
    fun analyze t state = case try (dest_comb ctxt af) t of
        SOME (t1, t2) => state |> analyze t1 ||>> analyze t2 |>> App
      | NONE => if can (dest_pure ctxt af) t
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
      commas_quote (map (Syntax.string_of_term ctxt o nth insts o #2) vs));
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
        |> has_fact #C_intro af ? apply2 (sort (fn ((_, a), (_, b)) => int_ord (b, a)))
        |> apply2 (if has_fact #W_intro af then merge_adjacent ([], 0) else map (apfst single))
        |> (if has_fact #K_intro af then merge else same);
  in vars end;

fun rewr_subst_ap ctxt af rewr thm1 thm2 =
  let
    val funT = thm1 |> Thm.lhs_of |> Thm.typ_of_cterm;
    val ap_inst = Thm.cterm_of ctxt (ap ctxt af funT);
    val rule1 = Drule.binop_cong_rule ap_inst thm1 thm2;
    val rule2 = Conv.rewr_conv rewr (Thm.rhs_of rule1);
  in Thm.transitive rule1 rule2 end;

fun squash_atoms ctxt af tt =
  let
    val {merge, ...} = facts_of_afun af;
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
    val rules = facts_of_afun af;

    fun mk_ap t1 t2 = lift_comb ctxt af (t1, t2);
    val rewr_subst_ap = rewr_subst_ap ctxt af;
    fun extract_comb n thm = Atom (thm |> Thm.rhs_of |> funpow n Thm.dest_arg1 |> Thm.term_of);
    fun refl_step tt = (tt, Thm.reflexive (Thm.cterm_of ctxt (term_of_tterm mk_ap tt)));
    fun comb2_step def (tt1, thm1) (tt2, thm2) =
      let val thm = rewr_subst_ap def thm1 thm2;
      in (App (App (extract_comb 3 thm, tt1), tt2), thm) end;
    val B_step = comb2_step (#B_intro rules);
    fun swap_B_step (tt1, thm1) thm2 =
      let
        val thm3 = rewr_subst_ap (#swap rules) thm1 thm2;
        val thm4 = Thm.transitive thm3 (Conv.rewr_conv (#B_intro rules) (Thm.rhs_of thm3));
      in (App (App (extract_comb 3 thm4, extract_comb 1 thm3), tt1), thm4) end;
    fun I_step tm =
      let val thm = Conv.rewr_conv (#I_intro rules) (Thm.cterm_of ctxt tm)
      in (extract_comb 1 thm, thm) end;
    fun W_step s1 s2 =
      let
        val (App (App (tt1, tt2), tt3), thm1) = B_step s1 s2;
        val thm2 = Conv.rewr_conv (#B_intro rules) (Thm.rhs_of thm1 |> funpow 2 Thm.dest_arg1);
        val thm3 = squash_atoms ctxt af tt3 |> the;
        val (tt4, thm4) = swap_B_step (App (App (extract_comb 3 thm2, tt1), tt2), thm2) thm3;
        val var = Thm.rhs_of thm1 |> Thm.dest_arg;
        val thm5 = rewr_subst_ap (#W_intro rules |> the) thm4 (Thm.reflexive var);
        val thm6 = Thm.transitive thm1 thm5;
      in (App (extract_comb 2 thm6, tt4), thm6) end;
    fun S_step s1 s2 =
      let
        val (App (App (tt1, tt2), tt3), thm1) = comb2_step (#C_intro rules |> the) s1 s2;
        val thm2 = Conv.rewr_conv (#B_intro rules) (Thm.rhs_of thm1 |> Thm.dest_arg1);
        val var = Thm.rhs_of thm1 |> Thm.dest_arg;
        val thm3 = rewr_subst_ap (#W_intro rules |> the) thm2 (Thm.reflexive var);
        val thm4 = Thm.transitive thm1 thm3;
        val tt = App (extract_comb 2 thm4, App (App (extract_comb 3 thm2, App (tt1, tt2)), tt3));
      in (tt, thm4) end;
    fun K_step tt tm =
      let
        val ct = Thm.cterm_of ctxt tm;
        val T = Term.fastype_of tm |> dest_type ctxt af |> #1 |> Thm.ctyp_of ctxt;
        val thm = Drule.instantiate' [SOME T] [SOME ct]
          (Conv.rewr_conv (#K_intro rules |> the) (term_of_tterm mk_ap tt |> Thm.cterm_of ctxt))
      in (App (extract_comb 2 thm, tt), thm) end;
    fun unreachable _ = raise ASSERT "eliminate: assertion failed";
    fun elim (Atom _) = unreachable ()
      | elim (Var (i, _, t)) = if exists (fn x => x = i) v then I_step t else unreachable ()
      | elim (App (t1, t2)) = (case (occurs_any v t1, occurs_any v t2) of
            (false, false) => unreachable ()
          | (false, true) => B_step (refl_step t1) (elim t2)
          | (true, false) => (case squash_atoms ctxt af t2 of
                SOME thm => swap_B_step (elim t1) thm
              | NONE => comb2_step (#C_intro rules |> the) (elim t1) (refl_step t2))
          | (true, true) => if has_fact #C_intro af
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
    fun elim_all tt [] = squash_atoms ctxt af tt |> the |> rename_boundvars (map #2 vs) insts
      | elim_all tt ((v, d)::vs) =
          let
            val (tt', rule1) = eliminate ctxt af tt (v, nth insts d);
            val rule2 = elim_all tt' vs;
            val ((ct1, _), ct3) = rule1 |> Thm.rhs_of |> Thm.dest_comb |>> Thm.dest_comb;
            val rule3 = Thm.combination (Thm.combination (Thm.reflexive ct1) rule2) (Thm.reflexive ct3);
          in Thm.transitive rule1 rule3 end;
  in (elim_all (#1 tts) vs, elim_all (#2 tts) vs) end;

val general_normalize_eq_tac = hol_eq_conv_tac oo general_normalform_conv;


(* High-level tactics *)

(* ignores local premises, detects functor instance if not given *)
fun WRAPPER tac ctxt af =
  REPEAT o rtac @{thm HOL.allI} THEN'
  Subgoal.FOCUS (fn {context, ...} =>
    AUTO_AFUN context af (tac context) 1) ctxt THEN'
  TRY o Raw_Simplifier.rewrite_goal_tac ctxt [Drule.triv_forall_equality];

(* FIXME should use a different wrapper *)
val unfold_wrapper_tac = WRAPPER applicative_unfold_tac;

val normalize_wrapper_tac = WRAPPER (fn ctxt => fn af =>
  applicative_unfold_tac ctxt af THEN' normalize_eq_tac ctxt af THEN' head_cong_tac ctxt);

val lifting_wrapper_tac = WRAPPER (fn ctxt => fn af =>
  applicative_unfold_tac ctxt af THEN' general_normalize_eq_tac ctxt af THEN' head_cong_tac ctxt);

end;
