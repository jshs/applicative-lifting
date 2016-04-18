(* Author: Joshua Schneider, ETH Zurich *)

signature APPLICATIVE =
sig
  type afun
  val intern: Context.generic -> xstring -> string
  val extern: Context.generic -> string -> xstring
  val afun_of_generic: Context.generic -> string -> afun
  val afun_of: Proof.context -> string -> afun
  val afuns_of_term_generic: Context.generic -> term -> afun list
  val afuns_of_term: Proof.context -> term -> afun list
  val afuns_of_typ_generic: Context.generic -> typ -> afun list
  val afuns_of_typ: Proof.context -> typ -> afun list

  val name_of_afun: afun -> binding
  val terms_of_afun: afun -> term * term
  val unfolds_of_afun: afun -> thm list
  val lift_type: afun -> typ list -> typ -> typ
  val pure: afun -> typ list -> typ -> term
  val lift: afun -> typ list -> term -> term
  val ap: Proof.context -> afun -> typ -> term
  val lift_comb: Proof.context -> afun -> term * term -> term
  val dest_type: Proof.context -> afun -> typ -> typ * typ list
  val dest_pure: Proof.context -> afun -> term -> term * typ list
  val dest_pure': Proof.context -> afun -> term -> term
  val dest_comb: Proof.context -> afun -> term -> term * term

  val afun_unfold_tac: Proof.context -> afun -> int -> tactic
  val afun_fold_tac: Proof.context -> afun -> int -> tactic
  val unfold_all_tac: Proof.context -> int -> tactic
  val normalform_conv: Proof.context -> afun -> conv
  val normalize_rel_tac: Proof.context -> afun -> int -> tactic
  val general_normalform_conv: Proof.context -> afun -> cterm * cterm -> thm * thm
  val general_normalize_rel_tac: Proof.context -> afun -> int -> tactic
  val forward_lift_rule: Proof.context -> afun -> thm -> thm
  val unfold_wrapper_tac: Proof.context -> afun option -> int -> tactic
  val fold_wrapper_tac: Proof.context -> afun option -> int -> tactic
  val normalize_wrapper_tac: Proof.context -> afun option -> int -> tactic
  val lifting_wrapper_tac: Proof.context -> afun option -> int -> tactic

  val setup_combinators: (string * thm) list -> local_theory -> local_theory
  val combinator_eq_attrib: string list option -> attribute
  val applicative_cmd: ((((binding * string list) * string) * string) * string option) ->
    local_theory -> Proof.state
  val print_afuns: Proof.context -> unit
  val add_unfold_attrib: xstring option -> attribute
  val forward_lift_attrib: xstring -> attribute
  val parse_opt_afun: afun option context_parser
end;

structure Applicative : APPLICATIVE =
struct

(** General utilities **)

fun dest_comb2 (f $ x $ y) = (f, (x, y))
  | dest_comb2 t = raise TERM ("dest_comb2", [t]);

fun mk_TFrees Ss ctxt = Variable.invent_types Ss ctxt |>> map TFree;
val mk_TFrees' = mk_TFrees oo replicate;

fun mk_Free name typ ctxt = Variable.variant_fixes [name] ctxt
  |>> (fn name' => Free (name', typ)) o the_single;


(** Internal representation **)

type sign =
 {pure: term,
  ap: term,
  T: typ * typ,  (* variable, type pattern *)
  sort: sort,
  params: typ list,
  param_sorts: sort list,
  rel: term option};

fun map_sign f1 f2 f3 f4 f5 f6 f7 {pure, ap, T, sort, params, param_sorts, rel} =
  {pure = f1 pure, ap = f2 ap, T = f3 T, sort = f4 sort, params = f5 params,
    param_sorts = f6 param_sorts, rel = Option.map f7 rel};

fun morph_sign phi = map_sign (Morphism.term phi) (Morphism.term phi) (apply2 (Morphism.typ phi))
  I (map (Morphism.typ phi)) I (Morphism.term phi);

type rel_axioms =
 {pure_transfer: thm,
  ap_transfer: thm,
  eq_rel_refl: thm};

fun map_rel_axioms f {pure_transfer, ap_transfer, eq_rel_refl} =
  {pure_transfer = f pure_transfer, ap_transfer = f ap_transfer, eq_rel_refl = f eq_rel_refl};

type axioms =
 {homomorphism: thm,
  interchange: thm,
  combinators: thm Symtab.table,
  relator: rel_axioms option};

fun map_axioms f {homomorphism, interchange, combinators, relator} =
  {homomorphism = f homomorphism, interchange = f interchange,
    combinators = Symtab.map (K f) combinators, relator = Option.map (map_rel_axioms f) relator};

val morph_axioms = map_axioms o Morphism.thm;

val combinator_axiom = Symtab.lookup o #combinators;

type facts =
 {I_intro: thm,
  B_intro: thm,
  C_intro: thm option,
  K_intro: thm option,
  W_intro: thm option,
  merge: thm,
  swap: thm,
  B_pure: thm,
  rel_intros: thm list};

fun map_facts f {I_intro, B_intro, C_intro, K_intro, W_intro, merge, swap, B_pure, rel_intros} =
  {I_intro = f I_intro, B_intro = f B_intro, C_intro = Option.map f C_intro,
    K_intro = Option.map f K_intro, W_intro = Option.map f W_intro, merge = f merge, swap = f swap,
    B_pure = f B_pure, rel_intros = map f rel_intros};

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

fun has_fact af fact = is_some (fact (facts_of_afun af));

fun mk_afun name sign axioms facts =
  AFun {name = name, sign = sign, axioms = axioms, facts = facts, unfolds = []};

fun map_afun f1 f2 f3 f4 f5 (AFun {name, sign, axioms, facts, unfolds}) =
  AFun {name = f1 name, sign = f2 sign, axioms = f3 axioms, facts = f4 facts,
    unfolds = f5 unfolds};

fun morph_afun phi =
  map_afun (Morphism.binding phi) (morph_sign phi) (morph_axioms phi) (morph_facts phi)
    (map (Morphism.thm phi));

(* FIXME is this (i.e. Thm.transfer) really needed? *)
val transfer_afun = morph_afun o Morphism.transfer_morphism;

fun add_unfolds thms = map_afun I I I I (union Thm.eq_thm_prop thms);


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

fun rel_sign {rel = opt_rel, params, ...} insts (T1, T2) =
  let
    val rel = the opt_rel;
    val (var1, var2) = Term.fastype_of rel
      |> Term.domain_type
      |> Term.dest_funT
      ||> Term.domain_type;
  in Term.subst_atomic_types ((var1, T1) :: (var2, T2) :: (params ~~ insts)) rel end;

val lift_type = lift_type_sign o sign_of_afun;
val pure = pure_sign o sign_of_afun;
val lift = lift_sign o sign_of_afun;
fun ap ctxt = ap_sign ctxt o sign_of_afun;
fun lift_comb ctxt = comb_sign ctxt o sign_of_afun;

fun lift_terms_sign ctxt sign Us (ts, lift_vars) =
  let
    fun map_var (var_name, (free_name, T)) = if member (op =) lift_vars var_name
      then
        let val free = Free (free_name, T)
        in (free, (var_name, lift_sign sign Us free)) end
      else
        let val free = Free (free_name, lift_type_sign sign Us T)
        in (free, (var_name, free)) end;

    val (var_names, var_Ts) = split_list (fold Term.add_vars ts []);
    val (free_names, ctxt') = Variable.variant_fixes (map #1 var_names) ctxt;
    val (frees, var_map) = split_list (map map_var (var_names ~~ (free_names ~~ var_Ts)));

    fun is_pure t = null (Term.add_vars t []);
    fun lift_term (Const c) = lift_sign sign Us (Const c)
      | lift_term (Abs a) = lift_sign sign Us (Abs a)
      | lift_term (Var (var, _)) = the (AList.lookup (op =) var_map var)
      | lift_term (s $ t) = (case (is_pure s, is_pure t) of
              (true, true) => lift_sign sign Us (s $ t)
            | (true, false) => comb_sign ctxt' sign (lift_sign sign Us s, lift_term t)
            | (false, true) => comb_sign ctxt' sign (lift_term s, lift_sign sign Us t)
            | (false, false) => comb_sign ctxt' sign (lift_term s, lift_term t))
      | lift_term t = raise TERM ("lift_terms_sign", [t]);
  in ((map lift_term ts, frees), ctxt') end;

(* TODO: cache patterns *)

fun pure_pattern {pure, ...} =
  let
    val (argT, _) = Term.fastype_of pure |> Term.dest_funT;
    val var = ((Name.uu, Term.maxidx_of_term pure + 1), argT);
  in (Term.betapply (pure, Var var), var) end;

fun ap_pattern {ap, ...} =
  let
    val (arg1T, (arg2T, _)) = Term.fastype_of ap |> Term.dest_funT ||> Term.dest_funT;
    val i = Term.maxidx_of_term ap;
    val var1 = ((Name.uu, i + 1), arg1T);
    val var2 = ((Name.uu, i + 2), arg2T);
  in (Term.betapplys (ap, [Var var1, Var var2]), (var1, var2)) end;

fun patterns_of_afun af =
  let val sign = sign_of_afun af
  in [#1 (pure_pattern sign), #1 (ap_pattern sign), sign |> #T |> #2 |> Net.encode_type] end;

fun dest_type_sign ctxt sign T =
  let
    val thy = Proof_Context.theory_of ctxt;
    val {T = (var, tycon), params, ...} = sign;
    val tyenv = Sign.typ_match thy (tycon, T) Vartab.empty
      handle Type.TYPE_MATCH => raise TYPE ("dest_type", [T, tycon], []);
  in (the (Type.lookup tyenv (Term.dest_TVar var)),
    map (the o Type.lookup tyenv o Term.dest_TVar) params) end;

fun dest_type ctxt af T = dest_type_sign ctxt (sign_of_afun af) T;

fun dest_pure_sign ctxt sign t =
  let
    val thy = Proof_Context.theory_of ctxt;
    val {params, ...} = sign;
    val (pat, var) = pure_pattern sign;
    val (tyenv, env) = Pattern.match thy (pat, t) (Vartab.empty, Vartab.empty)
      handle Pattern.MATCH => raise TERM ("dest_pure", [t, pat]);
  in (the (Envir.lookup1 env var),
    map (the o Type.lookup tyenv o Term.dest_TVar) params) end;

fun dest_pure ctxt af t = dest_pure_sign ctxt (sign_of_afun af) t;
fun dest_pure' ctxt af t = #1 (dest_pure ctxt af t);

fun dest_comb_sign ctxt sign t =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (pat, vars) = ap_pattern sign;
    val (_, env) = Pattern.match thy (pat, t) (Vartab.empty, Vartab.empty)
      handle Pattern.MATCH => raise TERM ("dest_ap", [t, pat]);
  in apply2 (the o Envir.lookup1 env) vars end;

fun dest_comb ctxt af t = dest_comb_sign ctxt (sign_of_afun af) t;


(** Basic conversions **)

(* FIXME: can we avoid recertification here? *)
(* FIXME: improve implementations *)

fun pure_conv_sign ctxt sign cv ct =
  let
    val (cta, Ts) = dest_pure_sign ctxt sign (Thm.term_of ct);
    val thm = cv (Thm.cterm_of ctxt cta);
    val argT = thm |> Thm.lhs_of |> Thm.typ_of_cterm;
    val pure_inst = Thm.cterm_of ctxt (pure_sign sign Ts argT);
  in Drule.arg_cong_rule pure_inst thm end;

fun ap_conv_sign ctxt sign cv1 cv2 ct =
  let
    val (ct1, ct2) = dest_comb_sign ctxt sign (Thm.term_of ct);
    val thm1 = cv1 (Thm.cterm_of ctxt ct1);
    val thm2 = cv2 (Thm.cterm_of ctxt ct2);
    val funT = thm1 |> Thm.lhs_of |> Thm.typ_of_cterm;
    val ap_inst = Thm.cterm_of ctxt (ap_sign ctxt sign funT);
  in Drule.binop_cong_rule ap_inst thm1 thm2 end;


(** Combinators and derivation of their reductions **)

datatype combinator_rule = Combinator_Rule of
 {strong_premises: string Ord_List.T,
  weak_premises: bool,
  conclusion: string,
  eq_thm: thm};

fun rep_combinator_rule (Combinator_Rule rule) = rule;
val conclusion_of_rule = #conclusion o rep_combinator_rule;
val thm_of_rule = #eq_thm o rep_combinator_rule;

fun eq_combinator_rule (rule1, rule2) =
  pointer_eq (rule1, rule2) orelse Thm.eq_thm (thm_of_rule rule1, thm_of_rule rule2);

fun explode_combinator_eq combs thm =
  let
    val (lhs, rhs) = Logic.dest_equals (Thm.prop_of thm);
    val (conclusion, _) = dest_Const lhs;
    val rhs_consts = Ord_List.make fast_string_ord (map #1 (Term.add_consts rhs []));
    val premises = Ord_List.inter fast_string_ord rhs_consts combs;
  in (conclusion, premises) end;

fun mk_combinator_rule combs weak_combs thm =
  let
    val (conclusion, premises) = explode_combinator_eq combs thm;
    val weak_premises = Ord_List.make fast_string_ord (these weak_combs);
    val strong_premises = Ord_List.subtract fast_string_ord weak_premises premises;
  in Combinator_Rule
   {strong_premises = strong_premises,
    weak_premises = is_some weak_combs,
    conclusion = conclusion,
    eq_thm = thm} end;

fun map_combinator_rule f1 f2 f3 f4
  (Combinator_Rule {strong_premises, weak_premises, conclusion, eq_thm}) =
    Combinator_Rule {strong_premises = f1 strong_premises, weak_premises = f2 weak_premises,
      conclusion = f3 conclusion, eq_thm = f4 eq_thm};

fun transfer_combinator_rule thy = map_combinator_rule I I I (Thm.transfer thy);

fun is_applicable have_weak have_premises rule =
  let val {strong_premises, weak_premises, ...} = rep_combinator_rule rule;
  in (have_weak orelse not weak_premises) andalso have_premises strong_premises end;

fun combinator_closure rules have_weak combs =
  let
    fun apply rule (cs, changed) =
      if not (Ord_List.member fast_string_ord cs (conclusion_of_rule rule)) andalso
        is_applicable have_weak (fn prems => Ord_List.subset fast_string_ord (prems, cs)) rule
      then (Ord_List.insert fast_string_ord (conclusion_of_rule rule) cs, true)
      else (cs, changed);
    fun loop cs = case fold apply rules (cs, false) of
        (cs', true) => loop cs'
      | (_, false) => cs;
  in loop combs end;

fun derive_combinator sign ctxt (base_thm, eq_thm) red_thms =
  let
    val base = Thm.prop_of base_thm;
    val tvars = Term.add_tvars base [];
    val ((Us, Ts), ctxt_Ts) = ctxt
      |> mk_TFrees (#param_sorts sign)
      ||>> mk_TFrees' (length tvars) (#sort sign);
    val base' = Term_Subst.instantiate (tvars ~~ Ts, []) base;
    val (lhs, rhs) = Logic.dest_equals base';
    val (([lhs', rhs'], _), ctxt') = lift_terms_sign ctxt_Ts sign Us ([lhs, rhs], []);
    val lifted = (lhs', rhs') |> HOLogic.mk_eq |> HOLogic.mk_Trueprop;
    val tac = HEADGOAL (CONVERSION (Conv.top_sweep_conv (K (Conv.rewr_conv eq_thm)) ctxt') THEN'
      Raw_Simplifier.rewrite_goal_tac ctxt' red_thms THEN'
      resolve_tac ctxt' [@{thm refl}]);
  in singleton (Variable.export ctxt' ctxt) (Goal.prove ctxt' [] [] lifted (K tac)) end;

(* FIXME: more of a workaround than a sensible solution *)
fun weak_red_closure (sign, merge_thm) ctxt strong_red =
  let
    val (lhs, _) = Thm.prop_of strong_red |> Logic.dest_equals;
    val vars = rev (Term.add_vars lhs []);
    fun closure [] prev thms = (prev::thms)
      | closure ((v, af_T)::vs) prev thms = case try (dest_type_sign ctxt sign) af_T of
            NONE => closure vs prev thms
          | SOME (T, Us) =>
            let
              val (v', ctxt') = mk_Free (#1 v) T ctxt;
              val pure_v = Thm.cterm_of ctxt' (lift_sign sign Us v');
              val next = Drule.instantiate_normalize ([], [((v, af_T), pure_v)]) prev;
              val next' = Raw_Simplifier.rewrite_rule ctxt' [merge_thm] next;
              val next'' = singleton (Variable.export ctxt' ctxt) next';
            in closure vs next'' (prev::thms) end;
   in closure vars strong_red [] end;

fun combinator_red_closure (sign, hom_thm) ctxt comb_defs rules weak_reds combs =
  let
    val merge_thm = hom_thm RS eq_reflection;
    val have_weak = not (null weak_reds);
    val red_thms0 = Symtab.fold (fn (_, thm) => cons (thm RS eq_reflection)) combs weak_reds;
    val red_thms = flat (map (weak_red_closure (sign, merge_thm) ctxt) red_thms0);
    val derive = derive_combinator sign ctxt;
    fun apply rule ((cs, rs), changed) =
      if not (Symtab.defined cs (conclusion_of_rule rule)) andalso
        is_applicable have_weak (forall (Symtab.defined cs)) rule
      then
        let
          val conclusion = conclusion_of_rule rule;
          val def = Symtab.lookup comb_defs conclusion |> the;
          val red_thm = derive (def, thm_of_rule rule) rs;
          val red_thms = weak_red_closure (sign, merge_thm) ctxt (red_thm RS eq_reflection);
        in ((Symtab.update (conclusion, red_thm) cs, red_thms @ rs), true) end
      else ((cs, rs), changed);
    fun loop xs = case fold apply rules (xs, false) of
        (xs', true) => loop xs'
      | (_, false) => xs;
  in #1 (loop (combs, red_thms)) end;


(** Context data **)

(* FIXME carefully verify context storage *)
(* FIXME needs tests, especially around theory merging *)

fun join_afuns _ (af1, af2) = if pointer_eq (af1, af2)
  then raise Change_Table.SAME
  else add_unfolds (unfolds_of_afun af2) af1;

structure Data = Generic_Data
(
  type T =
   {combinators: string Symtab.table * thm Symtab.table,
    combinator_rules: combinator_rule list,
    afuns: afun Name_Space.table,
    patterns: (string * term list) Item_Net.T};
  val empty =
   {combinators = (Symtab.empty, Symtab.empty),
    combinator_rules = [],
    afuns = Name_Space.empty_table "applicative functor",
    patterns = Item_Net.init (op = o apply2 #1) #2};
  val extend = I;
  fun merge ({combinators = (cn1, cd1), combinator_rules = cr1, afuns = a1, patterns = p1},
             {combinators = (cn2, cd2), combinator_rules = cr2, afuns = a2, patterns = p2}) =
   {combinators = (Symtab.merge (K true) (cn1, cn2), Symtab.merge (K true) (cd1, cd2)),
    combinator_rules = Library.merge eq_combinator_rule (cr1, cr2),
    afuns = Name_Space.join_tables join_afuns (a1, a2),
    patterns = Item_Net.merge (p1, p2)};
);

fun get_combinators context =
  let
    val {combinators = (by_name, defs), ...} = Data.get context;
    val transfer_thm = Thm.transfer (Context.theory_of context);
  in (by_name, Symtab.map (K transfer_thm) defs) end;

fun get_combinator_rules context =
  let val {combinator_rules, ...} = Data.get context
  in map (transfer_combinator_rule (Context.theory_of context)) combinator_rules end;

val get_afuns = #afuns o Data.get;
val get_afun_space = Name_Space.space_of_table o get_afuns;
val get_patterns = #patterns o Data.get;

fun map_data f1 f2 f3 f4 {combinators, combinator_rules, afuns, patterns} =
  {combinators = f1 combinators, combinator_rules = f2 combinator_rules, afuns = f3 afuns,
    patterns = f4 patterns};

val intern = Name_Space.intern o get_afun_space;
fun extern context = Name_Space.extern (Context.proof_of context) (get_afun_space context);

local fun undeclared name = error ("Undeclared applicative functor " ^ quote name);
in

fun afun_of_generic context name = case Name_Space.lookup (get_afuns context) name of
    SOME af => transfer_afun (Context.theory_of context) af
  | NONE => undeclared name;

val afun_of = afun_of_generic o Context.Proof;

fun update_afun name f context = if Name_Space.defined (get_afuns context) name
  then Data.map (map_data I I (Name_Space.map_table_entry name f) I) context
  else undeclared name;

end;

fun match_term context = map #1 o Item_Net.retrieve_matching (get_patterns context);
fun match_typ context = match_term context o Net.encode_type;

(* works only with terms which are combinations of pure and ap *)
fun afuns_of_term_generic context = map (afun_of_generic context) o match_term context;
val afuns_of_term = afuns_of_term_generic o Context.Proof;

fun afuns_of_typ_generic context = map (afun_of_generic context) o match_typ context;
val afuns_of_typ = afuns_of_typ_generic o Context.Proof;

fun all_unfolds_of_generic context =
  Name_Space.fold_table (fn (_, af) => append (unfolds_of_afun af)) (get_afuns context) [];
val all_unfolds_of = all_unfolds_of_generic o Context.Proof;

(* FIXME pervasive? *)
fun register_afun af =
  let fun decl phi context = Data.map (fn {combinators, combinator_rules, afuns, patterns} =>
    let
      val af' = morph_afun phi af;
      val (name, afuns') = Name_Space.define context true (name_of_afun af, af') afuns;
      val patterns' = Item_Net.update (name, patterns_of_afun af') patterns;
    in
      {combinators = combinators, combinator_rules = combinator_rules, afuns = afuns',
        patterns = patterns'}
    end) context;
  in Local_Theory.declaration {syntax = false, pervasive = false} decl end;


(* Combinator setup *)

fun combinator_of_red thm =
  let
    val (lhs, _) = Logic.dest_equals (Thm.prop_of thm);
    val (head, _) = strip_comb lhs;
  in #1 (dest_Const head) end;

fun add_combinators combs =
  let
    val (names, thms) = split_list combs;
    val consts = map combinator_of_red thms;
    val thms' = map Thm.trim_context thms;
    fun add_combs (by_name, defs) = (fold (Symtab.insert (K false)) (names ~~ consts) by_name,
        fold (Symtab.insert (K false)) (consts ~~ thms') defs);
  in Data.map (map_data add_combs I I I) end;

fun add_combinator_rule weak_names thm context =
  let
    val (lhs, rhs) = Logic.dest_equals (Thm.prop_of thm);
    val ltvars = Term.add_tvars lhs [];
    val rtvars = Term.add_tvars rhs [];
    val _ = if exists (not o member op = ltvars) rtvars
      then Pretty.breaks
         [Pretty.str "Combinator equation",
          Pretty.quote (Syntax.pretty_term (Context.proof_of context) (Thm.prop_of thm)),
          Pretty.str "has additional type variables on right-hand side."]
        |> Pretty.block |> Pretty.string_of |> error
      else ();

    val (by_name, comb_defs) = get_combinators context;
    val combs = Ord_List.make fast_string_ord (Symtab.keys comb_defs);
    val weak_combs = Option.map (map (the o Symtab.lookup by_name)) weak_names;
    val rule = mk_combinator_rule combs weak_combs thm;
    val add_rule = insert eq_combinator_rule rule;
  in Data.map (map_data I add_rule I I) context end;

(* FIXME *)
fun setup_combinators combs lthy = lthy
  |> Local_Theory.background_theory (Context.theory_map (add_combinators combs))
  |> Local_Theory.map_contexts (K (Context.proof_map (add_combinators combs)));

fun combinator_eq_attrib weak_combs = Thm.declaration_attribute (add_combinator_rule weak_combs);


(** Reasoning with applicative functors **)

(* Utilities *)

val clean_name = perhaps (perhaps_apply [try Name.dest_skolem, try Name.dest_internal]);

(* based on term_name from Pure/term.ML *)
fun term_to_vname (Const (x, _)) = Long_Name.base_name x
  | term_to_vname (Free (x, _)) = clean_name x
  | term_to_vname (Var ((x, _), _)) = clean_name x
  | term_to_vname _ = "x";

fun afuns_of_rel precise ctxt t =
  let val (_, (lhs, rhs)) = Variable.focus NONE t ctxt
    |> #1 |> #2
    |> Logic.strip_imp_concl
    |> Envir.beta_eta_contract
    |> HOLogic.dest_Trueprop
    |> dest_comb2;
  in if precise
    then (case afuns_of_term ctxt lhs of
        [] => afuns_of_term ctxt rhs
      | afs => afs)
    else afuns_of_typ ctxt (Term.fastype_of lhs) end;

fun AUTO_AFUNS precise tac ctxt opt_af = case opt_af of
    SOME af => tac [af]
  | NONE => SUBGOAL (fn (goal, i) => (case afuns_of_rel precise ctxt goal of
      [] => no_tac
    | afs => tac afs i) handle TERM _ => no_tac);

fun AUTO_AFUN precise tac = AUTO_AFUNS precise (tac o hd);

fun binop_par_conv cv ct =
  let
    val ((binop, arg1), arg2) = Thm.dest_comb ct |>> Thm.dest_comb;
    val (th1, th2) = cv (arg1, arg2);
  in Drule.binop_cong_rule binop th1 th2 end;

fun binop_par_conv_tac cv = CONVERSION (HOLogic.Trueprop_conv (binop_par_conv cv));

val fold_goal_tac = SELECT_GOAL oo Raw_Simplifier.fold_goals_tac;


(* Unfolding of lifted constants *)

fun afun_unfold_tac ctxt af = Raw_Simplifier.rewrite_goal_tac ctxt (unfolds_of_afun af);
fun afun_fold_tac ctxt af = fold_goal_tac ctxt (unfolds_of_afun af);

fun unfold_all_tac ctxt = Raw_Simplifier.rewrite_goal_tac ctxt (all_unfolds_of ctxt);


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

val normalize_rel_tac = binop_par_conv_tac o apply2 oo normalform_conv;


(* Bracket abstraction and generalized unlifting *)

datatype apterm =
    Pure of term  (* includes pure application *)
  | ApVar of int * term  (* unique index, instantiated term *)
  | Ap of apterm * apterm;

fun apterm_vars (Pure _) = I
  | apterm_vars (ApVar v) = cons v
  | apterm_vars (Ap (t1, t2)) = apterm_vars t1 #> apterm_vars t2;

fun occurs_any _ (Pure _) = false
  | occurs_any vs (ApVar (i, _)) = exists (fn j => i = j) vs
  | occurs_any vs (Ap (t1, t2)) = occurs_any vs t1 orelse occurs_any vs t2;

fun term_of_apterm ctxt af t =
  let
    fun tm_of (Pure t) = t
      | tm_of (ApVar (_, t)) = t
      | tm_of (Ap (t1, t2)) = lift_comb ctxt af (tm_of t1, tm_of t2);
  in tm_of t end;

fun apterm_of_term ctxt af t =
  let
    fun aptm_of t i = case try (dest_comb ctxt af) t of
        SOME (t1, t2) => i |> aptm_of t1 ||>> aptm_of t2 |>> Ap
      | NONE => if can (dest_pure ctxt af) t
          then (Pure t, i)
          else (ApVar (i, t), i + 1);
  in aptm_of t end;

fun consolidate ctxt af (t1, t2) =
  let
    fun common_inst (i, t) (j, insts) = case Termtab.lookup insts t of
        SOME k => (((i, t), k), (j, insts))
      | NONE => (((i, t), j), (j + 1, Termtab.update (t, j) insts));

    val (vars, _) = (0, Termtab.empty)
      |> fold_map common_inst (apterm_vars t1 [])
      ||>> fold_map common_inst (apterm_vars t2 []);

    fun merge_adjacent (([], _), _) [] = []
      | merge_adjacent ((is, t), d) [] = [((is, t), d)]
      | merge_adjacent (([], _), _) (((i, t), d)::xs) = merge_adjacent (([i], t), d) xs
      | merge_adjacent ((is, t), d) (((i', t'), d')::xs) = if d = d'
          then merge_adjacent ((i'::is, t), d) xs
          else ((is, t), d) :: merge_adjacent (([i'], t'), d') xs;

    fun align _ [] = NONE
      | align ((i, t), d) (((i', t'), d')::xs) = if d = d'
          then SOME ([((i @ i', t), d)], xs)
          else Option.map (apfst (cons ((i', t'), d'))) (align ((i, t), d) xs);
    fun merge ([], ys) = ys
      | merge (xs, []) = xs
      | merge ((xs as ((is1, t1), d1)::xs'), ys as (((is2, t2), d2)::ys')) = if d1 = d2
          then ((is1 @ is2, t1), d1) :: merge (xs', ys')
          else case (align ((is2, t2), d2) xs, align ((is1, t1), d1) ys) of
              (SOME (zs, xs''), NONE) => zs @ merge (xs'', ys')
            | (NONE, SOME (zs, ys'')) => zs @ merge (xs', ys'')
            | _ => ((is1, t1), d1) :: ((is2, t2), d2) :: merge (xs', ys');

    fun unbalanced vs = error ("Unbalanced opaque terms " ^
      commas_quote (map (Syntax.string_of_term ctxt o #2 o #1) vs));
    fun mismatch (t1, t2) = error ("Mismatched opaque terms " ^
      quote (Syntax.string_of_term ctxt t1) ^ " and " ^ quote (Syntax.string_of_term ctxt t2));
    fun same ([], []) = []
      | same ([], ys) = unbalanced ys
      | same (xs, []) = unbalanced xs
      | same ((((i1, t1), d1)::xs), (((i2, t2), d2)::ys)) = if d1 = d2
          then ((i1 @ i2, t1), d1) :: same (xs, ys)
          else mismatch (t1, t2);
  in vars
    |> has_fact af #C_intro ? apply2 (sort (int_ord o apply2 #2))
    |> apply2 (if has_fact af #W_intro
        then merge_adjacent (([], Term.dummy), 0)
        else map (apfst (apfst single)))
    |> (if has_fact af #K_intro then merge else same)
    |> map #1
  end;

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
    fun squash (Pure t) = SOME (Thm.reflexive (Thm.cterm_of ctxt t))
      | squash (ApVar _) = NONE
      | squash (Ap (tt1, tt2)) = case squash tt1 of
          NONE => NONE
        | SOME thm1 => case squash tt2 of
            NONE => NONE
          | SOME thm2 => SOME (rewr_subst_ap ctxt af merge thm1 thm2);
  in squash tt end;

exception ASSERT of string;

fun eliminate ctxt af tt (v, v_tm) =
  let
    val rules = facts_of_afun af;
    val has_C_comb = has_fact af #C_intro;

    val rewr_subst_ap = rewr_subst_ap ctxt af;
    fun extract_comb n thm = Pure (thm |> Thm.rhs_of |> funpow n Thm.dest_arg1 |> Thm.term_of);
    fun refl_step tt = (tt, Thm.reflexive (Thm.cterm_of ctxt (term_of_apterm ctxt af tt)));
    fun comb2_step def (tt1, thm1) (tt2, thm2) =
      let val thm = rewr_subst_ap def thm1 thm2;
      in (Ap (Ap (extract_comb 3 thm, tt1), tt2), thm) end;
    val B_step = comb2_step (#B_intro rules);
    fun swap_B_step (tt1, thm1) thm2 =
      let
        val thm3 = rewr_subst_ap (#swap rules) thm1 thm2;
        val thm4 = Thm.transitive thm3 (Conv.rewr_conv (#B_intro rules) (Thm.rhs_of thm3));
      in (Ap (Ap (extract_comb 3 thm4, extract_comb 1 thm3), tt1), thm4) end;
    fun I_step tm =
      let val thm = Conv.rewr_conv (#I_intro rules) (Thm.cterm_of ctxt tm)
      in (extract_comb 1 thm, thm) end;
    fun W_step s1 s2 =
      let
        val (Ap (Ap (tt1, tt2), tt3), thm1) = B_step s1 s2;
        val thm2 = Conv.rewr_conv (#B_intro rules) (Thm.rhs_of thm1 |> funpow 2 Thm.dest_arg1);
        val thm3 = squash_atoms ctxt af tt3 |> the;
        val (tt4, thm4) = swap_B_step (Ap (Ap (extract_comb 3 thm2, tt1), tt2), thm2) thm3;
        val var = Thm.rhs_of thm1 |> Thm.dest_arg;
        val thm5 = rewr_subst_ap (#W_intro rules |> the) thm4 (Thm.reflexive var);
        val thm6 = Thm.transitive thm1 thm5;
      in (Ap (extract_comb 2 thm6, tt4), thm6) end;
    fun S_step s1 s2 =
      let
        val (Ap (Ap (tt1, tt2), tt3), thm1) = comb2_step (#C_intro rules |> the) s1 s2;
        val thm2 = Conv.rewr_conv (#B_intro rules) (Thm.rhs_of thm1 |> Thm.dest_arg1);
        val var = Thm.rhs_of thm1 |> Thm.dest_arg;
        val thm3 = rewr_subst_ap (#W_intro rules |> the) thm2 (Thm.reflexive var);
        val thm4 = Thm.transitive thm1 thm3;
        val tt = Ap (extract_comb 2 thm4, Ap (Ap (extract_comb 3 thm2, Ap (tt1, tt2)), tt3));
      in (tt, thm4) end;
    fun K_step tt tm =
      let
        val ct = Thm.cterm_of ctxt tm;
        val T = Term.fastype_of tm |> dest_type ctxt af |> #1 |> Thm.ctyp_of ctxt;
        val thm = Thm.instantiate' [SOME T] [SOME ct]
          (Conv.rewr_conv (#K_intro rules |> the) (term_of_apterm ctxt af tt |> Thm.cterm_of ctxt))
      in (Ap (extract_comb 2 thm, tt), thm) end;
    fun unreachable _ = raise ASSERT "eliminate: assertion failed";
    fun elim (Pure _) = unreachable ()
      | elim (ApVar (i, t)) = if exists (fn x => x = i) v then I_step t else unreachable ()
      | elim (Ap (t1, t2)) = (case (occurs_any v t1, occurs_any v t2) of
            (false, false) => unreachable ()
          | (false, true) => B_step (refl_step t1) (elim t2)
          | (true, false) => (case squash_atoms ctxt af t2 of
                SOME thm => swap_B_step (elim t1) thm
              | NONE => comb2_step (#C_intro rules |> the) (elim t1) (refl_step t2))
          | (true, true) => if has_C_comb
              then S_step (elim t1) (elim t2)
              else W_step (elim t1) (elim t2));
  in if occurs_any v tt
    then elim tt
    else K_step tt v_tm
  end;

fun rename_boundvars ctxt af vs thm =
  let
    fun rename [] t = t
      | rename ((_, v)::vs) (Abs (_, T, t)) = Abs (term_to_vname v, T, rename vs t)
      | rename _ t = t;
    fun rename_pure t = t
      |> dest_pure' ctxt af
      |> rename (rev vs)
      |> lift af (Term.fastype_of t |> dest_type ctxt af |> #2);
    val prop' = Thm.prop_of thm
      |> Logic.dest_equals
      ||> rename_pure
      |> Logic.mk_equals;
  in Thm.renamed_prop prop' thm end;

fun general_normalform_conv ctxt af cts =
  let
    val (t1, t2) = apply2 (Thm.term_of) cts;
    val ((apt1, apt2), _) = 0 |> apterm_of_term ctxt af t1 ||>> apterm_of_term ctxt af t2;
    val vs = consolidate ctxt af (apt1, apt2);
    fun elim_all tt [] = squash_atoms ctxt af tt |> the |> rename_boundvars ctxt af vs
      | elim_all tt (v::vs) =
          let
            val (tt', rule1) = eliminate ctxt af tt v;
            val rule2 = elim_all tt' vs;
            (* FIXME remaining use of plain term destruction instead of Applicative.dest_comb *)
            val ((ct1, _), ct3) = rule1 |> Thm.rhs_of |> Thm.dest_comb |>> Thm.dest_comb;
            val rule3 = Thm.combination (Thm.combination (Thm.reflexive ct1) rule2) (Thm.reflexive ct3);
          in Thm.transitive rule1 rule3 end;
  in (elim_all apt1 vs, elim_all apt2 vs) end;

val general_normalize_rel_tac = binop_par_conv_tac oo general_normalform_conv;


(* Reduce canonical forms to base relation *)

(*
  R' (pure f <> x1 <> ... <> xn) (pure g <> x1 <> ... <> xn)
    ===> !!x1 ... xn. R (f x1 ... xn) (g x1 ... xn),
  where either both R and R' are equality, or R' = relF R for relator relF of the functor.
  Succeeds if partial progress can be made.
*)
fun head_cong_tac ctxt af =
  let val {rel_intros, ...} = facts_of_afun af
  in REPEAT_DETERM o resolve_tac ctxt rel_intros THEN'
    REPEAT_DETERM o resolve_tac ctxt [ext, @{thm rel_fun_eqI}] end;


(* Forward lifting *)

(* FIXME: use lift_terms_sign *)
fun forward_lift_rule ctxt af thm =
  let
    val sign = sign_of_afun af;
    val prop = Thm.prop_of thm;
    val tvars = Term.add_tvars prop [];
    val ((Ts, Us), ctxt') = ctxt
      |> mk_TFrees (map #2 tvars)
      ||>> mk_TFrees (#param_sorts sign);
    val prop' = Term.subst_atomic_types (map TVar tvars ~~ Ts) prop;
    val (var_names, var_Ts) = split_list (Term.add_vars prop' []);
    val (free_names, ctxt'') = Variable.variant_fixes (map #1 var_names) ctxt';
    val frees = map (fn (var, T) => Free (var, lift_type af Us T)) (free_names ~~ var_Ts);
    val var_map = var_names ~~ frees;

    fun is_pure t = null (Term.add_vars t []);

    fun lift_term (Const c) = lift af Us (Const c)
      | lift_term (Abs a) = lift af Us (Abs a)
      | lift_term (Var (var, _)) = the (AList.lookup (op =) var_map var)
      | lift_term (s $ t) = (case (is_pure s, is_pure t) of
              (true, true) => lift af Us (s $ t)
            | (true, false) => lift_comb ctxt'' af (lift af Us s, lift_term t)
            | (false, true) => lift_comb ctxt'' af (lift_term s, lift af Us t)
            | (false, false) => lift_comb ctxt'' af (lift_term s, lift_term t))
      | lift_term t = raise TERM ("forward_lift_rule", [t]);

    val (lhs, rhs) = prop' |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;
    val lifted_prop = HOLogic.mk_eq (lift_term lhs, lift_term rhs) |> HOLogic.mk_Trueprop;
    val tac = general_normalize_rel_tac ctxt'' af THEN'
      head_cong_tac ctxt'' af THEN'
      resolve_tac ctxt'' [thm];
    val thm' = singleton (Variable.export ctxt'' ctxt)
      (Goal.prove ctxt'' [] [] lifted_prop (K (tac 1)));
    val thm'' = Raw_Simplifier.fold_rule ctxt (unfolds_of_afun af) thm';
  in thm'' end;

fun forward_lift_attrib name =
  Thm.rule_attribute [] (fn context => fn thm =>
    let val af = afun_of_generic context (intern context name)  (* FIXME !?!? *)
    in forward_lift_rule (Context.proof_of context) af thm end);


(* High-level tactics *)

fun unfold_wrapper_tac ctxt = AUTO_AFUNS false (fn afs =>
  Simplifier.safe_asm_full_simp_tac (ctxt addsimps flat (map unfolds_of_afun afs))) ctxt;

fun fold_wrapper_tac ctxt = AUTO_AFUN true (fold_goal_tac ctxt o unfolds_of_afun) ctxt;

fun WRAPPER tac ctxt opt_af =
  REPEAT_DETERM o resolve_tac ctxt [@{thm allI}] THEN'
  Subgoal.FOCUS (fn {context = ctxt, ...} =>
      AUTO_AFUNS false (EVERY' o map (afun_unfold_tac ctxt)) ctxt opt_af 1 THEN
      AUTO_AFUN true (fn af =>
        afun_unfold_tac ctxt af THEN'
        CONVERSION Drule.beta_eta_conversion THEN'
        tac ctxt af THEN'
        head_cong_tac ctxt af) ctxt opt_af 1) ctxt;

val normalize_wrapper_tac = WRAPPER normalize_rel_tac;
val lifting_wrapper_tac = WRAPPER general_normalize_rel_tac;

val parse_opt_afun = Scan.peek (fn context =>
  Scan.option Parse.xname >> Option.map (intern context #> afun_of_generic context));


(** Declaration **)

fun mk_sign ctxt (raw_pure, raw_ap, raw_rel) =
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
    val param_sorts = map (fn (_, S) => Sign.inter_sort thy (S, @{sort HOL.type})) params;

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

    (* TODO: check relator *)
    val rel = Option.map closed_poly_term raw_rel;

    val sort = foldl1 (Sign.inter_sort thy) [pure_sort, ap_sort1, ap_sort2, @{sort HOL.type}];
    val _ = Sign.of_sort thy (Term.aT sort --> Term.aT sort, sort) orelse
      error ("Sort constraint " ^ quote (Syntax.string_of_sort ctxt sort) ^
        " not closed under function types");
  in
   {pure = pure, ap = ap, T = (TVar var, tycon), sort = sort, params = map TVar params,
     param_sorts = param_sorts, rel = rel}
  end;

fun mk_rel_intros ctxt sign {pure_transfer, ap_transfer, eq_rel_refl} =
  let
    val pure_rel_intro = pure_transfer RS @{thm rel_funD};
    val ap_rel_intro = ap_transfer RS @{thm rel_funD} RS @{thm rel_funD};

    val (([T1, T2, T3], Us), ctxt') = ctxt
      |> mk_TFrees' 3 (#sort sign)
      ||>> mk_TFrees (#param_sorts sign);
    val T12 = lift_type_sign sign Us (T1 --> T2);
    val T13 = lift_type_sign sign Us (T1 --> T3);
    val ((((R, f), g), x), ctxt'') = ctxt'
      |> mk_Free "R" (T2 --> T3 --> @{typ bool})
      ||>> mk_Free "f" (lift_type_sign sign Us (T1 --> T2))
      ||>> mk_Free "g" (lift_type_sign sign Us (T1 --> T3))
      ||>> mk_Free "x" (lift_type_sign sign Us T1);

    fun mk_af_rel tR t1 t2 = betapplys
      (rel_sign sign Us (BNF_Util.dest_pred2T (Term.fastype_of tR)), [tR, t1, t2]);
    val ap_funrel_prop = Logic.mk_implies
      (HOLogic.mk_Trueprop (mk_af_rel (BNF_Util.mk_rel_fun (HOLogic.eq_const T1) R) f g),
        HOLogic.mk_Trueprop (mk_af_rel R
          (comb_sign ctxt'' sign (f, x)) (comb_sign ctxt'' sign (g, x))));
    val ap_funrel_tac = HEADGOAL (resolve_tac ctxt'' [ap_rel_intro] THEN'
      RANGE [assume_tac ctxt'', resolve_tac ctxt'' [eq_rel_refl]]);
    val ap_funrel_intro = Goal.prove ctxt'' [] [] ap_funrel_prop (K ap_funrel_tac);
    val ap_funrel_intro' = singleton (Variable.export ctxt'' ctxt) ap_funrel_intro;
  in [pure_rel_intro, ap_funrel_intro'] end;

fun mk_facts ctxt sign axioms =
  let
    fun comb_intro thm = Thm.symmetric (thm RS eq_reflection);
    val B_intro = comb_intro (combinator_axiom axioms @{const_name B} |> the);
    val merge_rule = #homomorphism axioms RS eq_reflection;

    val B_pure =
      let
        val (([T1, T2, T3], Ts), ctxt') = ctxt
          |> mk_TFrees' 3 (#sort sign)
          ||>> mk_TFrees (#param_sorts sign);
        val (((g, f), x), ctxt'') = ctxt'
          |> mk_Free "g" (T2 --> T3)
          ||>> mk_Free "f" (lift_type_sign sign Ts (T1 --> T2))
          ||>> mk_Free "x" (lift_type_sign sign Ts T1);
        val comb = comb_sign ctxt'' sign;
        val lhs = comb (lift_sign sign Ts g, comb (f, x));
        val B_g = Abs ("f", T1 --> T2, Abs ("x", T1, Term.betapply (g, Bound 1 $ Bound 0)));
        val rhs = comb (comb (lift_sign sign Ts B_g, f), x);
        val prop = Logic.mk_equals (lhs, rhs);
        val tac =
          HEADGOAL (Raw_Simplifier.rewrite_goal_tac ctxt'' [B_intro, merge_rule] THEN'
          resolve_tac ctxt'' [reflexive_thm]);
      in singleton (Variable.export ctxt'' ctxt) (Goal.prove ctxt'' [] [] prop (K tac)) end;

    val eq_intros =
      let
        val (([T1, T2], Us), ctxt') = ctxt
          |> mk_TFrees' 2 (#sort sign)
          ||>> mk_TFrees (#param_sorts sign);
        val T12 = lift_type_sign sign Us (T1 --> T2);
        val (((((x, y), x'), f), g), ctxt'') = ctxt'
          |> mk_Free "x" T1
          ||>> mk_Free "y" T1
          ||>> mk_Free "x" (lift_type_sign sign Us T1)
          ||>> mk_Free "f" T12
          ||>> mk_Free "g" T12;
        val pure_fun = pure_sign sign Us T1;
        val pure_cong = Drule.infer_instantiate' ctxt''
          (map (SOME o Thm.cterm_of ctxt'') [x, y, pure_fun]) @{thm arg_cong};
        val ap_fun = ap_sign ctxt'' sign T12;
        val ap_cong1 = Drule.infer_instantiate' ctxt''
          (map (SOME o Thm.cterm_of ctxt'') [f, g, ap_fun, x']) @{thm arg1_cong};
      in Variable.export ctxt'' ctxt [pure_cong, ap_cong1] end;

    val rel_intros = case #relator axioms of
        NONE => []
      | SOME rel_axioms => mk_rel_intros ctxt sign rel_axioms;
  in
    {I_intro = comb_intro (combinator_axiom axioms @{const_name I} |> the),
      B_intro = B_intro,
      C_intro = Option.map comb_intro (combinator_axiom axioms @{const_name C}),
      K_intro = Option.map comb_intro (combinator_axiom axioms @{const_name K}),
      W_intro = Option.map comb_intro (combinator_axiom axioms @{const_name W}),
      merge = merge_rule,
      swap = #interchange axioms RS eq_reflection,
      B_pure = B_pure,
      rel_intros = eq_intros @ rel_intros}
  end;

fun reuse_TFrees n S (ctxt, Ts) =
  let
    val have_n = Int.min (n, length Ts);
    val (more_Ts, ctxt') = mk_TFrees' (n - have_n) S ctxt;
  in (take have_n Ts @ more_Ts, (ctxt', Ts @ more_Ts)) end;

fun mk_comb_prop lift_pos thm sign Us ctxt_Ts =
  let
    val base = Thm.prop_of thm;
    val tvars = Term.add_tvars base [];
    val (Ts, (ctxt', Ts')) = reuse_TFrees (length tvars) (#sort sign) ctxt_Ts;
    val base' = Term_Subst.instantiate (tvars ~~ Ts, []) base;
    val (lhs, rhs) = Logic.dest_equals base';
    val (_, lhs_vars) = strip_comb lhs;
    val lift_vars = map (#1 o dest_Var o nth lhs_vars) lift_pos;
    val (([lhs', rhs'], frees), _) = lift_terms_sign ctxt' sign Us ([lhs, rhs], lift_vars);
    val lifted = (lhs', rhs') |> HOLogic.mk_eq |> HOLogic.mk_Trueprop;
  in (fold Logic.all frees lifted, (ctxt', Ts')) end;

fun mk_homomorphism_prop sign Us ctxt_Ts =
  let
    val ([T1, T2], (ctxt', Ts')) = reuse_TFrees 2 (#sort sign) ctxt_Ts;
    val ((f, x), ctxt'') = ctxt'
      |> mk_Free "f" (T1 --> T2)
      ||>> mk_Free "x" T1;
    val lhs = comb_sign ctxt'' sign (lift_sign sign Us f, lift_sign sign Us x);
    val rhs = lift_sign sign Us (f $ x);
    val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in (Logic.all f (Logic.all x prop), (ctxt', Ts')) end;

fun mk_interchange_prop sign Us ctxt_Ts =
  let
    val ([T1, T2], (ctxt', Ts')) = reuse_TFrees 2 (#sort sign) ctxt_Ts;
    val ((f, x), ctxt'') = ctxt'
      |> mk_Free "f" (lift_type_sign sign Us (T1 --> T2))
      ||>> mk_Free "x" T1;
    val lhs = comb_sign ctxt'' sign (f, lift_sign sign Us x);
    val T_x = Abs ("f", T1 --> T2, Bound 0 $ x);
    val rhs = comb_sign ctxt'' sign (lift_sign sign Us T_x, f);
    val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in (Logic.all f (Logic.all x prop), (ctxt', Ts')) end;

fun mk_rel_props sign Us ctxt_Ts =
  let
    fun mk_af_rel tm = betapply (rel_sign sign Us (BNF_Util.dest_pred2T (Term.fastype_of tm)), tm);
    val ([T1, T2, T3, T4], (ctxt', Ts')) = reuse_TFrees 4 (#sort sign) ctxt_Ts;

    val (pure_R, _) = mk_Free "R" (T1 --> T2 --> @{typ bool}) ctxt';
    val rel_pure = BNF_Util.mk_rel_fun pure_R (mk_af_rel pure_R) $ pure_sign sign Us T1 $
      pure_sign sign Us T2;
    val pure_prop = Logic.all pure_R (HOLogic.mk_Trueprop rel_pure);

    val ((ap_R, ap_S), ap_ctxt) = ctxt'
      |> mk_Free "R" (T1 --> T2 --> @{typ bool})
      ||>> mk_Free "S" (T3 --> T4 --> @{typ bool});
    val rel_ap = BNF_Util.mk_rel_fun (mk_af_rel (BNF_Util.mk_rel_fun ap_R ap_S))
        (BNF_Util.mk_rel_fun (mk_af_rel ap_R) (mk_af_rel ap_S)) $
      ap_sign ap_ctxt sign (lift_type_sign sign Us (T1 --> T3)) $
      ap_sign ap_ctxt sign (lift_type_sign sign Us (T2 --> T4));
    val ap_prop = Logic.all ap_R (Logic.all ap_S (HOLogic.mk_Trueprop rel_ap));

    val (x, _) = mk_Free "x" (lift_type_sign sign Us T1) ctxt';
    val eq_rel = betapplys (mk_af_rel (HOLogic.eq_const T1), [x, x]);
    val eq_rel_prop = Logic.all x (HOLogic.mk_Trueprop eq_rel);
  in ([pure_prop, ap_prop, eq_rel_prop], (ctxt', Ts')) end;

fun mk_interchange (sign, hom_thm) ctxt comb_defs comb_unfolds reds =
  let
    val merge_thm = hom_thm RS eq_reflection;
    val T_def = Symtab.lookup comb_defs @{const_name T} |> the;
    val T_red = Symtab.lookup reds @{const_name T} |> the;
    val (Us, ctxt') = mk_TFrees (#param_sorts sign) ctxt;
    val (weak_prop, (ctxt'', _)) = mk_comb_prop [0] T_def sign Us (ctxt', []);
    fun tac {context, ...} = HEADGOAL (resolve_tac context [T_red]);
    val weak_red = singleton (Variable.export ctxt'' ctxt) (Goal.prove ctxt'' [] [] weak_prop tac);
  in Raw_Simplifier.rewrite_rule ctxt (merge_thm :: comb_unfolds) weak_red RS sym end;

fun mk_weak_reds sign ctxt comb_defs comb_unfolds (hom_thm, ichng_thm, reds) =
  let
    val unfolded_reds =
      Symtab.map (K (Raw_Simplifier.rewrite_rule ctxt comb_unfolds)) reds;
    val axioms = {homomorphism = hom_thm, interchange = ichng_thm, combinators = unfolded_reds,
      relator = NONE};
    val facts = mk_facts ctxt sign axioms;
    val af = mk_afun Binding.empty sign axioms facts;

    val (Us, ctxt') = mk_TFrees (#param_sorts sign) ctxt;
    fun tac {context, ...} = HEADGOAL (normalize_wrapper_tac context (SOME af) THEN'
      Raw_Simplifier.rewrite_goal_tac context comb_unfolds THEN'
      resolve_tac context [refl]);
    fun mk comb lift_pos =
      let
        val def = Symtab.lookup comb_defs comb |> the;
        val (prop, (ctxt'', _)) = mk_comb_prop lift_pos def sign Us (ctxt', []);
        val hol_thm = singleton (Variable.export ctxt'' ctxt) (Goal.prove ctxt'' [] [] prop tac);
      in hol_thm RS eq_reflection end;

    (* TODO: not a weak reduction? *)
    val uncurry_thm = forward_lift_rule ctxt af @{thm uncurry_pair} RS eq_reflection;
  in
    [mk @{const_name C} [1], mk @{const_name C} [2], uncurry_thm]
  end;

fun note_afun_thms af =
  let
    val axioms = axioms_of_afun af;
    val named_thms = [];
    (* FIXME
      [("afun_id", #identity axioms),
        ("afun_comp", #composition axioms),
        ("afun_hom", #homomorphism axioms),
        ("afun_ichng", #interchange axioms)]
      |> option I (cons o pair "afun_flip") (#flip axioms)
      |> option I (cons o pair "afun_const") (#const axioms)
      |> option I (cons o pair "afun_dup") (#duplicate axioms); *)

    val base_name = Binding.name_of (name_of_afun af);
    fun mk_note (name, thm) =
      ((Binding.qualify true base_name (Binding.name name), []), [([thm], [])]);
  in Local_Theory.notes (map mk_note named_thms) #> #2 end;

fun applicative_cmd ((((name, flags), pure), ap), rel) lthy =
  let
    val comb_unfolds = Named_Theorems.get lthy @{named_theorems combinator_unfold};
    val comb_reprs = Named_Theorems.get lthy @{named_theorems combinator_repr};
    val (combs_by_name, comb_defs) = get_combinators (Context.Proof lthy);
    val comb_rules = get_combinator_rules (Context.Proof lthy);

    fun lookup_combinator name = case Symtab.lookup combs_by_name name of
        SOME c => c
      | NONE => error ("Unknown combinator " ^ quote name);
    val _ = if has_duplicates op = flags
      then warning "Ignoring duplicate combinators"
      else ();
    val user_combs0 = Ord_List.make fast_string_ord (map lookup_combinator flags);

    val raw_pure = Syntax.read_term lthy pure;
    val raw_ap = Syntax.read_term lthy ap;
    val raw_rel = Option.map (Syntax.read_term lthy) rel;
    val sign = mk_sign lthy (raw_pure, raw_ap, raw_rel);

    val derived_combs0 = combinator_closure comb_rules false user_combs0;
    val required_combs = Ord_List.make fast_string_ord [@{const_name B}, @{const_name I}];
    val user_combs = Ord_List.union fast_string_ord user_combs0
      (Ord_List.subtract fast_string_ord derived_combs0 required_combs);
    val derived_combs1 = combinator_closure comb_rules false user_combs;
    val derived_combs2 = combinator_closure comb_rules true derived_combs1;
    fun is_redundant comb = eq_list (op =) (derived_combs2,
      (combinator_closure comb_rules true (Ord_List.remove fast_string_ord comb user_combs)));
    val redundant_combs = filter is_redundant user_combs;
    (* TODO: print user-level names *)
    val _ = if null redundant_combs then () else
      warning ("Redundant combinators: " ^ commas redundant_combs);
    val prove_interchange = not (Ord_List.member fast_string_ord derived_combs1 @{const_name T});

    val (Us, ctxt_Us) = mk_TFrees (#param_sorts sign) lthy;
    val mk_propss = [apfst single o mk_homomorphism_prop sign Us,
      fold_map (fn comb => mk_comb_prop [] (the (Symtab.lookup comb_defs comb)) sign Us) user_combs,
      if prove_interchange then apfst single o mk_interchange_prop sign Us else pair [],
      if is_some rel then mk_rel_props sign Us else pair []];
    val (propss, (ctxt_Ts, _)) = fold_map I mk_propss (ctxt_Us, []);

    fun repr_tac ctxt = Raw_Simplifier.rewrite_goals_tac ctxt comb_reprs;
    fun after_qed thmss lthy' =
      let
        val [[hom_thm], user_thms, ichng_thms, rel_thms] = map (Variable.export lthy' lthy) thmss;
        val user_reds = Symtab.make (user_combs ~~ user_thms);
        val reds0 = combinator_red_closure (sign, hom_thm) lthy comb_defs comb_rules [] user_reds;
        val ichng_thm = case ichng_thms of
            [] => mk_interchange (sign, hom_thm) lthy comb_defs comb_unfolds reds0
          | [thm] => thm;
        val weak_reds = mk_weak_reds sign lthy comb_defs comb_unfolds (hom_thm, ichng_thm, reds0);
        val reds1 = combinator_red_closure (sign, hom_thm) lthy comb_defs comb_rules weak_reds reds0;
        val unfolded_reds =
          Symtab.map (K (Raw_Simplifier.rewrite_rule lthy comb_unfolds)) reds1;
        val rel_axioms = case rel_thms of
            [] => NONE
          | [thm1, thm2, thm3] => SOME {pure_transfer = thm1, ap_transfer = thm2, eq_rel_refl = thm3};
        val axioms = {homomorphism = hom_thm, interchange = ichng_thm, combinators = unfolded_reds,
          relator = rel_axioms};
        val facts = mk_facts lthy sign axioms;
        val af = mk_afun name sign axioms facts;
      in lthy
        |> register_afun af
        |> note_afun_thms af
      end;
  in
    Proof.theorem NONE after_qed ((map o map) (rpair []) propss) ctxt_Ts
    |> Proof.refine (Method.Basic (SIMPLE_METHOD o repr_tac))
    |> Seq.the_result ""
  end;

(* TODO: print relator *)
fun print_afuns ctxt =
  let
    fun pretty_afun (name, af) =
      let
        val {pure, ap, T, ...} = sign_of_afun af;
        val (tvar, typ) = T;
        (* TODO: print user-level names *)
        val combinators = Symtab.keys (#combinators (axioms_of_afun af));
      in Pretty.block (Pretty.fbreaks [Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1,
          Pretty.quote (Syntax.pretty_typ ctxt typ), Pretty.brk 1, Pretty.str "of", Pretty.brk 1,
          Syntax.pretty_typ ctxt tvar],
        Pretty.block [Pretty.str "pure:", Pretty.brk 1, Pretty.quote (Syntax.pretty_term ctxt pure)],
        Pretty.block [Pretty.str "ap:", Pretty.brk 1, Pretty.quote (Syntax.pretty_term ctxt ap)],
        Pretty.block ([Pretty.str "combinators:", Pretty.brk 1] @
          Pretty.commas (map Pretty.str combinators))]) end;
    val afuns = sort_by #1 (Name_Space.fold_table cons (get_afuns (Context.Proof ctxt)) []);
  in Pretty.writeln (Pretty.big_list "Registered applicative functors:" (map pretty_afun afuns)) end;


(* Unfolding *)

fun add_unfold_thm name thm context =
  let
    val (lhs, _) = Thm.prop_of thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
      handle TERM _ => error "Not an equation";
    val names = case name of
        SOME n => [intern context n]
      | NONE => case match_typ context (Term.fastype_of lhs) of
          ns as (_::_) => ns
        | [] => error "Unable to determine applicative functor instance";
    val _ = map (afun_of_generic context) names;
    (* TODO check equation *)
    (* FIXME could also use Local_Defs.meta_rewrite_rule or unfold_tac *)
    val thm' = thm RS @{thm eq_reflection};
  in fold (fn n => update_afun n (add_unfolds [thm'])) names context end;

fun add_unfold_attrib name = Thm.declaration_attribute (add_unfold_thm name);

(* TODO deletion? *)

end;
