(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Idiomatic terms -- Properties and operations\<close>

theory Idiomatic_Terms
imports Equality_Model
begin

text \<open>
  This theory proves the correctness of the normalisation algorithm for
  arbitrary applicative functors.
\<close>

subsubsection \<open>Extensions to lambda terms\<close>

abbreviation "\<I> \<equiv> Abs (Var 0)"
abbreviation "\<B> \<equiv> Abs (Abs (Abs (Var 2 \<degree> (Var 1 \<degree> Var 0))))"
abbreviation "\<T> \<equiv> Abs (Abs (Var 0 \<degree> Var 1))" -- \<open>reverse application\<close>

lemma I_eval: "\<I> \<degree> x \<rightarrow>\<^sub>\<beta>\<^sup>* x"
proof -
  have "\<I> \<degree> x \<rightarrow>\<^sub>\<beta> x" by (metis beta.beta subst_eq)
  thus ?thesis by simp
qed

lemmas I_equiv = I_eval[THEN beta_into_beta_eta, THEN red_into_equiv]

lemma subst_lift2[simp]: "(lift (lift t 0) 0)[x/Suc 0] = lift t 0"
proof -
  have "lift (lift t 0) 0 = lift (lift t 0) (Suc 0)" using lift_lift by simp
  thus ?thesis by simp
qed

lemma B_eval: "\<B> \<degree> g \<degree> f \<degree> x \<rightarrow>\<^sub>\<beta>\<^sup>* g \<degree> (f \<degree> x)"
proof -
  have "\<B> \<degree> g \<degree> f \<degree> x \<rightarrow>\<^sub>\<beta> Abs (Abs (Var 2 \<degree> (Var 1 \<degree> Var 0)))[g/0] \<degree> f \<degree> x"
    by clarify
  also have "... = Abs (Abs (lift (lift g 0) 0 \<degree> (Var 1 \<degree> Var 0))) \<degree> f \<degree> x"
    by (simp add: numerals)
  also have "... \<rightarrow>\<^sub>\<beta>\<^sup>* Abs (lift (lift g 0) 0 \<degree> (Var 1 \<degree> Var 0))[f/0] \<degree> x"
    by (rule r_into_rtranclp) clarify
  also have "... = Abs (lift g 0 \<degree> (lift f 0 \<degree> Var 0)) \<degree> x"
    by simp
  also have "... \<rightarrow>\<^sub>\<beta>\<^sup>* (lift g 0 \<degree> (lift f 0 \<degree> Var 0))[x/0]"
    by (rule r_into_rtranclp) clarify
  also have "... = g \<degree> (f \<degree> x)" by simp
  finally show ?thesis .
qed

lemmas B_equiv = B_eval[THEN beta_into_beta_eta, THEN red_into_equiv]

lemma T_eval: "\<T> \<degree> x \<degree> f \<rightarrow>\<^sub>\<beta>\<^sup>* f \<degree> x"
proof -
  have "\<T> \<degree> x \<degree> f \<rightarrow>\<^sub>\<beta> Abs (Var 0 \<degree> Var 1)[x/0] \<degree> f" by clarify
  also have "... = Abs (Var 0 \<degree> lift x 0) \<degree> f" by simp
  also have "... \<rightarrow>\<^sub>\<beta>\<^sup>* (Var 0 \<degree> lift x 0)[f/0]" by (rule r_into_rtranclp) clarify
  also have "... \<rightarrow>\<^sub>\<beta>\<^sup>* f \<degree> x" by simp
  finally show ?thesis .
qed

lemmas T_equiv = T_eval[THEN beta_into_beta_eta, THEN red_into_equiv]


lemma subst_liftn:
  "i \<le> n + k \<and> k \<le> i \<Longrightarrow> (liftn (Suc n) s k)[t/i] = liftn n s k"
by (induction s arbitrary: i k t) auto

lemma free_liftn:
  "free (liftn n t k) i = (i < k \<and> free t i \<or> k + n \<le> i \<and> free t (i - n))"
proof (induction t arbitrary: k i)
  case (Var x)
  show ?case by simp arith
next
  case (App s t)
  thus ?case by auto
next
  case (Abs t)
  thus ?case by simp (metis Suc_diff_le add_leD2)
qed


subsubsection \<open>Idiomatic terms\<close>

text \<open>Basic definitions\<close>

datatype itrm =
    Term dB | Pure dB
  | IAp itrm itrm (infixl "\<diamondop>" 150)

locale itrm_cong =
  fixes R :: "itrm \<Rightarrow> itrm \<Rightarrow> bool"
  assumes refl[simp, intro]: "R x x"
  assumes sym[sym]: "R x y \<Longrightarrow> R y x"
  assumes trans[trans]: "R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  assumes iapL: "R x y \<Longrightarrow> R (x \<diamondop> z) (y \<diamondop> z)"
  assumes iapR: "R x y \<Longrightarrow> R (z \<diamondop> x) (z \<diamondop> y)"

locale itrm_eq = eq_model +
  itrm_cong itrm_eq for itrm_eq (infix "\<simeq>" 50) +
    assumes term_cong[intro]: "s =\<^sub>\<Omega> t \<Longrightarrow> Term s \<simeq> Term t"
    assumes pure_cong[intro]: "s =\<^sub>\<Omega> t \<Longrightarrow> Pure s \<simeq> Pure t"
    assumes identity: "Pure \<I> \<diamondop> x \<simeq> x"
    assumes composition: "Pure \<B> \<diamondop> g \<diamondop> f \<diamondop> x \<simeq> g \<diamondop> (f \<diamondop> x)"
    assumes homomorphism: "Pure f' \<diamondop> Pure x' \<simeq> Pure (f' \<degree> x')"
    assumes interchange: "f \<diamondop> Pure x' \<simeq> Pure (\<T> \<degree> x') \<diamondop> f"

(* TODO: define least relation satisfying itrm_eq, depending on eq_model *)
(* TODO: interpretation of idiomatic terms? *)

text \<open>Structural analysis\<close>

inductive itrm_rel :: "(dB \<Rightarrow> dB \<Rightarrow> bool) \<Rightarrow> itrm \<Rightarrow> itrm \<Rightarrow> bool"
for R
where
    rel_term: "R s t \<Longrightarrow> itrm_rel R (Term s) (Term t)"
  | rel_pure: "R s t \<Longrightarrow> itrm_rel R (Pure s) (Pure t)"
  | rel_ap: "itrm_rel R w x \<Longrightarrow> itrm_rel R y z \<Longrightarrow> itrm_rel R (w \<diamondop> y) (x \<diamondop> z)"
(* FIXME: split rel_ap? *)

lemma rel_TermE:
  assumes "itrm_rel R (Term x) y'"
  obtains y where "y' = Term y" and "R x y"
using assms by (induction "Term x" y') simp

lemma rel_PureE:
  assumes "itrm_rel R (Pure x) y'"
  obtains y where "y' = Pure y" and "R x y"
using assms by (induction "Pure x" y') simp

lemma rel_IApE:
  assumes "itrm_rel R (x \<diamondop> y) z"
  obtains x' y' where "z = x' \<diamondop> y'" and "itrm_rel R x x'" and "itrm_rel R y y'"
using assms by (induction "x \<diamondop> y" z) simp

lemma rel_refl: "reflp R \<Longrightarrow> reflp (itrm_rel R)"
proof (rule reflpI)
  fix x
  assume "reflp R"
  then show "itrm_rel R x x" by (induction) (blast intro: itrm_rel.intros dest: reflpD)+
qed

lemma rel_sym: "symp R \<Longrightarrow> symp (itrm_rel R)"
proof (rule sympI)
  fix x y
  assume "itrm_rel R x y" "symp R"
  then show "itrm_rel R y x" by (induction) (blast intro: itrm_rel.intros dest: sympD)+
qed

lemma rel_trans: "transp R \<Longrightarrow> transp (itrm_rel R)"
proof (rule transpI)
  fix x y z
  assume "itrm_rel R x y" "itrm_rel R y z" "transp R"
  then show "itrm_rel R x z" proof (induction arbitrary: z)
    case rel_term then show ?case
      by (blast intro: itrm_rel.rel_term elim: rel_TermE transpE)
  next
    case rel_pure then show ?case
      by (blast intro: itrm_rel.rel_pure elim: rel_PureE transpE)
  next
    case rel_ap then show ?case
      by (blast intro: itrm_rel.rel_ap elim: rel_IApE transpE)
  qed
qed

context eq_model
begin

abbreviation similar :: "itrm \<Rightarrow> itrm \<Rightarrow> bool" (infix "\<cong>" 50)
where "similar \<equiv> itrm_rel op =\<^sub>\<Omega>"

end

primrec opaque :: "itrm \<Rightarrow> dB list"
where
    "opaque (Term x) = [x]"
  | "opaque (Pure _) = []"
  | "opaque (f \<diamondop> x) = opaque f @ opaque x"

abbreviation "iorder x \<equiv> length (opaque x)"

primrec vary_terms :: "nat \<Rightarrow> itrm \<Rightarrow> nat \<Rightarrow> dB \<times> nat"
where
    "vary_terms n (Term _) i = (Var i, Suc i)"
  | "vary_terms n (Pure x) i = (liftn n x 0, i)"
  | "vary_terms n (f \<diamondop> x)  i = (case vary_terms n x i of (x', i') \<Rightarrow>
        apfst (\<lambda>f. f \<degree> x') (vary_terms n f i'))"

abbreviation "unlift' n x i \<equiv> fst (vary_terms n x i)"

abbreviation "unlift x \<equiv> (Abs ^^ iorder x) (unlift' (iorder x) x 0)"


lemma vary_terms_order: "snd (vary_terms n x i) = i + iorder x"
by (induction arbitrary: i) (auto simp add: case_prod_unfold)

lemma unlift_ap: "unlift' n (f \<diamondop> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
by (simp add: case_prod_unfold vary_terms_order)

lemma free_unlift: "free (unlift' n x i) j \<Longrightarrow> j \<ge> n \<or> (j \<ge> i \<and> j < i + iorder x)"
proof (induction x arbitrary: i)
  case (Term x)
  thus ?case by simp
next
  case (Pure x)
  thus ?case using free_liftn by simp
next
  case (IAp x y)
  thus ?case unfolding unlift_ap by fastforce
qed

lemma unlift_subst: "j \<le> i \<and> j \<le> n \<Longrightarrow> (unlift' (Suc n) t (Suc i))[s/j] = unlift' n t i"
proof (induction t arbitrary: i)
  case (Term x)
  thus ?case by simp
next
  case (Pure x)
  thus ?case using subst_liftn by simp
next
  case (IAp x y)
  thus ?case using unlift_ap by simp
qed

lemma (in eq_model) abs_pow_eq: "s =\<^sub>\<Omega> t \<Longrightarrow> (Abs^^n) s =\<^sub>\<Omega> (Abs^^n) t"
by (induction n) (auto intro: abs)

lemma list_equiv_refl[simp]: "list_all2 (op \<leftrightarrow>) x x"
by (induction x) (auto)

lemma list_equiv_suffix: "list_all2 (op \<leftrightarrow>) x y \<Longrightarrow> list_all2 (op \<leftrightarrow>) (x @ z) (y @ z)"
by(rule list_all2_appendI) simp_all

lemma list_equiv_prefix: "list_all2 (op \<leftrightarrow>) x y \<Longrightarrow> list_all2 (op \<leftrightarrow>) (z @ x) (z @ y)"
by(rule list_all2_appendI) simp_all

lemma opaque_rel:
  assumes "itrm_rel R x y"
    shows "list_all2 R (opaque x) (opaque y)"
using assms proof induction
  case rel_term then show ?case by simp
next
  case rel_pure then show ?case by simp
next
  case rel_ap then show ?case by (auto intro: list_all2_appendI)
qed

(* FIXME: update to least member of itrm_eq once defined

lemma opaque_equiv:
  assumes "x \<simeq> y"
    shows "list_all2 (op \<leftrightarrow>) (opaque x) (opaque y)"
using assms proof induction
  case (base_cong x y)
  thus ?case by induction auto
next
  case term_subst
  thus ?case by (auto)
next
  case ap_congL
  thus ?case by (auto intro: list_all2_appendI)
next
  case ap_congR
  thus ?case by (auto intro: list_all2_appendI)
next
  case itrm_sym
  thus ?case using list.rel_conversep[of "op \<leftrightarrow>"] by(simp add: fun_eq_iff)
next
  case itrm_trans
  show ?case by(rule list_all2_trans[OF _ itrm_trans.IH])(rule term_trans)
qed simp_all

lemma iorder_equiv: "x \<simeq> y \<Longrightarrow> iorder x = iorder y"
by(blast dest: opaque_equiv list_all2_lengthD)

lemma unlift'_equiv:
  assumes "x \<simeq> y"
    shows "unlift' n x i \<leftrightarrow> unlift' n y i"
using assms proof (induction arbitrary: n i)
  case (base_cong x y) thus ?case
  proof induction
    case (itrm_id x)
    show ?case
      unfolding unlift_ap using I_equiv[symmetric] by simp
  next
    case (itrm_comp g f x)
    let ?G = "unlift' n g (i + iorder f + iorder x)"
    let ?F = "unlift' n f (i + iorder x)"
    let ?X = "unlift' n x i"
    have "unlift' n (g \<diamondop> (f \<diamondop> x)) i = ?G \<degree> (?F \<degree> ?X)"
      unfolding unlift_ap by (simp add: add.assoc)
    moreover have "unlift' n (Pure \<B> \<diamondop> g \<diamondop> f \<diamondop> x) i = \<B> \<degree> ?G \<degree> ?F \<degree> ?X"
      unfolding unlift_ap by (simp add: add.commute add.left_commute)
    moreover have "?G \<degree> (?F \<degree> ?X) \<leftrightarrow> \<B> \<degree> ?G \<degree> ?F \<degree> ?X" using B_equiv[symmetric] .
    ultimately show ?case by simp
  next
    case (itrm_hom f x)
    show ?case by auto
  next
    case (itrm_xchng f x)
    let ?F = "unlift' n f i"
    let ?X = "liftn n x 0"
    have "unlift' n (f \<diamondop> Pure x) i = ?F \<degree> ?X"
      unfolding unlift_ap by simp
    moreover have "unlift' n (Pure (\<T> \<degree> x) \<diamondop> f) i = \<T> \<degree> ?X \<degree> ?F"
      unfolding unlift_ap by simp
    moreover have "?F \<degree> ?X \<leftrightarrow> \<T> \<degree> ?X \<degree> ?F" using T_equiv[symmetric] .
    ultimately show ?case by simp
  qed
next
  case term_subst
  thus ?case by simp
next
  case pure_subst
  thus ?case by (auto intro: equiv_liftn)
next
  case (ap_congL f f' x)
  have "unlift' n (f \<diamondop> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  moreover have "unlift' n (f' \<diamondop> x) i = unlift' n f' (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  ultimately show ?case using ap_congL.IH equiv_appL by auto
next
  case (ap_congR x x' f)
  from ap_congR.hyps have order_eq: "iorder x = iorder x'"
    using opaque_equiv list_all2_lengthD by blast
  have "unlift' n (f \<diamondop> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  moreover have "unlift' n (f \<diamondop> x') i = unlift' n f (i + iorder x) \<degree> unlift' n x' i"
    unfolding unlift_ap order_eq by simp
  ultimately show ?case using ap_congR.IH equiv_appR by auto
next
  case itrm_sym
  thus ?case using term_sym by simp
next
  case itrm_trans
  thus ?case using term_trans by blast
qed

lemma unlift_equiv: "x \<simeq> y \<Longrightarrow> unlift x \<leftrightarrow> unlift y"
using assms unlift'_equiv wrap_abs_equiv iorder_equiv by simp
*)


subsubsection \<open>Canonical forms\<close>

inductive_set CF :: "itrm set"
where
    pure_cf[simp,intro]: "Pure x \<in> CF"
  | ap_cf[intro]:   "f \<in> CF \<Longrightarrow> f \<diamondop> Term x \<in> CF"

fun CF_head :: "itrm \<Rightarrow> dB"
where
    "CF_head (Pure x) = x"
  | "CF_head (f \<diamondop> x) = CF_head f"

lemma ap_cfD1[dest]: "f \<diamondop> x \<in> CF \<Longrightarrow> f \<in> CF"
by (rule CF.cases) auto

lemma ap_cfD2[dest]: "f \<diamondop> x \<in> CF \<Longrightarrow> \<exists>x'. x = Term x'"
by (rule CF.cases) auto

lemma term_not_cf[dest]: "Term x \<in> CF \<Longrightarrow> False"
by (rule CF.cases) auto

context eq_model
begin

(* FIXME: generalize to itrm_rel *)
lemma cf_similarI:
  assumes "x \<in> CF" "y \<in> CF"
      and "list_all2 (op =\<^sub>\<Omega>) (opaque x) (opaque y)"
      and "CF_head x =\<^sub>\<Omega> CF_head y"
    shows "x \<cong> y"
using assms proof (induction arbitrary: y)
  case (pure_cf x)
  hence "opaque y = []" by auto
  with `y \<in> CF` obtain y' where "y = Pure y'" by cases auto
  with pure_cf.prems show ?case by (auto intro: rel_pure)
next
  case (ap_cf f x)
  from `list_all2 (op =\<^sub>\<Omega>) (opaque (f \<diamondop> Term x)) (opaque y)`
  obtain y1 y2 where "opaque y = y1 @ y2" and "list_all2 (op =\<^sub>\<Omega>) (opaque f) y1" 
    and "list_all2 (op =\<^sub>\<Omega>) [x] y2"  by (auto simp add: list_all2_append1)
  from `list_all2 (op =\<^sub>\<Omega>) [x] y2` obtain y' where "y2 = [y']" and "x =\<^sub>\<Omega> y'"
    by(auto simp add: list_all2_Cons1)
  with `y \<in> CF` and `opaque y = y1 @ y2` obtain g
    where "opaque g = y1" and y_split: "y = g \<diamondop> Term y'" "g \<in> CF" by cases auto
  with ap_cf.prems `list_all2 (op =\<^sub>\<Omega>) (opaque f) y1`
  have "list_all2 (op =\<^sub>\<Omega>) (opaque f) (opaque g)" "CF_head f =\<^sub>\<Omega> CF_head g" by auto
  with ap_cf.IH `g \<in> CF` have "f \<cong> g" by simp
  with ap_cf.prems y_split `x =\<^sub>\<Omega> y'` show ?case by (auto intro: rel_term rel_ap)
qed

lemma cf_unlift:
  assumes "x \<in> CF"
    shows "CF_head x =\<^sub>\<Omega> unlift x"
using assms proof (induction set: CF)
  case (pure_cf x)
  show ?case by simp
next
  case (ap_cf f x)
  let ?n = "iorder f + 1"
  have "unlift (f \<diamondop> Term x) = (Abs ^^ ?n) (unlift' ?n f 1 \<degree> Var 0)"
    unfolding unlift_ap by simp
  also have "... = (Abs ^^ iorder f) (Abs (unlift' ?n f 1 \<degree> Var 0))"
    by (simp add: funpow_swap1)
  also have "... =\<^sub>\<Omega> unlift f" proof -
    have "\<not> free (unlift' ?n f 1) 0" using free_unlift by fastforce
    hence "Abs (unlift' ?n f 1 \<degree> Var 0) \<rightarrow>\<^sub>\<eta> (unlift' ?n f 1)[Var 0/0]" ..
    also have "... = unlift' (iorder f) f 0"
      using unlift_subst by (metis One_nat_def Suc_eq_plus1 le0)
    finally show ?thesis
      by (simp add: abs_pow_eq eta_to_eq)
  qed
  also note ap_cf.IH[symmetric]
  finally have "CF_head f =\<^sub>\<Omega> unlift (f \<diamondop> Term x)" ..
  then show ?case by simp
qed

(* FIXME: generalize to itrm_rel *)
lemma cf_similarD:
  assumes in_cf: "x \<in> CF" "y \<in> CF"
      and similar: "x \<cong> y"
    shows "CF_head x =\<^sub>\<Omega> CF_head y \<and> list_all2 (op =\<^sub>\<Omega>) (opaque x) (opaque y)"
proof
  from similar in_cf show "CF_head x =\<^sub>\<Omega> CF_head y" by induction auto
next
  from similar show "list_all2 op =\<^sub>\<Omega> (opaque x) (opaque y)" by (rule opaque_rel)
qed

end

text \<open>Equivalent idiomatic terms in canonical form are similar. This justifies speaking of a
  normal form.\<close>

(* FIXME: update to least member of itrm_eq once defined

lemma cf_unique:
  assumes in_cf: "x \<in> CF" "y \<in> CF"
      and equiv: "x \<simeq> y"
    shows "x \<cong> y"
using in_cf proof (rule cf_similarI)
  from equiv show "list_all2 (op \<leftrightarrow>) (opaque x) (opaque y)" by (rule opaque_equiv)
next
  from equiv have "unlift x \<leftrightarrow> unlift y" by (rule unlift_equiv)
  thus "CF_head x \<leftrightarrow> CF_head y"
    using cf_unlift[OF in_cf(1)] cf_unlift[OF in_cf(2)]
    using term_sym term_trans
    by metis
qed
*)

subsubsection \<open>Normalization of idiomatic terms\<close>

fun rsize :: "itrm \<Rightarrow> nat"
where
    "rsize (x \<diamondop> y) = size y"
  | "rsize _ = 0"

(* FIXME: consider splitting argument for normalize_* *)

function (sequential) normalize_pure_cf :: "itrm \<Rightarrow> itrm"
where
    "normalize_pure_cf (Pure g \<diamondop> (f \<diamondop> x)) = normalize_pure_cf (Pure (\<B> \<degree> g) \<diamondop> f) \<diamondop> x"
  | "normalize_pure_cf (Pure f \<diamondop> Pure x) = Pure (f \<degree> x)"
  | "normalize_pure_cf x = x"
by pat_completeness auto
termination by (relation "measure rsize") auto

fun normalize_cf_pure :: "itrm \<Rightarrow> itrm"
where
    "normalize_cf_pure (f \<diamondop> Pure x) = normalize_pure_cf (Pure (\<T> \<degree> x) \<diamondop> f)"
  | "normalize_cf_pure x = x"

function (sequential) normalize_cf_cf :: "itrm \<Rightarrow> itrm"
where
    "normalize_cf_cf (g \<diamondop> (f \<diamondop> x)) = normalize_cf_cf (normalize_pure_cf (Pure \<B> \<diamondop> g) \<diamondop> f) \<diamondop> x"
  | "normalize_cf_cf x = normalize_cf_pure x"
by pat_completeness auto
termination by (relation "measure rsize") auto

fun normalize :: "itrm \<Rightarrow> itrm"
where
    "normalize (Pure x) = Pure x"
  | "normalize (Term x) = Pure \<I> \<diamondop> Term x"
  | "normalize (x \<diamondop> y)  = normalize_cf_cf (normalize x \<diamondop> normalize y)"


(*
  FIXME: We actually want to show that "normalize x" and x are related by all relations
  satisfying itrm_eq. The current lemmas follow, and we can use unlift_equiv (in an adjusted form)
  to show that "CF_head (normalize x) =\<^sub>\<Omega> unlift x". This in turn generalizes nf_lifting.
*)

context itrm_eq
begin

lemma pure_cf_in_cf:
  assumes "x \<in> CF"
    shows "normalize_pure_cf (Pure f \<diamondop> x) \<in> CF"
using assms
by (induction arbitrary: f rule: CF.induct) auto

lemma pure_cf_equiv: "normalize_pure_cf x \<simeq> x"
proof (induction rule: normalize_pure_cf.induct)
  case (1 g f x)
  have "normalize_pure_cf (Pure g \<diamondop> (f \<diamondop> x)) \<simeq> normalize_pure_cf (Pure (\<B> \<degree> g) \<diamondop> f) \<diamondop> x" by simp
  also from "1.IH" have "... \<simeq> Pure (\<B> \<degree> g) \<diamondop> f \<diamondop> x" by (rule iapL)
  also have "... \<simeq> Pure \<B> \<diamondop> Pure g \<diamondop> f \<diamondop> x" by (blast intro: homomorphism[symmetric] iapL)
  also have "... \<simeq> Pure g \<diamondop> (f \<diamondop> x)" by (rule composition)
  finally show ?case .
next
  case (2 f x)
  have "normalize_pure_cf (Pure f \<diamondop> Pure x) \<simeq> Pure (f \<degree> x)" by simp
  also have "... \<simeq> Pure f \<diamondop> Pure x" by (rule homomorphism[symmetric])
  finally show ?case .
qed auto

lemma cf_pure_in_cf:
  assumes "f \<in> CF"
    shows "normalize_cf_pure (f \<diamondop> Pure x) \<in> CF"
using assms
by (auto intro: pure_cf_in_cf)

lemma cf_pure_equiv: "normalize_cf_pure x \<simeq> x"
proof (induction rule: normalize_cf_pure.induct)
  case (1 f x)
  have "normalize_cf_pure (f \<diamondop> Pure x) \<simeq> normalize_pure_cf (Pure (\<T> \<degree> x) \<diamondop> f)" by simp
  also have "... \<simeq> Pure (\<T> \<degree> x) \<diamondop> f" by (rule pure_cf_equiv)
  also have "... \<simeq> f \<diamondop> Pure x" by (rule interchange[symmetric])
  finally show ?case .
qed auto

lemma cf_cf_in_cf:
  assumes "x \<in> CF" and "f \<in> CF"
    shows "normalize_cf_cf (f \<diamondop> x) \<in> CF"
using assms
by (induction arbitrary: f rule: CF.induct) (auto intro: pure_cf_in_cf)

lemma cf_cf_equiv: "normalize_cf_cf x \<simeq> x"
proof (induction rule: normalize_cf_cf.induct)
  case (1 g f x)
  have "normalize_cf_cf (g \<diamondop> (f \<diamondop> x)) \<simeq> normalize_cf_cf (normalize_pure_cf (Pure \<B> \<diamondop> g) \<diamondop> f) \<diamondop> x"
    by simp
  also from "1.IH" have "... \<simeq> normalize_pure_cf (Pure \<B> \<diamondop> g) \<diamondop> f \<diamondop> x" by (rule iapL)
  also have "... \<simeq> Pure \<B> \<diamondop> g \<diamondop> f \<diamondop> x" by (blast intro: pure_cf_equiv iapL)
  also have "... \<simeq> g \<diamondop> (f \<diamondop> x)" by (rule composition)
  finally show ?case .
qed (auto simp del: normalize_cf_pure.simps intro: cf_pure_equiv)

lemma normalize_in_cf: "normalize x \<in> CF"
by (induction x rule: normalize.induct) (auto intro: cf_cf_in_cf)

lemma normalize_equiv: "normalize x \<simeq> x"
proof (induction rule: normalize.induct)
  case (2 x)
  have "normalize (Term x) \<simeq> Pure \<I> \<diamondop> Term x" by simp
  also have "... \<simeq> Term x" by (rule identity)
  finally show ?case .
next
  case (3 x y)
  have "normalize (x \<diamondop> y) \<simeq> normalize_cf_cf (normalize x \<diamondop> normalize y)" by simp
  also have "... \<simeq> normalize x \<diamondop> normalize y" by (rule cf_cf_equiv)
  also from "3.IH" have "... \<simeq> x \<diamondop> normalize y" by (blast intro: iapL)
  also from "3.IH" have "... \<simeq> x \<diamondop> y" by (blast intro: iapR)
  finally show ?case .
qed auto

lemma normal_form: obtains n where "n \<simeq> x" and "n \<in> CF"
using normalize_equiv normalize_in_cf ..

end


subsubsection \<open>Proving lifted equations\<close>

(* FIXME: update

theorem nf_lifting:
  assumes opaque: "list_all2 (op \<leftrightarrow>) (opaque x) (opaque y)"
      and base_eq: "unlift x \<leftrightarrow> unlift y"
    shows "x \<simeq> y"
proof -
  obtain n where "n \<simeq> x" and "n \<in> CF" by (rule normal_form)
  hence n_head: "CF_head n \<leftrightarrow> unlift x"
    using cf_unlift unlift_equiv by (blast intro: term_trans)
  from `n \<simeq> x` have n_opaque: "list_all2 (op \<leftrightarrow>) (opaque n) (opaque x)"
    by (rule opaque_equiv)
  obtain n' where "n' \<simeq> y" and "n' \<in> CF" by (rule normal_form)
  hence n'_head: "CF_head n' \<leftrightarrow> unlift y"
    using cf_unlift unlift_equiv by (blast intro: term_trans)
  from `n' \<simeq> y` have n'_opaque: "list_all2 (op \<leftrightarrow>) (opaque n') (opaque y)"
    by (rule opaque_equiv)
  from n_head n'_head base_eq have "CF_head n \<leftrightarrow> CF_head n'"
    by (blast intro: term_sym term_trans)
  moreover from n_opaque n'_opaque opaque list.rel_conversep[of "op \<leftrightarrow>"]
  have "list_all2 (op \<leftrightarrow>) (opaque n) (opaque n')"
    by(auto simp add: fun_eq_iff elim!: list_all2_trans[where ?P2.0="op \<leftrightarrow>", rotated] intro: term_trans)
  moreover note `n \<in> CF` `n' \<in> CF`
  ultimately have "n \<cong> n'" by (blast intro: cf_similarI)
  hence "n \<simeq> n'" by (rule similar_equiv)
  with `n \<simeq> x` `n' \<simeq> y` show "x \<simeq> y" by (blast intro: itrm_sym itrm_trans)
qed
*)

end
