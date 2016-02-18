(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Idiomatic terms -- Properties and operations\<close>

theory Idiomatic_Terms
imports Beta_Eta "~~/src/HOL/Library/Permutation"
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

datatype 'a itrm =
    Opaque 'a | Pure dB
  | IAp "'a itrm" "'a itrm" (infixl "\<diamondop>" 150)

inductive itrm_cong :: "('a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool) \<Rightarrow> 'a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool"
for p
where
    base_cong: "p x y \<Longrightarrow> itrm_cong p x y"
  | pure_subst: "x \<leftrightarrow> y \<Longrightarrow> itrm_cong p (Pure x) (Pure y)"
  | ap_congL: "itrm_cong p f f' \<Longrightarrow> itrm_cong p (f \<diamondop> x) (f' \<diamondop> x)"
  | ap_congR: "itrm_cong p x x' \<Longrightarrow> itrm_cong p (f \<diamondop> x) (f \<diamondop> x')"
  | itrm_refl[simp,intro]: "itrm_cong p x x"
  | itrm_sym[sym]: "itrm_cong p x y \<Longrightarrow> itrm_cong p y x"
  | itrm_trans[trans]: "itrm_cong p x y \<Longrightarrow> itrm_cong p y z \<Longrightarrow> itrm_cong p x z"

lemma ap_cong: "itrm_cong p f f' \<Longrightarrow> itrm_cong p x x' \<Longrightarrow> itrm_cong p (f \<diamondop> x) (f' \<diamondop> x')"
by (blast intro: ap_congL ap_congR itrm_trans)

text \<open>Idiomatic terms are \emph{similar} iff they have the same structure, and all contained
  lambda terms are equivalent.\<close>

abbreviation similar :: "'a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool" (infixl "\<cong>" 50)
where "x \<cong> y \<equiv> itrm_cong (\<lambda>_ _. False) x y"

lemma pure_similarE:
  assumes "Pure x' \<cong> y"
  obtains y' where "y = Pure y'" and "x' \<leftrightarrow> y'"
proof -
  def x == "Pure x' :: 'a itrm"
  from assms have "x \<cong> y" unfolding x_def .
  then have "(\<forall>x''. x = Pure x'' \<longrightarrow> (\<exists>y'. y = Pure y' \<and> x'' \<leftrightarrow> y')) \<and>
    (\<forall>x''. y = Pure x'' \<longrightarrow> (\<exists>y'. x = Pure y' \<and> x'' \<leftrightarrow> y'))"
  proof (induction)
    case pure_subst thus ?case by (auto intro: term_sym)
  next
    case itrm_trans thus ?case by (fastforce intro: term_trans)
  qed simp_all
  with that show thesis unfolding x_def by blast
qed

lemma opaque_similarE:
  assumes "Opaque x' \<cong> y"
  obtains y' where "y = Opaque y'" and "x' = y'"
proof -
  def x == "Opaque x' :: 'a itrm"
  from assms have "x \<cong> y" unfolding x_def .
  then have "(\<forall>x''. x = Opaque x'' \<longrightarrow> (\<exists>y'. y = Opaque y' \<and> x'' = y')) \<and>
    (\<forall>x''. y = Opaque x'' \<longrightarrow> (\<exists>y'. x = Opaque y' \<and> x'' = y'))"
  by induction fast+
  with that show thesis unfolding x_def by blast
qed

lemma ap_similarE:
  assumes "x1 \<diamondop> x2 \<cong> y"
  obtains y1 y2 where "y = y1 \<diamondop> y2" and "x1 \<cong> y1" and "x2 \<cong> y2"
proof -
  from assms
  have "(\<forall>x1' x2'. x1 \<diamondop> x2 = x1' \<diamondop> x2' \<longrightarrow> (\<exists>y1 y2. y = y1 \<diamondop> y2 \<and> x1' \<cong> y1 \<and> x2' \<cong> y2)) \<and>
    (\<forall>x1' x2'. y = x1' \<diamondop> x2' \<longrightarrow> (\<exists>y1 y2. x1 \<diamondop> x2 = y1 \<diamondop> y2 \<and> x1' \<cong> y1 \<and> x2' \<cong> y2))"
  proof (induction)
    case ap_congL thus ?case by (blast intro: itrm_sym)
  next
    case ap_congR thus ?case by (blast intro: itrm_sym)
  next
    case itrm_trans thus ?case by (fastforce intro: itrm_cong.itrm_trans)
  qed simp_all
  with that show thesis by blast
qed

text \<open>The following relations define semantic equivalence of idiomatic terms.\<close>

inductive pre_equiv :: "'a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool"
where
    itrm_id: "pre_equiv x (Pure \<I> \<diamondop> x)"
  | itrm_comp: "pre_equiv (g \<diamondop> (f \<diamondop> x)) (Pure \<B> \<diamondop> g \<diamondop> f \<diamondop> x)"
  | itrm_hom: "pre_equiv (Pure f \<diamondop> Pure x) (Pure (f \<degree> x))"
  | itrm_xchng: "pre_equiv (f \<diamondop> Pure x) (Pure (\<T> \<degree> x) \<diamondop> f)"

abbreviation itrm_equiv :: "'a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool" (infixl "\<simeq>" 50)
where
  "x \<simeq> y \<equiv> itrm_cong pre_equiv x y"

lemma pre_equiv_into_equiv: "pre_equiv x y \<Longrightarrow> x \<simeq> y" ..

lemmas itrm_id' = itrm_id[THEN pre_equiv_into_equiv]
lemmas itrm_comp' = itrm_comp[THEN pre_equiv_into_equiv]
lemmas itrm_hom' = itrm_hom[THEN pre_equiv_into_equiv]
lemmas itrm_xchng' = itrm_xchng[THEN pre_equiv_into_equiv]

lemma similar_equiv: "x \<cong> y \<Longrightarrow> x \<simeq> y"
by (induction pred: itrm_cong) (auto intro: itrm_cong.intros)

text \<open>Structural analysis\<close>

primrec opaque :: "'a itrm \<Rightarrow> 'a list"
where
    "opaque (Opaque x) = [x]"
  | "opaque (Pure _) = []"
  | "opaque (f \<diamondop> x) = opaque f @ opaque x"

abbreviation "iorder x \<equiv> length (opaque x)"

primrec vary_terms :: "nat \<Rightarrow> 'a itrm \<Rightarrow> nat \<Rightarrow> dB \<times> nat"
where
    "vary_terms n (Opaque _) i = (Var i, Suc i)"
  | "vary_terms n (Pure x) i = (liftn n x 0, i)"
  | "vary_terms n (f \<diamondop> x)  i = (case vary_terms n x i of (x', i') \<Rightarrow>
        apfst (\<lambda>f. f \<degree> x') (vary_terms n f i'))"

abbreviation "unlift' n x i \<equiv> fst (vary_terms n x i)"

primrec wrap_abs :: "dB \<Rightarrow> nat \<Rightarrow> dB"
where
    "wrap_abs t 0 = t"
  | "wrap_abs t (Suc n) = Abs (wrap_abs t n)"

abbreviation "unlift x \<equiv> wrap_abs (unlift' (iorder x) x 0) (iorder x)"


lemma vary_terms_order: "snd (vary_terms n x i) = i + iorder x"
by (induction arbitrary: i) (auto simp add: case_prod_unfold)

lemma unlift_ap: "unlift' n (f \<diamondop> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
by (simp add: case_prod_unfold vary_terms_order)

lemma free_unlift: "free (unlift' n x i) j \<Longrightarrow> j \<ge> n \<or> (j \<ge> i \<and> j < i + iorder x)"
proof (induction x arbitrary: i)
  case (Opaque x)
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
  case (Opaque x)
  thus ?case by simp
next
  case (Pure x)
  thus ?case using subst_liftn by simp
next
  case (IAp x y)
  hence "j \<le> i + iorder y" by simp
  with IAp show ?case using unlift_ap by (metis add_Suc subst_App)
qed

lemma wrap_abs_inside: "wrap_abs t (Suc n) = wrap_abs (Abs t) n"
by (induction n) auto

lemma wrap_abs_equiv: "s \<leftrightarrow> t \<Longrightarrow> wrap_abs s n \<leftrightarrow> wrap_abs t n"
by (induction n) auto

lemma opaque_equiv:
  assumes "x \<simeq> y"
    shows "opaque x = opaque y"
using assms proof induction
  case (base_cong x y)
  thus ?case by induction auto
qed simp_all

lemma iorder_equiv: "x \<simeq> y \<Longrightarrow> iorder x = iorder y"
by (auto dest: opaque_equiv)

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
    by (rule iorder_equiv)
  have "unlift' n (f \<diamondop> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  moreover have "unlift' n (f \<diamondop> x') i = unlift' n f (i + iorder x) \<degree> unlift' n x' i"
    unfolding unlift_ap order_eq by simp
  ultimately show ?case using ap_congR.IH equiv_appR by auto
next
  case itrm_refl
  thus ?case by simp
next
  case itrm_sym
  thus ?case using term_sym by simp
next
  case itrm_trans
  thus ?case using term_trans by blast
qed

lemma unlift_equiv: "x \<simeq> y \<Longrightarrow> unlift x \<leftrightarrow> unlift y"
proof -
  assume "x \<simeq> y"
  then have "unlift' (iorder y) x 0 \<leftrightarrow> unlift' (iorder y) y 0" by (rule unlift'_equiv)
  moreover from `x \<simeq> y` have "iorder x = iorder y" by (rule iorder_equiv)
  ultimately show ?thesis by (auto intro: wrap_abs_equiv)
qed

lemma unlift_all_pure: "opaque x = [] \<Longrightarrow> x \<simeq> Pure (unlift x)"
proof (induction x)
  case (Opaque x) then show ?case by simp
next
  case (Pure x) then show ?case by simp
next
  case (IAp x y)
  then have no_opaque: "opaque x = []" "opaque y = []" by simp+
  then have unlift_ap: "unlift (x \<diamondop> y) = unlift x \<degree> unlift y"
    unfolding unlift_ap by simp
  from no_opaque IAp.IH have "x \<diamondop> y \<simeq> Pure (unlift x) \<diamondop> Pure (unlift y)"
    by (blast intro: ap_cong)
  also have "... \<simeq> Pure (unlift x \<degree> unlift y)" by (rule itrm_hom')
  also have "... = Pure (unlift (x \<diamondop> y))" by (simp only: unlift_ap)
  finally show ?case .
qed


subsubsection \<open>Canonical forms\<close>

inductive_set CF :: "'a itrm set"
where
    pure_cf[simp,intro]: "Pure x \<in> CF"
  | ap_cf[intro]:   "f \<in> CF \<Longrightarrow> f \<diamondop> Opaque x \<in> CF"

fun CF_head :: "'a itrm \<Rightarrow> dB"
where
    "CF_head (Pure x) = x"
  | "CF_head (f \<diamondop> x) = CF_head f"

lemma ap_cfD1[dest]: "f \<diamondop> x \<in> CF \<Longrightarrow> f \<in> CF"
by (rule CF.cases) auto

lemma ap_cfD2[dest]: "f \<diamondop> x \<in> CF \<Longrightarrow> \<exists>x'. x = Opaque x'"
by (rule CF.cases) auto

lemma opaque_not_cf[dest]: "Opaque x \<in> CF \<Longrightarrow> False"
by (rule CF.cases) auto

lemma cf_similarI:
  assumes "x \<in> CF" "y \<in> CF"
      and "opaque x = opaque y"
      and "CF_head x \<leftrightarrow> CF_head y"
    shows "x \<cong> y"
using assms proof (induction arbitrary: y)
  case (pure_cf x)
  hence "opaque y = []" by auto
  with `y \<in> CF` obtain y' where "y = Pure y'" by cases auto
  with pure_cf.prems show ?case by (auto intro: itrm_cong.intros)
next
  case (ap_cf f x)
  from `opaque (f \<diamondop> Opaque x) = opaque y`
  obtain y1 y2 where "opaque y = y1 @ y2"
    and "opaque f = y1" and "[x] = y2" by fastforce
  from `[x] = y2` obtain y' where "y2 = [y']" and "x = y'"
    by auto
  with `y \<in> CF` and `opaque y = y1 @ y2` obtain g
    where "opaque g = y1" and y_split: "y = g \<diamondop> Opaque y'" "g \<in> CF" by cases auto
  with ap_cf.prems `opaque f = y1`
  have "opaque f = opaque g" "CF_head f \<leftrightarrow> CF_head g" by auto
  with ap_cf.IH `g \<in> CF` have "f \<cong> g" by simp
  with ap_cf.prems y_split `x = y'` show ?case by (auto intro: itrm_cong.intros ap_cong)
qed

lemma cf_unlift:
  assumes "x \<in> CF"
    shows "CF_head x \<leftrightarrow> unlift x"
using assms proof (induction set: CF)
  case (pure_cf x)
  show ?case by simp
next
  case (ap_cf f x)
  let ?n = "iorder f + 1"
  have "unlift (f \<diamondop> Opaque x) = wrap_abs (unlift' ?n f 1 \<degree> Var 0) ?n"
    unfolding unlift_ap by simp
  also have "... = wrap_abs (Abs (unlift' ?n f 1 \<degree> Var 0)) (iorder f)"
    using wrap_abs_inside by simp
  also have "... \<leftrightarrow> unlift f" proof -
    have "\<not> free (unlift' ?n f 1) 0" using free_unlift by fastforce
    hence "Abs (unlift' ?n f 1 \<degree> Var 0) \<rightarrow>\<^sub>\<eta> (unlift' ?n f 1)[Var 0/0]" ..
    also have "... = unlift' (iorder f) f 0"
      using unlift_subst by (metis One_nat_def Suc_eq_plus1 le0)
    finally show ?thesis
      by (simp add: r_into_rtranclp wrap_abs_equiv red_into_equiv)
  qed
  finally show ?case
    using CF_head.simps ap_cf.IH by (auto intro: term_sym term_trans)
qed

lemma cf_similarD:
  assumes in_cf: "x \<in> CF" "y \<in> CF"
      and similar: "x \<cong> y"
    shows "CF_head x \<leftrightarrow> CF_head y \<and> opaque x = opaque y"
using assms
by (blast intro!: similar_equiv opaque_equiv cf_unlift unlift_equiv intro: term_trans term_sym)

text \<open>Equivalent idiomatic terms in canonical form are similar. This justifies speaking of a
  normal form.\<close>

lemma cf_unique:
  assumes in_cf: "x \<in> CF" "y \<in> CF"
      and equiv: "x \<simeq> y"
    shows "x \<cong> y"
using in_cf proof (rule cf_similarI)
  from equiv show "opaque x = opaque y" by (rule opaque_equiv)
next
  from equiv have "unlift x \<leftrightarrow> unlift y" by (rule unlift_equiv)
  thus "CF_head x \<leftrightarrow> CF_head y"
    using cf_unlift[OF in_cf(1)] cf_unlift[OF in_cf(2)]
    by (auto intro: term_sym term_trans)
qed

subsubsection \<open>Normalization of idiomatic terms\<close>

fun rsize :: "'a itrm \<Rightarrow> nat"
where
    "rsize (x \<diamondop> y) = size y"
  | "rsize _ = 0"

function (sequential) normalize_pure_cf :: "'a itrm \<Rightarrow> 'a itrm"
where
    "normalize_pure_cf (Pure g \<diamondop> (f \<diamondop> x)) = normalize_pure_cf (Pure (\<B> \<degree> g) \<diamondop> f) \<diamondop> x"
  | "normalize_pure_cf (Pure f \<diamondop> Pure x) = Pure (f \<degree> x)"
  | "normalize_pure_cf x = x"
by pat_completeness auto
termination by (relation "measure rsize") auto

fun normalize_cf_pure :: "'a itrm \<Rightarrow> 'a itrm"
where
    "normalize_cf_pure (f \<diamondop> Pure x) = normalize_pure_cf (Pure (\<T> \<degree> x) \<diamondop> f)"
  | "normalize_cf_pure x = x"

function (sequential) normalize_cf_cf :: "'a itrm \<Rightarrow> 'a itrm"
where
    "normalize_cf_cf (g \<diamondop> (f \<diamondop> x)) = normalize_cf_cf (normalize_pure_cf (Pure \<B> \<diamondop> g) \<diamondop> f) \<diamondop> x"
  | "normalize_cf_cf x = normalize_cf_pure x"
by pat_completeness auto
termination by (relation "measure rsize") auto

fun normalize :: "'a itrm \<Rightarrow> 'a itrm"
where
    "normalize (Pure x) = Pure x"
  | "normalize (Opaque x) = Pure \<I> \<diamondop> Opaque x"
  | "normalize (x \<diamondop> y)  = normalize_cf_cf (normalize x \<diamondop> normalize y)"


lemma pure_cf_in_cf:
  assumes "x \<in> CF"
    shows "normalize_pure_cf (Pure f \<diamondop> x) \<in> CF"
using assms
by (induction arbitrary: f rule: CF.induct) auto

lemma pure_cf_equiv: "normalize_pure_cf x \<simeq> x"
proof (induction rule: normalize_pure_cf.induct)
  case (1 g f x)
  have "normalize_pure_cf (Pure g \<diamondop> (f \<diamondop> x)) \<simeq> normalize_pure_cf (Pure (\<B> \<degree> g) \<diamondop> f) \<diamondop> x" by simp
  also from "1.IH" have "... \<simeq> Pure (\<B> \<degree> g) \<diamondop> f \<diamondop> x" by (rule ap_congL)
  also have "... \<simeq> Pure \<B> \<diamondop> Pure g \<diamondop> f \<diamondop> x" by (blast intro: itrm_hom'[symmetric] ap_congL)
  also have "... \<simeq> Pure g \<diamondop> (f \<diamondop> x)" by (rule itrm_comp'[symmetric])
  finally show ?case .
next
  case (2 f x)
  have "normalize_pure_cf (Pure f \<diamondop> Pure x) \<simeq> Pure (f \<degree> x)" by simp
  also have "... \<simeq> Pure f \<diamondop> Pure x" by (rule itrm_hom'[symmetric])
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
  also have "... \<simeq> f \<diamondop> Pure x" by (rule itrm_xchng'[symmetric])
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
  also from "1.IH" have "... \<simeq> normalize_pure_cf (Pure \<B> \<diamondop> g) \<diamondop> f \<diamondop> x" by (rule ap_congL)
  also have "... \<simeq> Pure \<B> \<diamondop> g \<diamondop> f \<diamondop> x" by (blast intro: pure_cf_equiv ap_congL)
  also have "... \<simeq> g \<diamondop> (f \<diamondop> x)" by (rule itrm_comp'[symmetric])
  finally show ?case .
qed (auto simp del: normalize_cf_pure.simps intro: cf_pure_equiv)

lemma normalize_in_cf: "normalize x \<in> CF"
by (induction x rule: normalize.induct) (auto intro: cf_cf_in_cf)

lemma normalize_equiv: "normalize x \<simeq> x"
proof (induction rule: normalize.induct)
  case (2 x)
  have "normalize (Opaque x) \<simeq> Pure \<I> \<diamondop> Opaque x" by simp
  also have "... \<simeq> Opaque x" by (rule itrm_id'[symmetric])
  finally show ?case .
next
  case (3 x y)
  have "normalize (x \<diamondop> y) \<simeq> normalize_cf_cf (normalize x \<diamondop> normalize y)" by simp
  also have "... \<simeq> normalize x \<diamondop> normalize y" by (rule cf_cf_equiv)
  also from "3.IH" have "... \<simeq> x \<diamondop> normalize y" by (blast intro: ap_congL)
  also from "3.IH" have "... \<simeq> x \<diamondop> y" by (blast intro: ap_congR)
  finally show ?case .
qed auto

lemma normal_form: obtains n where "n \<simeq> x" and "n \<in> CF"
using normalize_equiv normalize_in_cf ..


subsubsection \<open>Proving lifted equations\<close>

theorem nf_lifting:
  assumes opaque: "opaque x = opaque y"
      and base_eq: "unlift x \<leftrightarrow> unlift y"
    shows "x \<simeq> y"
proof -
  obtain n where "n \<simeq> x" and "n \<in> CF" by (rule normal_form)
  hence n_head: "CF_head n \<leftrightarrow> unlift x"
    using cf_unlift unlift_equiv by (blast intro: term_trans)
  from `n \<simeq> x` have n_opaque: "opaque n = opaque x"
    by (rule opaque_equiv)
  obtain n' where "n' \<simeq> y" and "n' \<in> CF" by (rule normal_form)
  hence n'_head: "CF_head n' \<leftrightarrow> unlift y"
    using cf_unlift unlift_equiv by (blast intro: term_trans)
  from `n' \<simeq> y` have n'_opaque: "opaque n' = opaque y"
    by (rule opaque_equiv)
  from n_head n'_head base_eq have "CF_head n \<leftrightarrow> CF_head n'"
    by (blast intro: term_sym term_trans)
  moreover from n_opaque n'_opaque opaque list.rel_conversep[of "op \<leftrightarrow>"]
  have "opaque n = opaque n'"
    by(auto simp add: fun_eq_iff intro: term_trans)
  moreover note `n \<in> CF` `n' \<in> CF`
  ultimately have "n \<cong> n'" by (blast intro: cf_similarI)
  hence "n \<simeq> n'" by (rule similar_equiv)
  with `n \<simeq> x` `n' \<simeq> y` show "x \<simeq> y" by (blast intro: itrm_sym itrm_trans)
qed


subsubsection \<open>Lifting with bracket abstraction\<close>

text \<open>Idioms which satisfy additional equations\<close>

locale itrm_ext =
  fixes E :: "'a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool"
  assumes idiom_ext: "pre_equiv \<le> E"
begin

abbreviation itrm_ext_equiv :: "'a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool" (infixl "\<simeq>\<^sup>+" 50)
where "x \<simeq>\<^sup>+ y \<equiv> itrm_cong E x y"

lemma pre_equiv_into_ext: "pre_equiv x y \<Longrightarrow> x \<simeq>\<^sup>+ y"
using idiom_ext by (blast intro: base_cong)

lemmas itrm_ext_id = itrm_id[THEN pre_equiv_into_ext]
lemmas itrm_ext_comp = itrm_comp[THEN pre_equiv_into_ext]
lemmas itrm_ext_hom = itrm_hom[THEN pre_equiv_into_ext]
lemmas itrm_ext_xchng = itrm_xchng[THEN pre_equiv_into_ext]

lemma equiv_into_ext: "x \<simeq> y \<Longrightarrow> x \<simeq>\<^sup>+ y"
by (induction pred: itrm_cong) (auto intro: itrm_cong.intros idiom_ext[THEN predicate2D])

end


text \<open>General notion of bracket abstraction for lambda terms\<close>

definition foldr_option :: "('a \<Rightarrow> 'b \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b option"
where "foldr_option f xs e = foldr (\<lambda>a b. Option.bind b (f a)) xs (Some e)"

lemma bind_eq_SomeE:
  assumes "Option.bind x f = Some y"
  obtains x' where "x = Some x'" and "f x' = Some y"
using assms by (auto iff: bind_eq_Some_conv)

lemma foldr_option_Nil[simp]: "foldr_option f [] e = Some e"
unfolding foldr_option_def by simp

lemma foldr_option_Cons:
  assumes "foldr_option f (x#xs) e = Some y"
  obtains y' where "foldr_option f xs e = Some y'" and "f x y' = Some y"
using assms unfolding foldr_option_def by (auto elim: bind_eq_SomeE)

definition frees :: "dB \<Rightarrow> nat set"
where [simp]: "frees t = {i. free t i}"

definition term_dist :: "nat list \<Rightarrow> dB \<Rightarrow> dB"
where [simp]: "term_dist = fold (\<lambda>i t. t \<degree> Var i)"

definition strip_context :: "nat \<Rightarrow> dB \<Rightarrow> dB"
where "strip_context n t = (THE t'. t = liftn n t 0)"

lemma dist_perm_eta:
  assumes vars_perm: "vs <~~> [0..<n]"
      and not_free: "\<forall>i\<in>frees s. n \<le> i" "\<forall>i\<in>frees t. n \<le> i"
      and perm_equiv: "wrap_abs (term_dist vs s) n \<leftrightarrow> wrap_abs (term_dist vs t) n"
    shows "strip_context n s \<leftrightarrow> strip_context n t"
(*
  TODO:
  - find permutation vs' such that rev vs' o vs = rev [0..<n]
  - show "term_dist vs' (wrap_abs (term_dist vs (liftn n s 0)) n) \<leftrightarrow> term_dist (rev [0..<n]) s"
    by repeated beta-reduction, likewise for t
  - show "wrap_abs (term_dist (rev [0..<n]) s) n \<leftrightarrow> strip_context n s" by repeated eta-reduction
    using not_free, likewise for t
  - compose everything with theorems like liftn_equiv, wrap_abs_equiv, etc.
*)
oops

locale bracket_abstraction =
  fixes term_bracket :: "nat \<Rightarrow> dB \<Rightarrow> dB option"
  assumes bracket_app: "term_bracket i s = Some s' \<Longrightarrow> s' \<degree> Var i \<leftrightarrow> s"
  assumes bracket_frees: "term_bracket i s = Some s' \<Longrightarrow> frees s' = frees s - {i}"
begin

definition term_brackets :: "nat list \<Rightarrow> dB \<Rightarrow> dB option"
where [simp]: "term_brackets = foldr_option term_bracket"

lemma bracket_dist:
  assumes "term_brackets vs t = Some t'"
    shows "term_dist vs t' \<leftrightarrow> t"
proof -
  from assms have "\<forall>t''. t' \<leftrightarrow> t'' \<longrightarrow> term_dist vs t'' \<leftrightarrow> t"
  proof (induction vs arbitrary: t')
    case Nil then show ?case by (simp add: term_sym)
  next
    case (Cons v vs)
    from Cons.prems obtain u where
        inner: "term_brackets vs t = Some u" and
        step: "term_bracket v u = Some t'"
      by (auto elim: foldr_option_Cons)
    from step have red1: "t' \<degree> Var v \<leftrightarrow> u" by (rule bracket_app)
    show ?case proof rule+
      fix t'' assume "t' \<leftrightarrow> t''"
      with red1 have red: "t'' \<degree> Var v \<leftrightarrow> u"
        using equiv_appL term_sym term_trans by blast
      have "term_dist (v # vs) t'' = term_dist vs (t'' \<degree> Var v)" by simp
      also have "... \<leftrightarrow> t" using Cons.IH[OF inner] red[symmetric] by blast
      finally show "term_dist (v # vs) t'' \<leftrightarrow> t" .
    qed
  qed
  then show ?thesis by blast
qed

end


text \<open>Bracket abstraction for idiomatic terms\<close>

locale itrm_abstraction = bracket_abstraction + itrm_ext E for E :: "nat itrm \<Rightarrow> _" +
  fixes itrm_bracket :: "nat \<Rightarrow> nat itrm \<Rightarrow> nat itrm option"
  assumes itrm_bracket_ap: "itrm_bracket i x = Some x' \<Longrightarrow> x' \<diamondop> Opaque i \<simeq>\<^sup>+ x"
  assumes itrm_bracket_opaque: "itrm_bracket i x = Some x' \<Longrightarrow> set (opaque x') = set (opaque x) - {i}"
  (* FIXME *)
  assumes bracket_compat:
    "set (opaque x) \<subseteq> set vs \<Longrightarrow>
      rel_option (op \<leftrightarrow>)
        (term_brackets vs (unlift' (iorder x) x 0))
        (map_option unlift (foldr_option itrm_bracket vs x))"
begin

definition "itrm_brackets = foldr_option itrm_bracket"

lemma itrm_brackets_Cons:
  assumes "itrm_brackets (v#vs) x = Some x'"
  obtains y' where "itrm_brackets vs x = Some y'" and "itrm_bracket v y' = Some x'"
using assms unfolding itrm_brackets_def by (elim foldr_option_Cons)

definition "itrm_bracket_norm = fold (\<lambda>i y. y \<diamondop> Opaque i)"

lemma bracket_nf: "itrm_brackets vs x = Some x' \<Longrightarrow> itrm_bracket_norm vs x' \<simeq>\<^sup>+ x"
proof -
  assume defined: "itrm_brackets vs x = Some x'"
  {
    def x'' == x'
    assume "x' \<simeq>\<^sup>+ x''"
    with defined have "itrm_bracket_norm vs x'' \<simeq>\<^sup>+ x"
      unfolding itrm_bracket_norm_def
      proof (induction vs arbitrary: x' x'')
        case Nil then show ?case unfolding itrm_brackets_def by (simp add: itrm_sym)
      next
        case (Cons v vs)
        from Cons.prems(1) obtain y'
          where *: "itrm_brackets vs x = Some y'" and "itrm_bracket v y' = Some x'"
          by (rule itrm_brackets_Cons)
        then have "x' \<diamondop> Opaque v \<simeq>\<^sup>+ y'" by (elim itrm_bracket_ap)
        then have "x'' \<diamondop> Opaque v \<simeq>\<^sup>+ y'" using Cons.prems(2) by (blast intro: itrm_cong.intros)
        with * have "fold (\<lambda>i y. y \<diamondop> Opaque i) vs (x'' \<diamondop> Opaque v) \<simeq>\<^sup>+ x" using Cons.IH
          by (auto intro: itrm_sym)
        then show ?case by simp
     qed
  }
  then show ?thesis using itrm_refl .
qed

lemma bracket_nf_cong: "x \<simeq>\<^sup>+ y \<Longrightarrow> itrm_bracket_norm vs x \<simeq>\<^sup>+ itrm_bracket_norm vs y"
unfolding itrm_bracket_norm_def
by (induction vs arbitrary: x y) (auto intro: ap_congL)

lemma bracket_complete:
  assumes complete: "set (opaque x) \<subseteq> set vs"
      and defined: "itrm_brackets vs x = Some x'"
    shows "opaque x' = []"
proof -
  from defined have "set (opaque x') = set (opaque x) - set vs"
    proof (induction vs arbitrary: x')
      case Nil then show ?case unfolding itrm_brackets_def by simp
    next
      case (Cons v vs) then show ?case
        by (auto elim: itrm_brackets_Cons dest!: itrm_bracket_opaque)
    qed
  with complete have "set (opaque x') = {}" by simp
  then show ?thesis by simp
qed

lemma bracket_complete_unlift:
  assumes complete: "set (opaque x) \<subseteq> set vs"
      and defined: "itrm_brackets vs x = Some x'"
    shows "x' \<simeq>\<^sup>+ Pure (unlift x')"
proof (rule equiv_into_ext)
  from assms have "opaque x' = []" by (rule bracket_complete)
  then show "x' \<simeq> Pure (unlift x')" by (rule unlift_all_pure)
qed

theorem bracket_lifting:
  assumes complete: "set (opaque x) \<subseteq> set vs" "set (opaque y) \<subseteq> set vs" (*FIXME*)
      and defined: "itrm_brackets vs x = Some x'" "itrm_brackets vs y = Some y'"
      and base_eq: "unlift x \<leftrightarrow> unlift y"
    shows "x \<simeq>\<^sup>+ y"
proof -
  have "x \<simeq>\<^sup>+ itrm_bracket_norm vs x'" using defined(1) by (rule bracket_nf[symmetric])
  also have "... \<simeq>\<^sup>+ itrm_bracket_norm vs (Pure (unlift x'))"
    using complete(1) defined(1)
    by (blast intro: bracket_nf_cong bracket_complete_unlift)
  (*TODO*)
oops

end

end
