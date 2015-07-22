theory Idiomatic_Terms
imports Beta_Eta
begin

section \<open>Operations on idiomatic terms\<close>

subsection \<open>Extensions to lambda terms\<close>

subsubsection \<open>Some combinators\<close>

abbreviation "\<I> \<equiv> Abs (Var 0)"
abbreviation "\<B> \<equiv> Abs (Abs (Abs (Var 2 \<degree> (Var 1 \<degree> Var 0))))"
abbreviation "\<A>' \<equiv> Abs (Abs (Var 0 \<degree> Var 1))" -- \<open>reverse application\<close>

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

lemma A'_eval: "\<A>' \<degree> x \<degree> f \<rightarrow>\<^sub>\<beta>\<^sup>* f \<degree> x"
proof -
  have "\<A>' \<degree> x \<degree> f \<rightarrow>\<^sub>\<beta> Abs (Var 0 \<degree> Var 1)[x/0] \<degree> f" by clarify
  also have "... = Abs (Var 0 \<degree> lift x 0) \<degree> f" by simp
  also have "... \<rightarrow>\<^sub>\<beta>\<^sup>* (Var 0 \<degree> lift x 0)[f/0]" by (rule r_into_rtranclp) clarify
  also have "... \<rightarrow>\<^sub>\<beta>\<^sup>* f \<degree> x" by simp
  finally show ?thesis .
qed

lemmas A'_equiv = A'_eval[THEN beta_into_beta_eta, THEN red_into_equiv]


subsubsection \<open>Auxiliary lemmas\<close>

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


subsection \<open>Idiomatic terms\<close>

subsubsection \<open>Basic definitions\<close>

datatype itrm =
    Term dB | Pure dB
  | IAp itrm itrm (infixl "\<diamond>" 150)

inductive itrm_cong :: "itrm \<Rightarrow> itrm \<Rightarrow> bool" (infixl "\<cong>" 50)
where
    "t \<leftrightarrow> t' \<Longrightarrow> Term t \<cong> Term t'"
  | "t \<leftrightarrow> t' \<Longrightarrow> Pure t \<cong> Pure t'"
  | "f \<cong> f' \<Longrightarrow> f \<diamond> x \<cong> f' \<diamond> x"
  | "x \<cong> x' \<Longrightarrow> f \<diamond> x \<cong> f \<diamond> x'"

inductive itrm_equiv :: "itrm \<Rightarrow> itrm \<Rightarrow> bool" (infixl "\<simeq>" 50)
where
    itrm_id: "x \<simeq> Pure \<I> \<diamond> x"
  | itrm_comp: "g \<diamond> (f \<diamond> x) \<simeq> Pure \<B> \<diamond> g \<diamond> f \<diamond> x"
  | itrm_hom: "Pure f \<diamond> Pure x \<simeq> Pure (f \<degree> x)"
  | itrm_xchng: "f \<diamond> Pure x \<simeq> Pure (\<A>' \<degree> x) \<diamond> f"
  | itrm_apL: "f \<simeq> f' \<Longrightarrow> f \<diamond> x \<simeq> f' \<diamond> x"
  | itrm_apR: "x \<simeq> x' \<Longrightarrow> f \<diamond> x \<simeq> f \<diamond> x'"
  | itrm_refl[simp,intro]: "x \<simeq> x"
  | itrm_sym[sym]: "x \<simeq> y \<Longrightarrow> y \<simeq> x"
  | itrm_trans[trans]: "x \<simeq> y \<Longrightarrow> y \<simeq> z \<Longrightarrow> x \<simeq> z"


subsubsection \<open>Structural analysis\<close>

primrec opaque :: "itrm \<Rightarrow> dB list"
where
    "opaque (Term x) = [x]"
  | "opaque (Pure _) = []"
  | "opaque (f \<diamond> x) = opaque f @ opaque x"

abbreviation "iorder x \<equiv> length (opaque x)"

primrec vary_terms :: "nat \<Rightarrow> itrm \<Rightarrow> nat \<Rightarrow> dB \<times> nat"
where
    "vary_terms n (Term _) i = (Var i, Suc i)"
  | "vary_terms n (Pure x) i = (liftn n x 0, i)"
  | "vary_terms n (f \<diamond> x)  i = (case vary_terms n x i of (x', i') \<Rightarrow>
        apfst (\<lambda>f. f \<degree> x') (vary_terms n f i'))"

abbreviation "unlift' n x i \<equiv> fst (vary_terms n x i)"

primrec wrap_abs :: "dB \<Rightarrow> nat \<Rightarrow> dB"
where
    "wrap_abs t 0 = t"
  | "wrap_abs t (Suc n) = Abs (wrap_abs t n)"

abbreviation "unlift x \<equiv> wrap_abs (unlift' (iorder x) x 0) (iorder x)"


lemma vary_terms_order: "snd (vary_terms n x i) = i + iorder x"
by (induction arbitrary: i) (auto simp add: case_prod_unfold)

lemma unlift_ap: "unlift' n (f \<diamond> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
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

lemma wrap_abs_inside: "wrap_abs t (Suc n) = wrap_abs (Abs t) n"
by (induction n) auto

lemma wrap_abs_equiv: "s \<leftrightarrow> t \<Longrightarrow> wrap_abs s n \<leftrightarrow> wrap_abs t n"
by (induction n) auto


lemma opaque_equiv:
  assumes "x \<simeq> y"
    shows "opaque x = opaque y"
using assms by induction auto

lemma unlift'_equiv:
  assumes "x \<simeq> y"
    shows "unlift' n x i \<leftrightarrow> unlift' n y i"
using assms proof (induction arbitrary: n i)
  case (itrm_id x)
  show ?case
    unfolding unlift_ap using I_equiv[symmetric] by simp
next
  case (itrm_comp g f x)
  let ?G = "unlift' n g (i + iorder f + iorder x)"
  let ?F = "unlift' n f (i + iorder x)"
  let ?X = "unlift' n x i"
  have "unlift' n (g \<diamond> (f \<diamond> x)) i = ?G \<degree> (?F \<degree> ?X)"
    unfolding unlift_ap by (simp add: add.assoc)
  moreover have "unlift' n (Pure \<B> \<diamond> g \<diamond> f \<diamond> x) i = \<B> \<degree> ?G \<degree> ?F \<degree> ?X"
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
  have "unlift' n (f \<diamond> Pure x) i = ?F \<degree> ?X"
    unfolding unlift_ap by simp
  moreover have "unlift' n (Pure (\<A>' \<degree> x) \<diamond> f) i = \<A>' \<degree> ?X \<degree> ?F"
    unfolding unlift_ap by simp
  moreover have "?F \<degree> ?X \<leftrightarrow> \<A>' \<degree> ?X \<degree> ?F" using A'_equiv[symmetric] .
  ultimately show ?case by simp
next
  case (itrm_apL f f' x)
  have "unlift' n (f \<diamond> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  moreover have "unlift' n (f' \<diamond> x) i = unlift' n f' (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  ultimately show ?case using itrm_apL.IH equiv_appL by auto
next
  case (itrm_apR x x' f)
  from itrm_apR.hyps have order_eq: "iorder x = iorder x'"
    using opaque_equiv by auto
  have "unlift' n (f \<diamond> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  moreover have "unlift' n (f \<diamond> x') i = unlift' n f (i + iorder x) \<degree> unlift' n x' i"
    unfolding unlift_ap order_eq by simp
  ultimately show ?case using itrm_apR.IH equiv_appR by auto
next
  case itrm_refl
  show ?case ..
next
  case itrm_sym
  thus ?case using term_sym by simp
next
  case itrm_trans
  thus ?case using term_trans by blast
qed

lemma unlift_equiv:
  assumes "x \<simeq> y"
    shows "unlift x \<leftrightarrow> unlift y"
using assms unlift'_equiv wrap_abs_equiv opaque_equiv
by simp


subsection \<open>Normal form\<close>

inductive_set NF :: "itrm set"
where
    pure_nf[simp,intro]: "Pure x \<in> NF"
  | ap_nf[intro]:   "f \<in> NF \<Longrightarrow> f \<diamond> Term x \<in> NF"

fun NF_head :: "itrm \<Rightarrow> dB"
where
    "NF_head (Pure x) = x"
  | "NF_head (f \<diamond> x) = NF_head f"

lemma ap_nfD1[dest]: "f \<diamond> x \<in> NF \<Longrightarrow> f \<in> NF"
by (rule NF.cases) auto

lemma ap_nfD2[dest]: "f \<diamond> x \<in> NF \<Longrightarrow> \<exists>x'. x = Term x'"
by (rule NF.cases) auto

lemma term_not_nf[dest]: "Term x \<in> NF \<Longrightarrow> False"
by (rule NF.cases) auto

lemma nf_cong:
  assumes "n \<in> NF" "n' \<in> NF"
      and "opaque n = opaque n'"
      and "NF_head n \<leftrightarrow> NF_head n'"
    shows "n \<cong> n'"
using assms proof (induction arbitrary: n')
  case (pure_nf x)
    then obtain y where "n' = Pure y" by cases auto
    with pure_nf.prems show ?case by (auto intro: itrm_cong.intros)
next
  case (ap_nf f x)
    note `n' \<in> NF` and `opaque (f \<diamond> Term x) = opaque n'`
    then obtain g y where n'_split: "n' = g \<diamond> Term y" "g \<in> NF"
      by cases auto
    with ap_nf.prems have "opaque f = opaque g" "NF_head f \<leftrightarrow> NF_head g" by auto
    with ap_nf.IH `g \<in> NF` have "f \<cong> g" by simp
    with ap_nf.prems n'_split show ?case by (auto intro: itrm_cong.intros)
qed

lemma nf_unlift:
  assumes "n \<in> NF"
    shows "NF_head n \<leftrightarrow> unlift n"
using assms proof (induction set: NF)
  case (pure_nf x)
  show ?case by simp
next
  case (ap_nf f x)
  let ?n = "iorder f + 1"
  have "unlift (f \<diamond> Term x) = wrap_abs (unlift' ?n f 1 \<degree> Var 0) ?n"
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
    using NF_head.simps ap_nf.IH term_sym term_trans by metis
qed

lemma nf_unique:
  assumes in_nf: "n \<in> NF" "n' \<in> NF"
      and equiv: "n \<simeq> n'"
    shows "n \<cong> n'"
using in_nf proof (rule nf_cong)
  from equiv show "opaque n = opaque n'" by (rule opaque_equiv)
  from equiv have "unlift n \<leftrightarrow> unlift n'" by (rule unlift_equiv)
  thus "NF_head n \<leftrightarrow> NF_head n'"
    using nf_unlift[OF in_nf(1)] nf_unlift[OF in_nf(2)]
    using term_sym term_trans
    by metis
qed


subsection \<open>Normalization of idiomatic terms\<close>

fun rsize :: "itrm \<Rightarrow> nat"
where
    "rsize (x \<diamond> y) = size y"
  | "rsize _ = 0"

function (sequential) normalize_pure_nf :: "itrm \<Rightarrow> itrm"
where
    "normalize_pure_nf (Pure g \<diamond> (f \<diamond> x)) = normalize_pure_nf (Pure (\<B> \<degree> g) \<diamond> f) \<diamond> x"
  | "normalize_pure_nf (Pure f \<diamond> Pure x) = Pure (f \<degree> x)"
  | "normalize_pure_nf x = x"
by pat_completeness auto
termination by (relation "measure rsize") auto

fun normalize_nf_pure :: "itrm \<Rightarrow> itrm"
where
    "normalize_nf_pure (f \<diamond> Pure x) = normalize_pure_nf (Pure (\<A>' \<degree> x) \<diamond> f)"
  | "normalize_nf_pure x = x"

function (sequential) normalize_nf_nf :: "itrm \<Rightarrow> itrm"
where
    "normalize_nf_nf (g \<diamond> (f \<diamond> x)) = normalize_nf_nf (normalize_pure_nf (Pure \<B> \<diamond> g) \<diamond> f) \<diamond> x"
  | "normalize_nf_nf x = normalize_nf_pure x"
by pat_completeness auto
termination by (relation "measure rsize") auto

fun normalize :: "itrm \<Rightarrow> itrm"
where
    "normalize (Pure x) = Pure x"
  | "normalize (Term x)  = Pure \<I> \<diamond> Term x"
  | "normalize (x \<diamond> y)  = normalize_nf_nf (normalize x \<diamond> normalize y)"


lemma pure_nf_in_nf:
  assumes "x \<in> NF"
    shows "normalize_pure_nf (Pure f \<diamond> x) \<in> NF"
using assms
by (induction arbitrary: f rule: NF.induct) auto

lemma pure_nf_equiv: "normalize_pure_nf x \<simeq> x"
proof (induction rule: normalize_pure_nf.induct)
  case (1 g f x)
  have "normalize_pure_nf (Pure g \<diamond> (f \<diamond> x)) \<simeq> normalize_pure_nf (Pure (\<B> \<degree> g) \<diamond> f) \<diamond> x" by simp
  also from "1.IH" have "... \<simeq> Pure (\<B> \<degree> g) \<diamond> f \<diamond> x" by (rule itrm_apL)
  also have "... \<simeq> Pure \<B> \<diamond> Pure g \<diamond> f \<diamond> x" by (blast intro: itrm_hom[symmetric] itrm_apL)
  also have "... \<simeq> Pure g \<diamond> (f \<diamond> x)" by (rule itrm_comp[symmetric])
  finally show ?case .
next
  case (2 f x)
  have "normalize_pure_nf (Pure f \<diamond> Pure x) \<simeq> Pure (f \<degree> x)" by simp
  also have "... \<simeq> Pure f \<diamond> Pure x" by (rule itrm_hom[symmetric])
  finally show ?case .
qed auto

lemma nf_pure_in_nf:
  assumes "f \<in> NF"
    shows "normalize_nf_pure (f \<diamond> Pure x) \<in> NF"
using assms
by (auto intro: pure_nf_in_nf)

lemma nf_pure_equiv: "normalize_nf_pure x \<simeq> x"
proof (induction rule: normalize_nf_pure.induct)
  case (1 f x)
  have "normalize_nf_pure (f \<diamond> Pure x) \<simeq> normalize_pure_nf (Pure (\<A>' \<degree> x) \<diamond> f)" by simp
  also have "... \<simeq> Pure (\<A>' \<degree> x) \<diamond> f" by (rule pure_nf_equiv)
  also have "... \<simeq> f \<diamond> Pure x" by (rule itrm_xchng[symmetric])
  finally show ?case .
qed auto

lemma nf_nf_in_nf:
  assumes "x \<in> NF" and "f \<in> NF"
    shows "normalize_nf_nf (f \<diamond> x) \<in> NF"
using assms
by (induction arbitrary: f rule: NF.induct) (auto intro: pure_nf_in_nf)

lemma nf_nf_equiv: "normalize_nf_nf x \<simeq> x"
proof (induction rule: normalize_nf_nf.induct)
  case (1 g f x)
  have "normalize_nf_nf (g \<diamond> (f \<diamond> x)) \<simeq> normalize_nf_nf (normalize_pure_nf (Pure \<B> \<diamond> g) \<diamond> f) \<diamond> x"
    by simp
  also from "1.IH" have "... \<simeq> normalize_pure_nf (Pure \<B> \<diamond> g) \<diamond> f \<diamond> x" by (rule itrm_apL)
  also have "... \<simeq> Pure \<B> \<diamond> g \<diamond> f \<diamond> x" by (blast intro: pure_nf_equiv itrm_apL)
  also have "... \<simeq> g \<diamond> (f \<diamond> x)" by (rule itrm_comp[symmetric])
  finally show ?case .
qed (auto simp del: normalize_nf_pure.simps intro: nf_pure_equiv)

lemma normalize_in_nf: "normalize x \<in> NF"
by (induction x rule: normalize.induct) (auto intro: nf_nf_in_nf)

lemma normalize_equiv: "normalize x \<simeq> x"
proof (induction rule: normalize.induct)
  case (2 x)
  have "normalize (Term x) \<simeq> Pure \<I> \<diamond> Term x" by simp
  also have "... \<simeq> Term x" by (rule itrm_id[symmetric])
  finally show ?case .
next
  case (3 x y)
  have "normalize (x \<diamond> y) \<simeq> normalize_nf_nf (normalize x \<diamond> normalize y)" by simp
  also have "... \<simeq> normalize x \<diamond> normalize y" by (rule nf_nf_equiv)
  also from "3.IH" have "... \<simeq> x \<diamond> normalize y" by (blast intro: itrm_apL)
  also from "3.IH" have "... \<simeq> x \<diamond> y" by (blast intro: itrm_apR)
  finally show ?case .
qed auto

lemma normal_form: obtains n where "n \<simeq> x" and "n \<in> NF"
using normalize_equiv normalize_in_nf ..

end
