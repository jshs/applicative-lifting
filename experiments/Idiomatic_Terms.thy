theory Idiomatic_Terms
imports Lambda Eta  (* in HOL-Proofs-Lambda *)
begin

section {* Operations on idiomatic terms *}

subsection {* Extensions to lambda terms *}

subsubsection {* Combined beta- and eta-reduction *}

abbreviation beta_eta :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infixl "\<rightarrow>\<^sub>\<beta>\<^sub>\<eta>" 50)
where
  "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta> t \<equiv> s \<rightarrow>\<^sub>\<beta> t \<or> s \<rightarrow>\<^sub>\<eta> t"

abbreviation beta_eta_reds :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infixl "\<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>*" 50)
where
  "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<equiv> (beta_eta)\<^sup>*\<^sup>* s t"

lemma beta_eta_appl: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* s' \<Longrightarrow> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* s' \<degree> t"
by (induction set: rtranclp) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma beta_eta_appr: "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t' \<Longrightarrow> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* s \<degree> t'"
by (induction set: rtranclp) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma beta_eta_abs[intro]: "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t' \<Longrightarrow> Abs t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Abs t'"
by (induction set: rtranclp) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma beta_mono: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t"
by (auto intro: rtranclp_mono[THEN predicate2D])

lemma eta_mono: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t"
by (auto intro: rtranclp_mono[THEN predicate2D])

lemma beta_eta_confluent: "confluent beta_eta"
proof -
  have "beta_eta = sup beta eta" by blast
  with Eta.confluent_beta_eta show ?thesis by simp
qed


subsubsection {* Equivalent terms *}

definition term_equiv :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infixl "\<leftrightarrow>" 50)
where
  "s \<leftrightarrow> t = (\<exists>u. s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u \<and> t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u)"

lemma term_refl[simp,intro]: "t \<leftrightarrow> t"
unfolding term_equiv_def by blast

lemma term_sym[sym]: "(s \<leftrightarrow> t) \<Longrightarrow> (t \<leftrightarrow> s)"
unfolding term_equiv_def by blast

lemma diamond_merge: "diamond P \<Longrightarrow> P x y \<Longrightarrow> P x z \<Longrightarrow> (\<exists>w. P y w \<and> P z w)"
unfolding diamond_def commute_def square_def
by blast

lemma term_trans[trans]: "s \<leftrightarrow> t \<Longrightarrow> t \<leftrightarrow> u \<Longrightarrow> s \<leftrightarrow> u"
proof -
  assume "s \<leftrightarrow> t"
  then obtain x where A: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* x" and B: "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* x"
    unfolding term_equiv_def by blast
  assume "t \<leftrightarrow> u"
  then obtain y where B': "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* y" and C: "u \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* y"
    unfolding term_equiv_def by blast
  from B B' obtain z where D: "x \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* z" "y \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* z"
    using diamond_merge[OF beta_eta_confluent] by blast
  from A C D show "s \<leftrightarrow> u"
    unfolding term_equiv_def by (blast intro: rtranclp_trans)
qed

lemma term_appl: "s \<leftrightarrow> s' \<Longrightarrow> s \<degree> t \<leftrightarrow> s' \<degree> t"
unfolding term_equiv_def
by (blast intro: beta_eta_appl)

lemma term_appr: "t \<leftrightarrow> t' \<Longrightarrow> s \<degree> t \<leftrightarrow> s \<degree> t'"
unfolding term_equiv_def
by (blast intro: beta_eta_appr)

lemma term_abs[intro]: "t \<leftrightarrow> t' \<Longrightarrow> Abs t \<leftrightarrow> Abs t'"
unfolding term_equiv_def
by blast

lemma beta_eta_red: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> s \<leftrightarrow> t"
unfolding term_equiv_def
by blast


subsubsection {* Some combinators *}

abbreviation "\<I> \<equiv> Abs (Var 0)"
abbreviation "\<B> \<equiv> Abs (Abs (Abs (Var 2 \<degree> (Var 1 \<degree> Var 0))))"
abbreviation "\<A>' \<equiv> Abs (Abs (Var 0 \<degree> Var 1))" -- {* reverse application *}

lemma I_eval: "\<I> \<degree> x \<rightarrow>\<^sub>\<beta>\<^sup>* x"
proof -
  have "\<I> \<degree> x \<rightarrow>\<^sub>\<beta> x" by (metis beta.beta subst_eq)
  thus ?thesis by simp
qed

lemmas I_equiv = I_eval[THEN beta_mono, THEN beta_eta_red]

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

lemmas B_equiv = B_eval[THEN beta_mono, THEN beta_eta_red]

lemma A'_eval: "\<A>' \<degree> x \<degree> f \<rightarrow>\<^sub>\<beta>\<^sup>* f \<degree> x"
proof -
  have "\<A>' \<degree> x \<degree> f \<rightarrow>\<^sub>\<beta> Abs (Var 0 \<degree> Var 1)[x/0] \<degree> f" by clarify
  also have "... = Abs (Var 0 \<degree> lift x 0) \<degree> f" by simp
  also have "... \<rightarrow>\<^sub>\<beta>\<^sup>* (Var 0 \<degree> lift x 0)[f/0]" by (rule r_into_rtranclp) clarify
  also have "... \<rightarrow>\<^sub>\<beta>\<^sup>* f \<degree> x" by simp
  finally show ?thesis .
qed

lemmas A'_equiv = A'_eval[THEN beta_mono, THEN beta_eta_red]


subsubsection {* Auxiliary lemmas *}

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


subsection {* Idiomatic terms *}

subsubsection {* Basic definitions *}

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
  | itrm_apl: "f \<simeq> f' \<Longrightarrow> f \<diamond> x \<simeq> f' \<diamond> x"
  | itrm_apr: "x \<simeq> x' \<Longrightarrow> f \<diamond> x \<simeq> f \<diamond> x'"
  | itrm_refl[simp,intro]: "x \<simeq> x"
  | itrm_sym[sym]: "x \<simeq> y \<Longrightarrow> y \<simeq> x"
  | itrm_trans[trans]: "x \<simeq> y \<Longrightarrow> y \<simeq> z \<Longrightarrow> x \<simeq> z"


subsubsection {* Structural analysis *}

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
  case (itrm_apl f f' x)
  have "unlift' n (f \<diamond> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  moreover have "unlift' n (f' \<diamond> x) i = unlift' n f' (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  ultimately show ?case using itrm_apl.IH term_appl by auto
next
  case (itrm_apr x x' f)
  from itrm_apr.hyps have order_eq: "iorder x = iorder x'"
    using opaque_equiv by auto
  have "unlift' n (f \<diamond> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"
    unfolding unlift_ap by simp
  moreover have "unlift' n (f \<diamond> x') i = unlift' n f (i + iorder x) \<degree> unlift' n x' i"
    unfolding unlift_ap order_eq by simp
  ultimately show ?case using itrm_apr.IH term_appr by auto
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


primrec leaves :: "itrm \<Rightarrow> nat"
where
    "leaves (Pure _) = 1"
  | "leaves (Term _)  = 1"
  | "leaves (f \<diamond> x)  = leaves f + leaves x"

primrec rleaves :: "itrm \<Rightarrow> nat"
where
    "rleaves (Pure _) = 0"
  | "rleaves (Term _)  = 1"
  | "rleaves (f \<diamond> x)  = rleaves f + leaves x"

lemma min_leaves: "0 < leaves x"
by induction auto


subsection {* Normal form *}

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
      by (simp add: r_into_rtranclp wrap_abs_equiv beta_eta_red)
  qed
  finally show ?case
    using NF_head.simps ap_nf.IH term_sym term_trans by presburger
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
    by presburger
qed


subsection {* Normalization of idiomatic terms *}

function (sequential) normalize_pure_nf :: "itrm \<Rightarrow> itrm"
where
    "normalize_pure_nf (Pure g \<diamond> (f \<diamond> x)) = normalize_pure_nf (Pure (\<B> \<degree> g) \<diamond> f) \<diamond> x"
  | "normalize_pure_nf (Pure f \<diamond> Pure x) = Pure (f \<degree> x)"
  | "normalize_pure_nf x = x"
by pat_completeness auto
termination by (relation "measure (\<lambda>t.
    (case t of
        Pure f \<diamond> x \<Rightarrow> size x
      | _ \<Rightarrow> 0))") auto

lemma pure_nf_rleaves: "rleaves (normalize_pure_nf (Pure f \<diamond> x)) \<le> rleaves x"
by (induct "Pure f \<diamond> x" arbitrary: f x rule: normalize_pure_nf.induct) auto

fun normalize_nf_pure :: "itrm \<Rightarrow> itrm"
where
    "normalize_nf_pure (f \<diamond> Pure x) = normalize_pure_nf (Pure (\<A>' \<degree> x) \<diamond> f)"
  | "normalize_nf_pure x = x"

function (sequential) normalize_nf_nf :: "itrm \<Rightarrow> itrm"
where
    "normalize_nf_nf (g \<diamond> (f \<diamond> x)) = normalize_nf_nf (normalize_pure_nf (Pure \<B> \<diamond> g) \<diamond> f) \<diamond> x"
  | "normalize_nf_nf x = normalize_nf_pure x"
by pat_completeness auto
termination proof
  fix g f x
  have "rleaves (normalize_pure_nf (Pure \<B> \<diamond> g)) \<le> rleaves g" using pure_nf_rleaves .
  also have "rleaves g < rleaves g + leaves x" using min_leaves by simp
  finally show "(normalize_pure_nf (Pure \<B> \<diamond> g) \<diamond> f, g \<diamond> (f \<diamond> x)) \<in> measure rleaves" by simp
qed simp

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

lemma nf_pure_in_nf:
  assumes "f \<in> NF"
    shows "normalize_nf_pure (f \<diamond> Pure x) \<in> NF"
using assms
by (auto intro: pure_nf_in_nf)

lemma nf_nf_in_nf:
  assumes "x \<in> NF" and "f \<in> NF"
    shows "normalize_nf_nf (f \<diamond> x) \<in> NF"
using assms
by (induction arbitrary: f rule: NF.induct) (auto intro: pure_nf_in_nf)

lemma normalized: "normalize x \<in> NF"
by (induction x rule: normalize.induct) (auto intro: nf_nf_in_nf)

(* TODO normalize x \<simeq> x *)


end
