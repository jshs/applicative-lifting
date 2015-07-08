theory Idiomatic_Terms
imports Main
begin

section {* Operations on idiomatic terms *}

subsection {* Lambda terms *}

datatype 'a trm =
    Var 'a | BVar nat
  | Abs "'a trm"
  | App "'a trm" "'a trm" (infixl "$" 200)

abbreviation "\<B> \<equiv> Abs (Abs (Abs (BVar 2 $ (BVar 1 $ BVar 0))))"
abbreviation "\<B>\<^sub>1 f \<equiv> Abs (Abs (f $ (BVar 1 $ BVar 0)))"


subsection {* Idiomatic terms *}

datatype 'a itrm =
    Imp "'a trm" | Pure "'a trm"
  | IAp "'a itrm" "'a itrm" (infixl "\<diamond>" 150)

primrec leaves :: "'a itrm \<Rightarrow> nat"
where
    "leaves (Pure _) = 1"
  | "leaves (Imp _)  = 1"
  | "leaves (f \<diamond> x)  = leaves f + leaves x"

primrec rleaves :: "'a itrm \<Rightarrow> nat"
where
    "rleaves (Pure _) = 0"
  | "rleaves (Imp _)  = 1"
  | "rleaves (f \<diamond> x)  = rleaves f + leaves x"

lemma min_leaves: "0 < leaves x"
by induction auto


subsection {* Normal form *}

inductive_set NF :: "'a itrm set"
where
    pure_nf[intro]: "Pure x \<in> NF"
  | ap_nf[intro]:   "f \<in> NF \<Longrightarrow> f \<diamond> Imp x \<in> NF"

lemma ap_nfD1[dest]: "f \<diamond> x \<in> NF \<Longrightarrow> f \<in> NF"
by (rule NF.cases) auto

lemma ap_nfD2[dest]: "f \<diamond> x \<in> NF \<Longrightarrow> \<exists>x'. x = Imp x'"
by (rule NF.cases) auto

lemma imp_not_nf[dest]: "Imp x \<in> NF \<Longrightarrow> False"
by (rule NF.cases) auto


subsection {* Normalization of idiomatic terms *}

function (sequential) normalize_pure_nf :: "'a itrm \<Rightarrow> 'a itrm"
where
    "normalize_pure_nf (Pure g \<diamond> (f \<diamond> x)) = normalize_pure_nf (Pure (\<B>\<^sub>1 g) \<diamond> f) \<diamond> x"
  | "normalize_pure_nf (Pure f \<diamond> Pure x) = Pure (f $ x)"
  | "normalize_pure_nf x = x"
by pat_completeness auto
termination by (relation "measure (\<lambda>t.
    (case t of
        Pure f \<diamond> x \<Rightarrow> size x
      | _ \<Rightarrow> 0))") auto

lemma pure_nf_rleaves: "rleaves (normalize_pure_nf (Pure f \<diamond> x)) \<le> rleaves x"
by (induct "Pure f \<diamond> x" arbitrary: f x rule: normalize_pure_nf.induct) auto

fun normalize_nf_pure :: "'a itrm \<Rightarrow> 'a itrm"
where
    "normalize_nf_pure (f \<diamond> Pure x) = normalize_pure_nf (Pure (Abs (BVar 0 $ x)) \<diamond> f)"
  | "normalize_nf_pure x = x"

function (sequential) normalize_nf_nf :: "'a itrm \<Rightarrow> 'a itrm"
where
    "normalize_nf_nf (g \<diamond> (f \<diamond> x)) = normalize_nf_nf (normalize_pure_nf (Pure \<B> \<diamond> g) \<diamond> f) \<diamond> x"
  | "normalize_nf_nf x = normalize_nf_pure x"
by pat_completeness auto
termination proof
  fix g f x :: "'a itrm"
  have "rleaves (normalize_pure_nf (Pure \<B> \<diamond> g)) \<le> rleaves g" using pure_nf_rleaves .
  also have "rleaves g < rleaves g + leaves x" using min_leaves by simp
  finally show "(normalize_pure_nf (Pure \<B> \<diamond> g) \<diamond> f, g \<diamond> (f \<diamond> x)) \<in> measure rleaves" by simp
qed simp

fun normalize :: "'a itrm \<Rightarrow> 'a itrm"
where
    "normalize (Pure x) = Pure x"
  | "normalize (Imp x)  = Pure (Abs (BVar 0)) \<diamond> Imp x"
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
by (induction arbitrary: f rule: NF.induct) (auto intro: pure_nf_in_nf nf_pure_in_nf)

lemma normalized: "normalize x \<in> NF"
by (induction x rule: normalize.induct) (auto intro: nf_nf_in_nf)


end