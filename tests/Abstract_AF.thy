theory Abstract_AF
imports Main
begin

section {* An abstract applicative functor *}

typedef 'a af = "UNIV :: 'a set" ..

definition pure
  where "pure x = Abs_af x"

definition ap (infixl "\<diamond>" 60)
  where "f \<diamond> x = Abs_af ((Rep_af f) (Rep_af x))"

lemma af_identity: "pure id \<diamond> x = x"
unfolding pure_def ap_def
by (simp add: Abs_af_inverse Rep_af_inverse)

lemma af_homomorphism: "pure f \<diamond> pure x = pure (f x)"
unfolding pure_def ap_def
by (simp add: Abs_af_inverse Rep_af_inverse)

lemma af_composition: "pure comp \<diamond> g \<diamond> f \<diamond> x = g \<diamond> (f \<diamond> x)"
unfolding pure_def ap_def
by (simp add: Abs_af_inverse Rep_af_inverse)

lemma af_interchange: "f \<diamond> pure x = pure (\<lambda>g. g x) \<diamond> f"
unfolding pure_def ap_def
by (simp add: Abs_af_inverse Rep_af_inverse)

hide_const Abs_af Rep_af
hide_fact pure_def ap_def

end
