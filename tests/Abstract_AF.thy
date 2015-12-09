theory Abstract_AF
imports "../src/Applicative_Functor"
begin

section {* An abstract applicative functor *}

typedef 'a af = "UNIV :: 'a set" ..

abbreviation "af_pure \<equiv> Abs_af"
definition "af_ap f x = Abs_af ((Rep_af f) (Rep_af x))"

adhoc_overloading pure Abs_af
adhoc_overloading ap af_ap

lemma af_identity: "af_pure id \<diamond> x = x"
unfolding af_ap_def
by (simp add: Abs_af_inverse Rep_af_inverse)

lemma af_homomorphism: "af_pure f \<diamond> af_pure x = af_pure (f x)"
unfolding af_ap_def
by (simp add: Abs_af_inverse Rep_af_inverse)

lemma af_composition: "af_pure comp \<diamond> g \<diamond> f \<diamond> x = g \<diamond> (f \<diamond> x)"
unfolding af_ap_def
by (simp add: Abs_af_inverse Rep_af_inverse)

lemma af_interchange: "f \<diamond> af_pure x = af_pure (\<lambda>g. g x) \<diamond> f"
unfolding af_ap_def
by (simp add: Abs_af_inverse Rep_af_inverse)

hide_const Abs_af Rep_af
hide_fact af_ap_def

applicative af
for
  pure: af_pure
  ap: af_ap
using af_identity af_composition af_homomorphism af_interchange
unfolding id_def comp_def[abs_def]
.

end
