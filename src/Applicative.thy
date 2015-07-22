theory Applicative
imports Fun
begin

lemma comp_def_ext:
  "comp = (\<lambda>g f x. g (f x))"
by rule+ simp

lemma id_unfold: "id \<equiv> \<lambda>x. x"
by (unfold id_def)

lemma comp_unfold: "comp \<equiv> (\<lambda>g f x. g (f x))"
by (unfold comp_def_ext)

ML_file "applicative.ML"

method_setup lifting_nf = {* Scan.succeed (fn ctxt =>
  SIMPLE_METHOD' (Applicative.lifting_nf_tac ctxt)) *}

end
