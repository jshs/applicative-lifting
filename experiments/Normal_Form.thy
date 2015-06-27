theory Normal_Form
imports Abstract_AF
begin

section {* Normal form conversion *}

lemma comp_def_ext:
  "comp = (\<lambda>g f x. g (f x))"
by rule+ simp

lemma id_unfold: "id \<equiv> \<lambda>x. x"
by (unfold id_def)

lemma comp_unfold: "comp \<equiv> (\<lambda>g f x. g (f x))"
by (unfold comp_def_ext)

ML_file "applicative.ML"

ML {*
  val abstract_sign = Applicative.mk_sign @{context} (@{term "pure"}, @{term "op \<diamond>"});
  val abstract_laws =
   {identity = @{thm af_identity},
    composition = @{thm af_composition},
    homomorphism = @{thm af_homomorphism},
    interchange = @{thm af_interchange}};
  val abstract_af = Applicative.mk_afun @{context} (abstract_sign, abstract_laws);
*}
setup {* Applicative.add_global abstract_af *}

ML {*
  fun auto_normalform_conv ctxt ct = Applicative.normalform_conv ctxt
      (Applicative.get (Context.Proof ctxt) (Thm.term_of ct)) ct;
*}

(* Tests *)

notepad
begin
  fix f g x y z

  ML_val {* Applicative.normalform_conv @{context} abstract_af @{cterm "x :: 'a af"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "pure x"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "pure f \<diamond> x"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "pure f \<diamond> x \<diamond> y"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "pure g \<diamond> (f \<diamond> x)"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "f \<diamond> x \<diamond> y"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "g \<diamond> (f \<diamond> x)"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "f \<diamond> pure x"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "pure x \<diamond> pure y"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "f \<diamond> x \<diamond> pure y"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "pure f \<diamond> x \<diamond> pure y"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "pure f \<diamond> x \<diamond> pure y \<diamond> z"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "pure f \<diamond> x \<diamond> (pure g \<diamond> y)"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "f \<diamond> (g \<diamond> x) \<diamond> y"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "f \<diamond> (g \<diamond> x \<diamond> y) \<diamond> z"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "f \<diamond> (g \<diamond> (x \<diamond> pure y)) \<diamond> z"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "f \<diamond> (g \<diamond> x \<diamond> x)"} *}
  ML_val {* auto_normalform_conv @{context} @{cterm "f x \<diamond> y"} *}
end

end
