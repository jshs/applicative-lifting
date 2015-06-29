theory Normal_Form
imports Abstract_AF
begin

section {* Normal form conversion *}

subsection {* Setup *}

lemma comp_def_ext:
  "comp = (\<lambda>g f x. g (f x))"
by rule+ simp

lemma id_unfold: "id \<equiv> \<lambda>x. x"
by (unfold id_def)

lemma comp_unfold: "comp \<equiv> (\<lambda>g f x. g (f x))"
by (unfold comp_def_ext)

ML_file "applicative.ML"


subsection {* Example: Abstract functor *}

setup {*
  let
    val abstract_sign = Applicative.mk_sign @{context} (@{term "pure"}, @{term "op \<diamond>"});
    val abstract_laws =
     {identity = @{thm af_identity},
      composition = @{thm af_composition},
      homomorphism = @{thm af_homomorphism},
      interchange = @{thm af_interchange}};
    val abstract_af = Applicative.mk_afun @{context} (abstract_sign, abstract_laws);
  in Applicative.add_global abstract_af end
*}

ML {*
  fun auto_normalform_conv ctxt ct = Applicative.normalform_conv ctxt
      (Applicative.get (Context.Proof ctxt) (Thm.term_of ct)) ct;
*}

(* Tests *)

notepad
begin
  fix f g x y z

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

  have "x = pure (\<lambda>x. x) \<diamond> x"
    apply (tactic {* Applicative.normalize_eq_tac @{context} 1 *})
    apply (rule refl)
    done

  have "pure g \<diamond> (f \<diamond> x) = pure (\<lambda>f x. g (f x)) \<diamond> f \<diamond> x"
    apply (tactic {* Applicative.normalize_eq_tac @{context} 1 *})
    apply (rule refl)
    done
end


subsection {* Example: Sets *}

(* TODO fix normalform_conv such that it works with {x} directly, if possible *)
definition single :: "'a \<Rightarrow> 'a set"
  where "single x = {x}"

definition set_ap :: "('a \<Rightarrow> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set" (infixl "\<otimes>" 60)
  where "F \<otimes> X = {f x | f x. f \<in> F \<and> x \<in> X}"

lemma set_identity: "single id \<otimes> X = X"
unfolding single_def set_ap_def
by simp

lemma set_homomorphism: "single f \<otimes> single x = single (f x)"
unfolding single_def set_ap_def
by simp

lemma set_composition: "single comp \<otimes> G \<otimes> F \<otimes> X = G \<otimes> (F \<otimes> X)"
unfolding single_def set_ap_def
by fastforce

lemma set_interchange: "F \<otimes> single x = single (\<lambda>g. g x) \<otimes> F"
unfolding single_def set_ap_def
by simp

setup {*
  let
    val set_sign = Applicative.mk_sign @{context} (@{term "single"}, @{term "op \<otimes>"});
    val set_laws =
     {identity = @{thm set_identity},
      composition = @{thm set_composition},
      homomorphism = @{thm set_homomorphism},
      interchange = @{thm set_interchange}};
    val set_af = Applicative.mk_afun @{context} (set_sign, set_laws);
  in Applicative.add_global set_af end
*}

notepad
begin
  fix X Y Z :: "nat set"

  have "single plus \<otimes> X \<otimes> (single plus \<otimes> Y \<otimes> Z) = single plus \<otimes> (single plus \<otimes> X \<otimes> Y) \<otimes> Z"
    apply (tactic {* Applicative.normalize_eq_tac @{context} 1 *})
    apply (tactic "cong_tac @{context} 1", simp_all)+
    apply (rule ext)+
    apply (insert add.assoc)
    apply simp
    done
end

end
