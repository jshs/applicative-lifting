theory Normal_Form
imports Abstract_AF
begin

section {* Normal form conversion *}

lemma comp_def_ext:
  "comp = (\<lambda>g f x. g (f x))"
by rule+ simp

lemma nf_leaf:
  "x \<equiv> pure (\<lambda>x. x) \<diamond> x"
unfolding atomize_eq id_def[THEN sym] af_identity
..

lemma nf_merge:
  "pure f \<diamond> pure x \<equiv> pure (f x)"
unfolding atomize_eq af_homomorphism
..

lemma nf_swap:
  "f \<diamond> pure x \<equiv> pure (\<lambda>f. f x) \<diamond> f"
unfolding atomize_eq af_interchange
..

lemma nf_rotate:
  "g \<diamond> (f \<diamond> x) \<equiv> pure (\<lambda>g f x. g (f x)) \<diamond> g \<diamond> f \<diamond> x"
unfolding atomize_eq af_composition[THEN sym] comp_def_ext
..

lemma nf_pure_rotate:
  "pure g \<diamond> (f \<diamond> x) \<equiv> pure (\<lambda>f x. g (f x)) \<diamond> f \<diamond> x"
unfolding nf_rotate af_homomorphism
by (rule reflexive)


ML {*
  fun dest_pure (Const (@{const_name "pure"}, _) $ x) = x
    | dest_pure t = raise TERM("dest_pure", [t]);

  fun dest_ap (Const (@{const_name "ap"}, _) $ f $ x) = (f, x)
    | dest_ap t = raise TERM ("dest_ap", [t]);

  val leaf_conv = Conv.rewr_conv @{thm nf_leaf};
  val merge_conv = Conv.rewr_conv @{thm nf_merge};
  val swap_conv = Conv.rewr_conv @{thm nf_swap};
  val rotate_conv = Conv.rewr_conv @{thm nf_rotate};
  val pure_rotate_conv = Conv.rewr_conv @{thm nf_pure_rotate};

  fun normalize_pure_nf ct =
    ((pure_rotate_conv then_conv Conv.arg1_conv normalize_pure_nf) else_conv merge_conv) ct;

  val normalize_nf_pure = swap_conv then_conv normalize_pure_nf;

  fun normalize_nf_nf ct =
    ((rotate_conv then_conv
      Conv.arg1_conv (Conv.arg1_conv normalize_pure_nf then_conv normalize_nf_nf)) else_conv
    normalize_nf_pure) ct;

  fun normalform_conv ct =
    let
      val t = Thm.term_of ct;
      val normalize_ap = Conv.arg1_conv normalform_conv then_conv
        Conv.arg_conv normalform_conv then_conv
        normalize_nf_nf;
    in
      if can dest_ap t then normalize_ap ct
      else if can dest_pure t then Conv.all_conv ct
      else leaf_conv ct
    end;
*}

(* Tests *)

notepad
begin
  fix f g x y z

  ML_val {* normalform_conv @{cterm "x :: 'a af"} *}
  ML_val {* normalform_conv @{cterm "pure x"} *}
  ML_val {* normalform_conv @{cterm "pure f \<diamond> x"} *}
  ML_val {* normalform_conv @{cterm "pure f \<diamond> x \<diamond> y"} *}
  ML_val {* normalform_conv @{cterm "pure g \<diamond> (f \<diamond> x)"} *}
  ML_val {* normalform_conv @{cterm "f \<diamond> x \<diamond> y"} *}
  ML_val {* normalform_conv @{cterm "g \<diamond> (f \<diamond> x)"} *}
  ML_val {* normalform_conv @{cterm "f \<diamond> pure x"} *}
  ML_val {* normalform_conv @{cterm "pure x \<diamond> pure y"} *}
  ML_val {* normalform_conv @{cterm "f \<diamond> x \<diamond> pure y"} *}
  ML_val {* normalform_conv @{cterm "pure f \<diamond> x \<diamond> pure y"} *}
  ML_val {* normalform_conv @{cterm "pure f \<diamond> x \<diamond> pure y \<diamond> z"} *}
  ML_val {* normalform_conv @{cterm "pure f \<diamond> x \<diamond> (pure g \<diamond> y)"} *}
  ML_val {* normalform_conv @{cterm "f \<diamond> (g \<diamond> x) \<diamond> y"} *}
  ML_val {* normalform_conv @{cterm "f \<diamond> (g \<diamond> x \<diamond> y) \<diamond> z"} *}
  ML_val {* normalform_conv @{cterm "f \<diamond> (g \<diamond> (x \<diamond> pure y)) \<diamond> z"} *}
end

end
