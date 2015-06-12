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


ML_file "applicative.ML"

ML {*
  fun dest_pure (Const (@{const_name "pure"}, _) $ x) = x
    | dest_pure t = raise TERM("dest_pure", [t]);

  fun dest_ap (Const (@{const_name "ap"}, _) $ f $ x) = (f, x)
    | dest_ap t = raise TERM ("dest_ap", [t]);

  val clean_name = perhaps (perhaps_apply [try Name.dest_skolem, try Name.dest_internal]);

  (* based on term_name from Pure/term.ML *)
  fun term_to_vname (Const (x, _)) = Long_Name.base_name x
    | term_to_vname (Free (x, _)) = clean_name x
    | term_to_vname (Var ((x, _), _)) = clean_name x
    | term_to_vname _ = Name.uu;

  fun rename_rewr_conv mk_map rule ct =
    let val rule' = Drule.rename_bvars (mk_map (Thm.term_of ct)) rule
    in Conv.rewr_conv rule' ct end;

  val leaf_conv = rename_rewr_conv (fn t => [("x", term_to_vname t)]) @{thm nf_leaf};
  val merge_conv = Conv.rewr_conv @{thm nf_merge};
  val swap_conv = Conv.rewr_conv @{thm nf_swap};

  fun rename_rr_conv v = rename_rewr_conv (fn t =>
      (case t of
          _ $ (_ $ t') => [(v, term_to_vname t')]
        | _ => raise TERM ("rename_rr_conv", [t])));

  val rotate_conv = rename_rr_conv "x" @{thm nf_rotate};
  val pure_rotate_conv = rename_rr_conv "x" @{thm nf_pure_rotate};

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
  ML_val {* normalform_conv @{cterm "f \<diamond> (g \<diamond> x \<diamond> x)"} *}
  ML_val {* normalform_conv @{cterm "f x \<diamond> y"} *}
end


ML {*
  val abstract_af =
   {pure = @{term pure},
    ap = @{term "op \<diamond>"},
    identity = @{thm af_identity},
    composition = @{thm af_composition},
    homomorphism = @{thm af_homomorphism},
    interchange = @{thm af_interchange}};
*}
setup {* Applicative.add_global abstract_af *}

lemma id_unfold: "id \<equiv> \<lambda>x. x"
by (unfold id_def)

lemma comp_unfold: "comp \<equiv> (\<lambda>g f x. g (f x))"
by (unfold comp_def_ext)

ML {*
  type nf_rules =
   {leaf_rule: thm,
    merge_rule: thm,
    swap_rule: thm,
    rotate_rule: thm,
    pure_rotate_rule: thm};

  fun mk_nf_rules ctx (af: Applicative.afun) =
    let
      val leaf_rule = Thm.symmetric (#identity af RS eq_reflection)
          |> Raw_Simplifier.rewrite_rule ctx [@{thm id_unfold}];
      val merge_rule = #homomorphism af RS eq_reflection;
      val swap_rule = #interchange af RS eq_reflection;
      val rotate_rule = Thm.symmetric (#composition af RS eq_reflection)
          |> Raw_Simplifier.rewrite_rule ctx [@{thm comp_unfold}];

      val g = Thm.cprop_of rotate_rule |> Thm.dest_arg1 |> Thm.dest_arg1;
      val gT = Thm.typ_of_cterm g;
      val pure = Logic.varify_global (#pure af);
      val pure_argT = Term.type_of pure |> Term.dest_funT |> fst;
      val pure_x = betapply (pure, Var (("", maxidx_of_term pure + 1), pure_argT));
      val tyenv = Sign.typ_match (Proof_Context.theory_of ctx) (Term.type_of pure_x, gT) Vartab.empty;
      val g' = Envir.subst_term_types tyenv (Thm.term_of g);
      val pure_x' = Envir.subst_term_types tyenv pure_x;
      val pure_rotate_rule = Thm.certify_instantiate ([], [(Term.dest_Var g', pure_x')]) rotate_rule
          |> Raw_Simplifier.rewrite_rule @{context} [merge_rule];
    in
      {leaf_rule = leaf_rule, merge_rule = merge_rule, swap_rule = swap_rule,
       rotate_rule = rotate_rule, pure_rotate_rule = pure_rotate_rule}
    end;
*}

ML_val {*
  val ctx = @{context};
  mk_nf_rules ctx (Applicative.get (Context.Proof ctx) @{term "f \<diamond> x"})
*}

end
