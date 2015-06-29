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

method_setup lifting_nf = {* Scan.succeed (fn ctxt =>
  SIMPLE_METHOD' (Applicative.lifting_nf_tac ctxt)) *}


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

notepad
begin
  have "\<And>x. x = pure (\<lambda>x. x) \<diamond> x" by lifting_nf
  have "\<And>x. pure x = pure x" by lifting_nf
  have "\<And>f x. pure f \<diamond> x = pure f \<diamond> x" by lifting_nf
  have "\<And>f x y. pure f \<diamond> x \<diamond> y = pure f \<diamond> x \<diamond> y" by lifting_nf
  have "\<And>g f x. pure g \<diamond> (f \<diamond> x) = pure (\<lambda>f x. g (f x)) \<diamond> f \<diamond> x" by lifting_nf
  have "\<And>f x y. f \<diamond> x \<diamond> y = pure (\<lambda>f x y. f x y) \<diamond> f \<diamond> x \<diamond> y" by lifting_nf
  have "\<And>g f x. g \<diamond> (f \<diamond> x) = pure (\<lambda>g f x. g (f x)) \<diamond> g \<diamond> f \<diamond> x" by lifting_nf
  have "\<And>f x. f \<diamond> pure x = pure (\<lambda>f. f x) \<diamond> f" by lifting_nf
  have "\<And>x y. pure x \<diamond> pure y = pure (x y)" by lifting_nf
  have "\<And>f x y. f \<diamond> x \<diamond> pure y = pure (\<lambda>f x. f x y) \<diamond> f \<diamond> x" by lifting_nf
  have "\<And>f x y. pure f \<diamond> x \<diamond> pure y = pure (\<lambda>x. f x y) \<diamond> x" by lifting_nf
  have "\<And>f x y z. pure f \<diamond> x \<diamond> pure y \<diamond> z = pure (\<lambda>x z. f x y z) \<diamond> x \<diamond> z" by lifting_nf
  have "\<And>f x g y. pure f \<diamond> x \<diamond> (pure g \<diamond> y) = pure (\<lambda>x y. f x (g y)) \<diamond> x \<diamond> y" by lifting_nf
  have "\<And>f g x y. f \<diamond> (g \<diamond> x) \<diamond> y = pure (\<lambda>f g x y. f (g x) y) \<diamond> f \<diamond> g \<diamond> x \<diamond> y" by lifting_nf
  have "\<And>f g x y z. f \<diamond> (g \<diamond> x \<diamond> y) \<diamond> z = pure (\<lambda>f g x y z. f (g x y) z) \<diamond> f \<diamond> g \<diamond> x \<diamond> y \<diamond> z" by lifting_nf
  have "\<And>f g x y z. f \<diamond> (g \<diamond> (x \<diamond> pure y)) \<diamond> z = pure (\<lambda>f g x z. f (g (x y)) z) \<diamond> f \<diamond> g \<diamond> x \<diamond> z" by lifting_nf
  have "\<And>f g x. f \<diamond> (g \<diamond> x \<diamond> x) = pure (\<lambda>f g x x'. f (g x x')) \<diamond> f \<diamond> g \<diamond> x \<diamond> x" by lifting_nf
  have "\<And>f x y. f x \<diamond> y = pure (\<lambda>f x. f x) \<diamond> f x \<diamond> y" by lifting_nf
next
  fix f :: "('a \<Rightarrow> 'b) af" and g :: "('b \<Rightarrow> 'c) af" and x
  have "g \<diamond> (f \<diamond> x) = pure (\<lambda>g f x. g (f x)) \<diamond> g \<diamond> f \<diamond> x" by lifting_nf
end
(* TODO automatic test for names of new variables *)


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

instantiation set :: (semigroup_add) semigroup_add
begin
  definition set_plus_def: "X + Y = single plus \<otimes> X \<otimes> Y"
  instance proof
    fix X Y Z :: "'a set"
    from add.assoc
    show "X + Y + Z = X + (Y + Z)" unfolding set_plus_def by lifting_nf
   qed
end

end
