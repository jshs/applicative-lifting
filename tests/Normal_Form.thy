theory Normal_Form
imports "../src/Applicative" Abstract_AF "~~/src/HOL/Library/Stream"
begin

section {* Normal form conversion *}

subsection {* Example: Abstract functor *}

lemma af_identity': "pure (\<lambda>x. x) \<diamond> x = x"
using af_identity unfolding id_def .

lemma af_composition': "pure (\<lambda>g f x. g (f x)) \<diamond> g \<diamond> f \<diamond> x = g \<diamond> (f \<diamond> x)"
using af_composition unfolding comp_def[THEN ext, THEN ext] .

setup {*
  let
    val abstract_sign = Applicative.mk_sign @{context} (@{term "pure"}, @{term "op \<diamond>"});
    val abstract_laws =
     {identity = @{thm af_identity'},
      composition = @{thm af_composition'},
      homomorphism = @{thm af_homomorphism},
      interchange = @{thm af_interchange},
      flip = NONE, const = NONE, duplicate = NONE};
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

lemma "\<And>f x. f \<diamond> x = x"
apply lifting_nf
oops


subsection {* Example: Sets *}

(* TODO fix normalform_conv such that it works with {x} directly, if possible *)
definition single :: "'a \<Rightarrow> 'a set"
  where "single x = {x}"

definition set_ap :: "('a \<Rightarrow> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set" (infixl "\<otimes>" 60)
  where "F \<otimes> X = {f x | f x. f \<in> F \<and> x \<in> X}"

lemma set_identity: "single (\<lambda>x. x) \<otimes> X = X"
unfolding single_def set_ap_def
by simp

lemma set_homomorphism: "single f \<otimes> single x = single (f x)"
unfolding single_def set_ap_def
by simp

lemma set_composition: "single (\<lambda>g f x. g (f x)) \<otimes> G \<otimes> F \<otimes> X = G \<otimes> (F \<otimes> X)"
unfolding single_def set_ap_def
by fastforce

lemma set_interchange: "F \<otimes> single x = single (\<lambda>g. g x) \<otimes> F"
unfolding single_def set_ap_def
by simp

lemma set_flip: "single (\<lambda>f x y. f y x) \<otimes> F \<otimes> X \<otimes> Y = F \<otimes> Y \<otimes> X"
unfolding single_def set_ap_def
by fastforce

setup {*
  let
    val set_sign = Applicative.mk_sign @{context} (@{term "single"}, @{term "op \<otimes>"});
    val set_laws =
     {identity = @{thm set_identity},
      composition = @{thm set_composition},
      homomorphism = @{thm set_homomorphism},
      interchange = @{thm set_interchange},
      flip = SOME @{thm set_flip},
      const = NONE, duplicate = NONE};
    val set_af = Applicative.mk_afun @{context} (set_sign, set_laws);
  in Applicative.add_global set_af end
*}

instantiation set :: (plus) plus
begin
  definition set_plus_def: "X + Y = single plus \<otimes> X \<otimes> Y"
  instance ..
end

instantiation set :: (semigroup_add) semigroup_add
begin
  instance proof
    fix X Y Z :: "'a set"
    from add.assoc
    show "X + Y + Z = X + (Y + Z)" unfolding set_plus_def by general_lifting
   qed
end

instantiation set :: (ab_semigroup_add) ab_semigroup_add
begin
  instance proof
    fix X Y :: "'a set"
    from add.commute
    show "X + Y = Y + X" unfolding set_plus_def by general_lifting
  qed
end


subsection {* Example: Sum type (a.k.a. either) *}

(* TODO support parametric functors to generalize the other type *)

fun do_with :: "('a \<Rightarrow> 'b) + nat \<Rightarrow> 'a + nat \<Rightarrow> 'b + nat" (infixl "\<oplus>" 60)
where
    "Inr e \<oplus> _ = Inr e"
  | "Inl f \<oplus> Inr e = Inr e"
  | "Inl f \<oplus> Inl x = Inl (f x)"

lemma inl_identity: "Inl (\<lambda>x. x) \<oplus> x = x"
by (cases x) simp_all

lemma inl_homomorphism: "Inl f \<oplus> Inl x = Inl (f x)"
by simp

lemma inl_composition: "Inl (\<lambda>g f x. g (f x)) \<oplus> g \<oplus> f \<oplus> x = g \<oplus> (f \<oplus> x)"
by (cases g, cases f, cases x) simp_all

lemma inl_interchange: "f \<oplus> Inl x = Inl (\<lambda>f. f x) \<oplus> f"
by (cases f) simp_all

lemma inl_duplicate: "Inl (\<lambda>f x. f x x) \<oplus> f \<oplus> x = f \<oplus> x \<oplus> x"
by (cases f, cases x) simp_all

setup {*
  let
    val inl_sign = Applicative.mk_sign @{context} (@{term "Inl::'a \<Rightarrow> 'a + nat"}, @{term "op \<oplus>"});
    val inl_laws =
     {identity = @{thm inl_identity},
      composition = @{thm inl_composition},
      homomorphism = @{thm inl_homomorphism},
      interchange = @{thm inl_interchange},
      flip = NONE, const = NONE,
      duplicate = SOME @{thm inl_duplicate}};
    val inl_af = Applicative.mk_afun @{context} (inl_sign, inl_laws);
  in Applicative.add_global inl_af end
*}

lemma "Inl plus \<oplus> (x :: nat + nat) \<oplus> x = Inl (\<lambda>x. 2 * x) \<oplus> x"
by general_lifting linarith


subsection {* Example: Streams *}

definition stream_ap :: "('a \<Rightarrow> 'b) stream \<Rightarrow> 'a stream \<Rightarrow> 'b stream" (infixl "<.>" 60)
where
  "stream_ap f x = smap (\<lambda>(f, x). f x) (szip f x)"

lemma stream_identity: "sconst (\<lambda>x. x) <.> x = x"
unfolding stream_ap_def
by (coinduction arbitrary: x) simp

lemma stream_homomorphism: "sconst f <.> sconst x = sconst (f x)"
unfolding stream_ap_def
by coinduction simp

lemma stream_composition: "sconst (\<lambda>g f x. g (f x)) <.> g <.> f <.> x = g <.> (f <.> x)"
unfolding stream_ap_def
by (coinduction arbitrary: g f x) auto

lemma stream_interchange: "f <.> sconst x = sconst (\<lambda>f. f x) <.> f"
unfolding stream_ap_def
by (coinduction arbitrary: f) auto

lemma stream_flip: "sconst (\<lambda>f x y. f y x) <.> f <.> x <.> y = f <.> y <.> x"
unfolding stream_ap_def
by (coinduction arbitrary: f x y) auto

lemma stream_const: "sconst (\<lambda>x y. x) <.> x <.> y = x"
unfolding stream_ap_def
by (coinduction arbitrary: x y) auto

lemma stream_duplicate: "sconst (\<lambda>f x. f x x) <.> f <.> x = f <.> x <.> x"
unfolding stream_ap_def
by (coinduction arbitrary: f x) auto

setup {*
  let
    val stream_sign = Applicative.mk_sign @{context} (@{term "sconst"}, @{term "op <.>"});
    val stream_laws =
     {identity = @{thm stream_identity},
      composition = @{thm stream_composition},
      homomorphism = @{thm stream_homomorphism},
      interchange = @{thm stream_interchange},
      flip = SOME @{thm stream_flip},
      const = SOME @{thm stream_const},
      duplicate = SOME @{thm stream_duplicate}};
    val stream_af = Applicative.mk_afun @{context} (stream_sign, stream_laws);
  in Applicative.add_global stream_af end
*}

instantiation stream :: (plus) plus
begin
  definition stream_plus_def: "x + y = sconst plus <.> x <.> y"
  instance ..
end

instantiation stream :: (times) times
begin
  definition stream_times_def: "x * y = sconst times <.> x <.> y"
  instance ..
end

lemma "(x::int stream) * sconst 0 = sconst 0"
unfolding stream_times_def
by general_lifting linarith

lemma "(x::int stream) * (y + z) = x * y + x * z"
unfolding stream_plus_def stream_times_def
apply general_lifting
by algebra

end
