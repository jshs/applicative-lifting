theory Normal_Form
imports "../src/Applicative" Abstract_AF "~~/src/HOL/Library/Stream"
begin

section {* Normal form conversion *}

subsection {* Example: Abstract functor *}

applicative af
for
  pure: pure
  ap: "op \<diamond>"
using af_identity af_composition af_homomorphism af_interchange
unfolding id_def comp_def[THEN ext, THEN ext]
.

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

applicative set (C)
for
  pure: single
  ap: "op \<otimes>"
unfolding single_def set_ap_def
by fastforce+

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

fun do_with :: "('a \<Rightarrow> 'b) + 'e \<Rightarrow> 'a + 'e \<Rightarrow> 'b + 'e" (infixl "\<oplus>" 60)
where
    "Inr e \<oplus> _ = Inr e"
  | "Inl f \<oplus> Inr e = Inr e"
  | "Inl f \<oplus> Inl x = Inl (f x)"

(* FIXME names of type variables in proof obligations are visible to user *)

applicative either (W)
for
  pure: "Inl :: 'a \<Rightarrow> 'a + 'e"
  ap: do_with
proof -
  fix g f x
  show "Inl (\<lambda>x. x) \<oplus> x = x" by (cases x) simp_all
  show "Inl (\<lambda>g f x. g (f x)) \<oplus> g \<oplus> f \<oplus> x = g \<oplus> (f \<oplus> x)"
    by (cases g, cases f, cases x) simp_all
next
  fix f x
  show "Inl f \<oplus> Inl x = Inl (f x)" by simp
next
  fix f x
  show "f \<oplus> Inl x = Inl (\<lambda>f. f x) \<oplus> f" by (cases f) simp_all
next
  fix f x
  show "Inl (\<lambda>f x. f x x) \<oplus> f \<oplus> x = f \<oplus> x \<oplus> x" by (cases f, cases x) simp_all
qed

lemma "Inl plus \<oplus> (x :: nat + 'e list) \<oplus> x = Inl (\<lambda>x. 2 * x) \<oplus> x"
by general_lifting linarith


subsection {* Example: Streams *}

definition stream_ap :: "('a \<Rightarrow> 'b) stream \<Rightarrow> 'a stream \<Rightarrow> 'b stream" (infixl "<.>" 60)
where
  "stream_ap f x = smap (\<lambda>(f, x). f x) (szip f x)"

applicative stream (C, K, W)
for
  pure: sconst
  ap: stream_ap
proof -
  fix x
  show "sconst (\<lambda>x. x) <.> x = x"
    unfolding stream_ap_def
    by (coinduction arbitrary: x) simp
next
  fix f x
  show "sconst f <.> sconst x = sconst (f x)"
    unfolding stream_ap_def
    by coinduction simp
next
  fix g f x
  show "sconst (\<lambda>g f x. g (f x)) <.> g <.> f <.> x = g <.> (f <.> x)"
    unfolding stream_ap_def
    by (coinduction arbitrary: g f x) auto
next
  fix f x
  show "f <.> sconst x = sconst (\<lambda>f. f x) <.> f"
    unfolding stream_ap_def
    by (coinduction arbitrary: f) auto
next
  fix f x y
  show "sconst (\<lambda>f x y. f y x) <.> f <.> x <.> y = f <.> y <.> x"
    unfolding stream_ap_def
    by (coinduction arbitrary: f x y) auto
next
  fix x y
  show "sconst (\<lambda>x y. x) <.> x <.> y = x"
    unfolding stream_ap_def
    by (coinduction arbitrary: x y) auto
next
  fix f x
  show "sconst (\<lambda>f x. f x x) <.> f <.> x = f <.> x <.> x"
    unfolding stream_ap_def
    by (coinduction arbitrary: f x) auto
qed

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
