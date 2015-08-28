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
  have "\<forall>x. x = pure (\<lambda>x. x) \<diamond> x" by applicative_nf
  have "\<forall>x. pure x = pure x" by applicative_nf
  have "\<forall>f x. pure f \<diamond> x = pure f \<diamond> x" by applicative_nf
  have "\<forall>f x y. pure f \<diamond> x \<diamond> y = pure f \<diamond> x \<diamond> y" by applicative_nf
  have "\<forall>g f x. pure g \<diamond> (f \<diamond> x) = pure (\<lambda>f x. g (f x)) \<diamond> f \<diamond> x" by applicative_nf
  have "\<forall>f x y. f \<diamond> x \<diamond> y = pure (\<lambda>f x y. f x y) \<diamond> f \<diamond> x \<diamond> y" by applicative_nf
  have "\<forall>g f x. g \<diamond> (f \<diamond> x) = pure (\<lambda>g f x. g (f x)) \<diamond> g \<diamond> f \<diamond> x" by applicative_nf
  have "\<forall>f x. f \<diamond> pure x = pure (\<lambda>f. f x) \<diamond> f" by applicative_nf
  have "\<forall>x y. pure x \<diamond> pure y = pure (x y)" by applicative_nf
  have "\<forall>f x y. f \<diamond> x \<diamond> pure y = pure (\<lambda>f x. f x y) \<diamond> f \<diamond> x" by applicative_nf
  have "\<forall>f x y. pure f \<diamond> x \<diamond> pure y = pure (\<lambda>x. f x y) \<diamond> x" by applicative_nf
  have "\<forall>f x y z. pure f \<diamond> x \<diamond> pure y \<diamond> z = pure (\<lambda>x z. f x y z) \<diamond> x \<diamond> z" by applicative_nf
  have "\<forall>f x g y. pure f \<diamond> x \<diamond> (pure g \<diamond> y) = pure (\<lambda>x y. f x (g y)) \<diamond> x \<diamond> y" by applicative_nf
  have "\<forall>f g x y. f \<diamond> (g \<diamond> x) \<diamond> y = pure (\<lambda>f g x y. f (g x) y) \<diamond> f \<diamond> g \<diamond> x \<diamond> y" by applicative_nf
  have "\<forall>f g x y z. f \<diamond> (g \<diamond> x \<diamond> y) \<diamond> z = pure (\<lambda>f g x y z. f (g x y) z) \<diamond> f \<diamond> g \<diamond> x \<diamond> y \<diamond> z" by applicative_nf
  have "\<forall>f g x y z. f \<diamond> (g \<diamond> (x \<diamond> pure y)) \<diamond> z = pure (\<lambda>f g x z. f (g (x y)) z) \<diamond> f \<diamond> g \<diamond> x \<diamond> z" by applicative_nf
  have "\<forall>f g x. f \<diamond> (g \<diamond> x \<diamond> x) = pure (\<lambda>f g x x'. f (g x x')) \<diamond> f \<diamond> g \<diamond> x \<diamond> x" by applicative_nf
  have "\<forall>f x y. f x \<diamond> y = pure (\<lambda>f x. f x) \<diamond> f x \<diamond> y" by applicative_nf
next
  fix f :: "('a \<Rightarrow> 'b) af" and g :: "('b \<Rightarrow> 'c) af" and x
  have "g \<diamond> (f \<diamond> x) = pure (\<lambda>g f x. g (f x)) \<diamond> g \<diamond> f \<diamond> x" by applicative_nf
end
(* TODO automatic test for names of new variables *)

lemma "\<And>f x. f \<diamond> x = x"
apply applicative_nf
oops


subsection {* Example: Sets *}

definition set_ap :: "('a \<Rightarrow> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set" (infixl "\<otimes>" 60)
  where "F \<otimes> X = {f x | f x. f \<in> F \<and> x \<in> X}"

applicative set (C)
for
  pure: "\<lambda>x. {x}"
  ap: "op \<otimes>"
unfolding single_def set_ap_def
by fastforce+

instantiation set :: (plus) plus
begin
  definition set_plus_def[applicative_unfold]: "X + Y = {plus} \<otimes> X \<otimes> Y"
  instance ..
end

instantiation set :: (semigroup_add) semigroup_add
begin
  instance proof
    fix X Y Z :: "'a set"
    from add.assoc
    show "X + Y + Z = X + (Y + Z)" by applicative_lifting
   qed
end

instantiation set :: (ab_semigroup_add) ab_semigroup_add
begin
  instance proof
    fix X Y :: "'a set"
    from add.commute
    show "X + Y = Y + X" by applicative_lifting
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
by applicative_lifting


subsection {* Example: Streams *}

(*
  FIXME "sconst" is just an abbreviation containing "id", which causes problems with simplifier
  rule id_apply
*)
definition "spure = sconst"

definition stream_ap :: "('a \<Rightarrow> 'b) stream \<Rightarrow> 'a stream \<Rightarrow> 'b stream" (infixl "<.>" 60)
where
  "stream_ap f x = smap (\<lambda>(f, x). f x) (szip f x)"

applicative stream (C, K, W)
for
  pure: spure
  ap: stream_ap
proof -
  fix x
  show "spure (\<lambda>x. x) <.> x = x"
    unfolding spure_def stream_ap_def
    by (coinduction arbitrary: x) simp
next
  fix f x
  show "spure f <.> spure x = spure (f x)"
    unfolding spure_def stream_ap_def
    by coinduction simp
next
  fix g f x
  show "spure (\<lambda>g f x. g (f x)) <.> g <.> f <.> x = g <.> (f <.> x)"
    unfolding spure_def stream_ap_def
    by (coinduction arbitrary: g f x) auto
next
  fix f x
  show "f <.> spure x = spure (\<lambda>f. f x) <.> f"
    unfolding spure_def stream_ap_def
    by (coinduction arbitrary: f) auto
next
  fix f x y
  show "spure (\<lambda>f x y. f y x) <.> f <.> x <.> y = f <.> y <.> x"
    unfolding spure_def stream_ap_def
    by (coinduction arbitrary: f x y) auto
next
  fix x y
  show "spure (\<lambda>x y. x) <.> x <.> y = x"
    unfolding spure_def stream_ap_def
    by (coinduction arbitrary: x y) auto
next
  fix f x
  show "spure (\<lambda>f x. f x x) <.> f <.> x = f <.> x <.> x"
    unfolding spure_def stream_ap_def
    by (coinduction arbitrary: f x) auto
qed

lemma smap_applicative[applicative_unfold]: "smap f x = spure f <.> x"
unfolding spure_def stream_ap_def
by (coinduction arbitrary: x) auto

lemma smap2_applicative[applicative_unfold]: "smap2 f x y = spure f <.> x <.> y"
unfolding spure_def stream_ap_def
by (coinduction arbitrary: x y) auto

instantiation stream :: (plus) plus
begin
  definition stream_plus_def[applicative_unfold]: "x + y = spure plus <.> x <.> y"
  instance ..
end

instantiation stream :: (times) times
begin
  definition stream_times_def[applicative_unfold]: "x * y = spure times <.> x <.> y"
  instance ..
end

lemma "(x::int stream) * spure 0 = spure 0"
by applicative_lifting

lemma "(x::int stream) * (y + z) = x * y + x * z"
apply applicative_lifting
by algebra


definition "lift_streams xs = foldr (smap2 Cons) xs (spure [])"

lemma lift_streams_Nil[applicative_unfold]: "lift_streams [] = spure []"
unfolding lift_streams_def
by simp

lemma lift_streams_Cons[applicative_unfold]:
  "lift_streams (x # xs) = smap2 Cons x (lift_streams xs)"
unfolding lift_streams_def
by applicative_unfold

lemma stream_append_Cons: "smap2 append (smap2 Cons x ys) zs = smap2 Cons x (smap2 append ys zs)"
by applicative_lifting

lemma lift_streams_append[applicative_unfold]:
  "lift_streams (xs @ ys) = smap2 append (lift_streams xs) (lift_streams ys)"
proof (induction xs)
  case Nil
  (*
    case could be proved directly if "lift_streams ([] @ ys) = lift_streams ys" is solved
    in head_cong_tac (invoke simplifier?) -- but only with applicative_nf
  *)
  have "lift_streams ys = spure append <.> lift_streams [] <.> lift_streams ys"
    by applicative_lifting
  thus ?case by applicative_unfold
next
  case (Cons x xs)
  with stream_append_Cons  (* the actual lifted fact *)
  show ?case by applicative_unfold (rule sym)  (* slightly weird *)
qed

(* There seems to be a pattern! *)

lemma "lift_streams (rev x) = smap rev (lift_streams x)"
proof (induction x)
  case Nil
  have "lift_streams [] = smap rev (lift_streams [])"
    by applicative_lifting
  thus ?case by simp
next
  case (Cons x xs)
  have "\<forall>y ys. rev ys @ [y] = rev (y # ys)" by simp
  hence "\<forall>y ys. smap2 append (smap rev ys) (smap2 Cons y (spure [])) = smap rev (smap2 Cons y ys)"
    by applicative_lifting
  with Cons.IH show ?case by applicative_unfold blast
qed

definition [applicative_unfold]: "sconcat xs = smap concat xs"

lemma "sconcat (lift_streams [spure ''Hello '', spure ''world!'']) = spure ''Hello world!''"
by applicative_lifting

end
