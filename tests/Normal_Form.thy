theory Normal_Form
imports "../src/Applicative_Functor" "../src/Stream_Arith" Abstract_AF
begin

section {* Normal form conversion *}

subsection {* Example: Abstract functor *}

notepad
begin
  have "\<forall>x. x = af_pure (\<lambda>x. x) \<diamond> x" by applicative_nf rule
  have "\<forall>x. af_pure x = af_pure x" by applicative_nf rule
  have "\<forall>f x. af_pure f \<diamond> x = af_pure f \<diamond> x" by applicative_nf rule
  have "\<forall>f x y. af_pure f \<diamond> x \<diamond> y = af_pure f \<diamond> x \<diamond> y" by applicative_nf rule
  have "\<forall>g f x. af_pure g \<diamond> (f \<diamond> x) = af_pure (\<lambda>f x. g (f x)) \<diamond> f \<diamond> x" by applicative_nf rule
  have "\<forall>f x y. f \<diamond> x \<diamond> y = af_pure (\<lambda>f x y. f x y) \<diamond> f \<diamond> x \<diamond> y" by applicative_nf rule
  have "\<forall>g f x. g \<diamond> (f \<diamond> x) = af_pure (\<lambda>g f x. g (f x)) \<diamond> g \<diamond> f \<diamond> x" by applicative_nf rule
  have "\<forall>f x. f \<diamond> af_pure x = af_pure (\<lambda>f. f x) \<diamond> f" by applicative_nf rule
  have "\<forall>x y. af_pure x \<diamond> af_pure y = af_pure (x y)" by applicative_nf rule
  have "\<forall>f x y. f \<diamond> x \<diamond> af_pure y = af_pure (\<lambda>f x. f x y) \<diamond> f \<diamond> x" by applicative_nf rule
  have "\<forall>f x y. af_pure f \<diamond> x \<diamond> af_pure y = af_pure (\<lambda>x. f x y) \<diamond> x" by applicative_nf rule
  have "\<forall>f x y z. af_pure f \<diamond> x \<diamond> af_pure y \<diamond> z = af_pure (\<lambda>x z. f x y z) \<diamond> x \<diamond> z" by applicative_nf rule
  have "\<forall>f x g y. af_pure f \<diamond> x \<diamond> (af_pure g \<diamond> y) = af_pure (\<lambda>x y. f x (g y)) \<diamond> x \<diamond> y" by applicative_nf rule
  have "\<forall>f g x y. f \<diamond> (g \<diamond> x) \<diamond> y = af_pure (\<lambda>f g x y. f (g x) y) \<diamond> f \<diamond> g \<diamond> x \<diamond> y" by applicative_nf rule
  have "\<forall>f g x y z. f \<diamond> (g \<diamond> x \<diamond> y) \<diamond> z = af_pure (\<lambda>f g x y z. f (g x y) z) \<diamond> f \<diamond> g \<diamond> x \<diamond> y \<diamond> z" by applicative_nf rule
  have "\<forall>f g x y z. f \<diamond> (g \<diamond> (x \<diamond> af_pure y)) \<diamond> z = af_pure (\<lambda>f g x z. f (g (x y)) z) \<diamond> f \<diamond> g \<diamond> x \<diamond> z" by applicative_nf rule
  have "\<forall>f g x. f \<diamond> (g \<diamond> x \<diamond> x) = af_pure (\<lambda>f g x x'. f (g x x')) \<diamond> f \<diamond> g \<diamond> x \<diamond> x" by applicative_nf rule
  have "\<forall>f x y. f x \<diamond> y = af_pure (\<lambda>f x. f x) \<diamond> f x \<diamond> y" by applicative_nf rule
next
  fix f :: "('a \<Rightarrow> 'b) af" and g :: "('b \<Rightarrow> 'c) af" and x
  have "g \<diamond> (f \<diamond> x) = af_pure (\<lambda>g f x. g (f x)) \<diamond> g \<diamond> f \<diamond> x" by applicative_nf rule
end
(* TODO automatic test for names of new variables *)

lemma "\<And>f x::'a af. f \<diamond> x = x"
apply applicative_nf
oops


subsection {* Example: Sets *}

instantiation set :: (plus) plus
begin
  definition set_plus_def[applicative_unfold]: "(X::('a::plus)set) + Y = {plus} \<diamond> X \<diamond> Y"
  instance ..
end

thm add.assoc[applicative_lifted set]

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

lemma "Inl plus \<diamond> (x :: nat + 'e list) \<diamond> x = Inl (\<lambda>x. 2 * x) \<diamond> x"
by applicative_lifting simp


subsection {* Example: Streams *}

lemma "(x::int stream) * sconst 0 = sconst 0"
by applicative_lifting simp

lemma "(x::int stream) * (y + z) = x * y + x * z"
apply applicative_lifting
by algebra


definition "lift_streams xs = foldr (smap2 Cons) xs (sconst [])"

lemma lift_streams_Nil[applicative_unfold]: "lift_streams [] = sconst []"
unfolding lift_streams_def
by simp

lemma lift_streams_Cons[applicative_unfold]:
  "lift_streams (x # xs) = smap2 Cons x (lift_streams xs)"
unfolding lift_streams_def
by applicative_unfold

lemma stream_append_Cons: "smap2 append (smap2 Cons x ys) zs = smap2 Cons x (smap2 append ys zs)"
by applicative_lifting simp

lemma lift_streams_append[applicative_unfold]:
  "lift_streams (xs @ ys) = smap2 append (lift_streams xs) (lift_streams ys)"
proof (induction xs)
  case Nil
  (*
    case could be proved directly if "lift_streams ([] @ ys) = lift_streams ys" is solved
    in head_cong_tac (invoke simplifier?) -- but only with applicative_nf
  *)
  have "lift_streams ys = sconst append \<diamond> lift_streams [] \<diamond> lift_streams ys"
    by applicative_lifting simp
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
    by applicative_lifting simp
  thus ?case by simp
next
  case (Cons x xs)
  have "\<forall>y ys. rev ys @ [y] = rev (y # ys)" by simp
  hence "\<forall>y ys. smap2 append (smap rev ys) (smap2 Cons y (sconst [])) = smap rev (smap2 Cons y ys)"
    by applicative_lifting simp
  with Cons.IH show ?case by applicative_unfold blast
qed

definition [applicative_unfold]: "sconcat xs = smap concat xs"

lemma "sconcat (lift_streams [sconst ''Hello '', sconst ''world!'']) = sconst ''Hello world!''"
by applicative_lifting simp

print_applicative

end
