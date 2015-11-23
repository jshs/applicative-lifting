(*  Title:      Stream_Arith.thy
    Author:     Andreas Lochbihler, ETH Zurich
    Author:     Joshua Schneider, ETH Zurich

Pointwise arithmetic on streams
*)

theory Stream_Arith
imports "~~/src/HOL/Library/Stream" Applicative_Functor
begin

section \<open>Pointwise arithmetic on streams\<close>

subsection \<open>Streams are applicative\<close>

primcorec ap_stream :: "('a \<Rightarrow> 'b) stream \<Rightarrow> 'a stream \<Rightarrow> 'b stream"
where
    "shd (ap_stream f x) = shd f (shd x)"
  | "stl (ap_stream f x) = ap_stream (stl f) (stl x)"

adhoc_overloading pure sconst
adhoc_overloading ap ap_stream

applicative stream (C, K, W)
for
  pure: sconst
  ap: ap_stream
proof -
  fix x :: "'a stream"
  show "pure (\<lambda>x. x) \<diamond> x = x" by (coinduction arbitrary: x) simp
next
  fix f :: "'a \<Rightarrow> 'b" and x
  show "sconst f \<diamond> pure x = pure (f x)" by coinduction simp
next
  fix g :: "('c \<Rightarrow> 'b) stream" and f :: "('a \<Rightarrow> 'c) stream" and x
  show "pure (\<lambda>g f x. g (f x)) \<diamond> g \<diamond> f \<diamond> x = g \<diamond> (f \<diamond> x)"
    by (coinduction arbitrary: g f x) auto
next
  fix f :: "('a \<Rightarrow> 'b) stream" and x
  show "f \<diamond> pure x = pure (\<lambda>f. f x) \<diamond> f"
    by (coinduction arbitrary: f) auto
next
  fix f :: "('c \<Rightarrow> 'b \<Rightarrow> 'a) stream" and x y
  show "pure (\<lambda>f x y. f y x) \<diamond> f \<diamond> x \<diamond> y = f \<diamond> y \<diamond> x"
    by (coinduction arbitrary: f x y) auto
next
  fix x :: "'b stream" and y :: "'a stream"
  show "pure (\<lambda>x y. x) \<diamond> x \<diamond> y = x"
    by (coinduction arbitrary: x y) auto
next
  fix f :: "('b \<Rightarrow> 'b \<Rightarrow> 'a) stream" and x
  show "pure (\<lambda>f x. f x x) \<diamond> f \<diamond> x = f \<diamond> x \<diamond> x"
    by (coinduction arbitrary: f x) auto
qed

lemma smap_applicative[applicative_unfold]: "smap f x = pure f \<diamond> x"
unfolding ap_stream_def by (coinduction arbitrary: x) auto

lemma smap2_applicative[applicative_unfold]: "smap2 f x y = pure f \<diamond> x \<diamond> y"
unfolding ap_stream_def by (coinduction arbitrary: x y) auto


subsection \<open>Constants and operators\<close>

instantiation stream :: (zero) zero begin
definition [applicative_unfold]: "0 = sconst 0"
instance ..
end

instantiation stream :: (one) one begin
definition [applicative_unfold]: "1 = sconst 1"
instance ..
end

instantiation stream :: (plus) plus begin
definition [applicative_unfold]: "x + y = pure op + \<diamond> x \<diamond> (y :: 'a stream)"
instance ..
end

instantiation stream :: (minus) minus begin
definition [applicative_unfold]: "x - y = pure op - \<diamond> x \<diamond> (y :: 'a stream)"
instance ..
end

instantiation stream :: (uminus) uminus begin
definition [applicative_unfold stream]: "uminus = (op \<diamond> (pure uminus) :: 'a stream \<Rightarrow> 'a stream)"
instance ..
end

instantiation stream :: (times) times begin
definition [applicative_unfold]: "x * y = pure op * \<diamond> x \<diamond> (y :: 'a stream)"
instance ..
end

instance stream :: (Rings.dvd) Rings.dvd ..

instantiation stream :: ("Divides.div") "Divides.div" begin
definition [applicative_unfold]: "x div y = pure op div \<diamond> x \<diamond> (y :: 'a stream)"
definition [applicative_unfold]: "x mod y = pure op mod \<diamond> x \<diamond> (y :: 'a stream)"
instance ..
end


subsection \<open>Algebraic instances\<close>

instance stream :: (semigroup_add) semigroup_add
using add.assoc by intro_classes applicative_lifting

instance stream :: (ab_semigroup_add) ab_semigroup_add
using add.commute by intro_classes applicative_lifting

instance stream :: (semigroup_mult) semigroup_mult
using mult.assoc by intro_classes applicative_lifting

instance stream :: (ab_semigroup_mult) ab_semigroup_mult
using mult.commute by intro_classes applicative_lifting

instance stream :: (monoid_add) monoid_add
by intro_classes (applicative_lifting, simp)+

instance stream :: (comm_monoid_add) comm_monoid_add
by intro_classes (applicative_lifting, simp)

instance stream :: (comm_monoid_diff) comm_monoid_diff
by intro_classes (applicative_lifting, simp add: diff_diff_add)+

instance stream :: (monoid_mult) monoid_mult
by intro_classes (applicative_lifting, simp)+

instance stream :: (comm_monoid_mult) comm_monoid_mult
by intro_classes (applicative_lifting, simp)

(*
  Lifted properties which are more complex than plain equations are not handled by the
  applicative lifting tool.
*)

lemma plus_stream_shd: "shd (x + y) = shd x + shd y"
unfolding plus_stream_def by simp

lemma plus_stream_stl: "stl (x + y) = stl x + stl y"
unfolding plus_stream_def by simp

instance stream :: (cancel_semigroup_add) cancel_semigroup_add
proof
  fix a b c :: "'a stream"
  assume "a + b = a + c"
  thus "b = c" proof (coinduction arbitrary: a b c)
    case (Eq_stream a b c)
    hence "shd (a + b) = shd (a + c)" "stl (a + b) = stl (a + c)" by simp_all
    thus ?case by (auto simp add: plus_stream_shd plus_stream_stl)
  qed
next
  fix a b c :: "'a stream"
  assume "b + a = c + a"
  thus "b = c" proof (coinduction arbitrary: a b c)
    case (Eq_stream a b c)
    hence "shd (b + a) = shd (c + a)" "stl (b + a) = stl (c + a)" by simp_all
    thus ?case by (auto simp add: plus_stream_shd plus_stream_stl)
  qed
qed

instance stream :: (cancel_ab_semigroup_add) cancel_ab_semigroup_add
by intro_classes (applicative_lifting, simp add: diff_diff_eq)+

instance stream :: (cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance stream :: (group_add) group_add
by intro_classes (applicative_lifting, simp)+

instance stream :: (ab_group_add) ab_group_add
by intro_classes simp_all

instance stream :: (semiring) semiring
by intro_classes (applicative_lifting, simp add: ring_distribs)+

instance stream :: (mult_zero) mult_zero
by intro_classes (applicative_lifting, simp)+

instance stream :: (semiring_0) semiring_0 ..

instance stream :: (semiring_0_cancel) semiring_0_cancel ..

instance stream :: (comm_semiring) comm_semiring
by intro_classes(rule distrib_right)

instance stream :: (comm_semiring_0) comm_semiring_0 ..

instance stream :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

lemma pure_stream_inject [simp]: "sconst x = sconst y \<longleftrightarrow> x = y"
proof
  assume "sconst x = sconst y"
  hence "shd (sconst x) = shd (sconst y)" by simp
  thus "x = y" by simp
qed auto

instance stream :: (zero_neq_one) zero_neq_one
by intro_classes (applicative_unfold stream)

instance stream :: (semiring_1) semiring_1 ..

instance stream :: (comm_semiring_1) comm_semiring_1 ..

instance stream :: (semiring_1_cancel) semiring_1_cancel ..

instance stream :: (comm_semiring_1_cancel) comm_semiring_1_cancel ..

instance stream :: (ring) ring ..

instance stream :: (comm_ring) comm_ring ..

instance stream :: (ring_1) ring_1 ..

instance stream :: (comm_ring_1) comm_ring_1 ..

instance stream :: (numeral) numeral ..

instance stream :: (neg_numeral) neg_numeral ..

instance stream :: (semiring_numeral) semiring_numeral ..

lemma of_nat_stream: "of_nat n = sconst (of_nat n)"
proof (induction n)
  case 0 show ?case by (simp add: zero_stream_def del: id_apply)
next
  case (Suc n)
  have "1 + pure (of_nat n) = pure (1 + of_nat n)" by applicative_nf rule
  with Suc.IH show ?case by (simp del: id_apply)
qed

instance stream :: (semiring_char_0) semiring_char_0
by intro_classes (simp add: inj_on_def of_nat_stream)

instance stream :: (ring_char_0) ring_char_0 ..

end