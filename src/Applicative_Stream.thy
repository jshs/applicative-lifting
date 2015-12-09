subsection \<open>Streams as an applicative functor\<close>

theory Applicative_Stream imports
  Applicative
  "~~/src/Tools/Adhoc_Overloading"
  "~~/src/HOL/Library/Stream"
begin

primcorec ap_stream :: "('a \<Rightarrow> 'b) stream \<Rightarrow> 'a stream \<Rightarrow> 'b stream"
where
    "shd (ap_stream f x) = shd f (shd x)"
  | "stl (ap_stream f x) = ap_stream (stl f) (stl x)"

adhoc_overloading Applicative.pure sconst
adhoc_overloading Applicative.ap ap_stream

context begin interpretation applicative_syntax .

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

end

end