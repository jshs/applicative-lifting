(* Author:     Andreas Lochbihler, ETH Zurich
   Author:     Joshua Schneider, ETH Zurich
*)

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

lemma ap_stream_id: "pure (\<lambda>x. x) \<diamondop> x = x"
by (coinduction arbitrary: x) simp

lemma ap_stream_homo: "pure f \<diamondop> pure x = pure (f x)"
by coinduction simp

lemma ap_stream_interchange: "f \<diamondop> pure x = pure (\<lambda>f. f x) \<diamondop> f"
by (coinduction arbitrary: f) auto

lemma ap_stream_composition: "pure (\<lambda>g f x. g (f x)) \<diamondop> g \<diamondop> f \<diamondop> x = g \<diamondop> (f \<diamondop> x)"
by (coinduction arbitrary: g f x) auto

applicative stream (S, K)
for
  pure: sconst
  ap: ap_stream
proof -
  fix g :: "('b \<Rightarrow> 'a \<Rightarrow> 'c) stream" and f x
  show "pure (\<lambda>g f x. g x (f x)) \<diamondop> g \<diamondop> f \<diamondop> x = g \<diamondop> x \<diamondop> (f \<diamondop> x)"
    by (coinduction arbitrary: g f x) auto
next
  fix x :: "'b stream" and y :: "'a stream"
  show "pure (\<lambda>x y. x) \<diamondop> x \<diamondop> y = x"
    by (coinduction arbitrary: x y) auto
qed(rule ap_stream_homo ap_stream_composition)+

lemma smap_applicative[applicative_unfold]: "smap f x = pure f \<diamondop> x"
unfolding ap_stream_def by (coinduction arbitrary: x) auto

lemma smap2_applicative[applicative_unfold]: "smap2 f x y = pure f \<diamondop> x \<diamondop> y"
unfolding ap_stream_def by (coinduction arbitrary: x y) auto

end

end