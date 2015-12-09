(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>State monad\<close>

theory Applicative_State imports
  Applicative
  "~~/src/Tools/Adhoc_Overloading"
begin

type_synonym ('a, 's) state = "'s \<Rightarrow> 'a \<times> 's"

definition "ap_state f x = (\<lambda>s. case f s of (g, s') \<Rightarrow> case x s' of (y, s'') \<Rightarrow> (g y, s''))"

adhoc_overloading Applicative.ap ap_state

applicative state
for
  pure: Pair
  ap: "ap_state :: ('a \<Rightarrow> 'b, 's) state \<Rightarrow> ('a, 's) state \<Rightarrow> ('b, 's) state"
unfolding ap_state_def
by (auto split: split_split)

end