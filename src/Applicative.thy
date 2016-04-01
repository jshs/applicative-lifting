(* Author: Joshua Schneider, ETH Zurich *)

section \<open>Lifting with applicative functors\<close>

theory Applicative
imports Main
keywords "applicative" :: thy_goal and "print_applicative" :: diag
begin

context begin

subsection \<open>Combinators\<close>

qualified named_theorems combinator_unfold
qualified named_theorems combinator_repr
qualified named_theorems combinator_eq

private definition "I x \<equiv> x"
private definition "B g f x \<equiv> g (f x)"
private definition "C f x y \<equiv> f y x"
private definition "K x y \<equiv> x"
private definition "W f x \<equiv> f x x"
private definition "S f g x \<equiv> (f x) (g x)"
private definition "T' x f \<equiv> f x"

lemmas [abs_def, combinator_unfold] = I_def B_def C_def K_def W_def S_def T'_def
lemmas [combinator_repr] = combinator_unfold

(* TODO: complete set of equations *)
lemma [combinator_eq]: "B \<equiv> S (K S) K" unfolding combinator_unfold .
lemma [combinator_eq]: "C \<equiv> S (S (K (S (K S) K)) S) (K K)" unfolding combinator_unfold .
lemma [combinator_eq]: "I \<equiv> W K" unfolding combinator_unfold .
lemma [combinator_eq]: "I \<equiv> C K ()" unfolding combinator_unfold .
lemma [combinator_eq]: "S \<equiv> B (B W) (B B C)" unfolding combinator_unfold .
lemma [combinator_eq]: "W \<equiv> S S (S K)" unfolding combinator_unfold .
lemma [combinator_eq]: "T' \<equiv> C I" unfolding combinator_unfold .


subsection \<open>Proof automation\<close>

ML_file "applicative.ML"

local_setup \<open>Applicative.declare_combinators
 [("I", (@{thm I_def}, [])),
  ("B", (@{thm B_def}, [])),
  ("C", (@{thm C_def}, [])),
  ("K", (@{thm K_def}, [])),
  ("W", (@{thm W_def}, [])),
  ("S", (@{thm S_def}, [])),
  ("interchange", (@{thm T'_def}, [0]))]\<close>

method_setup applicative_unfold = {*
  Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.unfold_wrapper_tac ctxt opt_af)) *}
  "unfold to applicative expression"

method_setup applicative_fold = {*
  Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.fold_wrapper_tac ctxt opt_af)) *}
  "folding of applicative expression"

method_setup applicative_nf = {*
  Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.normalize_wrapper_tac ctxt opt_af)) *}
  "reduce equation using applicative normal form"

method_setup applicative_lifting = {*
  Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.lifting_wrapper_tac ctxt opt_af)) *}
  "reduce equation lifted with applicative functor"

ML {* Outer_Syntax.local_theory_to_proof @{command_keyword "applicative"}
  "register applicative functors"
  (Parse.binding --
    Scan.optional (@{keyword "("} |-- Parse.list Parse.short_ident --| @{keyword ")"}) [] --|
    @{keyword "for"} --| Parse.reserved "pure" --| @{keyword ":"} -- Parse.term --|
    Parse.reserved "ap" --| @{keyword ":"} -- Parse.term >>
    (fn (((name, combs), pure), ap) => Applicative.applicative_cmd name pure ap combs)) *}

ML {* Outer_Syntax.command @{command_keyword "print_applicative"}
  "print registered applicative functors"
  (Scan.succeed (Toplevel.keep (Applicative.print_afuns o Toplevel.context_of))) *}

attribute_setup applicative_unfold =
  {* Scan.lift (Scan.option Parse.xname >> Applicative.add_unfold_attrib) *}
  "register rules for unfolding to applicative expressions"

attribute_setup applicative_lifted =
  {* Scan.lift (Parse.xname >> Applicative.forward_lift_attrib) *}
  "lift an equation to an applicative functor"

end  (* context *)

subsection \<open>Overloaded applicative operators\<close>

consts pure :: "'a \<Rightarrow> 'b"

consts ap :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
locale applicative_syntax begin
  notation ap (infixl "\<diamondop>" 70)
end
hide_const (open) ap

end
