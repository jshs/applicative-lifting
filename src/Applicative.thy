(* Author: Joshua Schneider, ETH Zurich *)

section \<open>Lifting with applicative functors\<close>

theory Applicative
imports Main
keywords "applicative" :: thy_goal and "print_applicative" :: diag
begin

lemma arg1_cong: "x = y \<Longrightarrow> f x z = f y z"
by (rule arg_cong)

lemma rel_fun_eqI: "(\<And>x. B (f x) (g x)) \<Longrightarrow> rel_fun (op =) B f g"
by blast


context begin

subsection \<open>Combinators\<close>

private named_theorems combinator_unfold
private named_theorems combinator_repr

private definition "B g f x \<equiv> g (f x)"
private definition "C f x y \<equiv> f y x"
private definition "I x \<equiv> x"
private definition "K x y \<equiv> x"
private definition "S f g x \<equiv> (f x) (g x)"
private definition "T x f \<equiv> f x"
private definition "W f x \<equiv> f x x"

lemmas [abs_def, combinator_unfold] = B_def C_def I_def K_def S_def T_def W_def
lemmas [combinator_repr] = combinator_unfold

private definition "cpair \<equiv> Pair"
private definition "cuncurry \<equiv> case_prod"

private lemma uncurry_pair: "cuncurry f (cpair x y) = f x y"
unfolding cpair_def cuncurry_def by simp


subsection \<open>Proof automation\<close>

ML_file "applicative.ML"

local_setup \<open>Applicative.setup_combinators
 [("B", @{thm B_def}),
  ("C", @{thm C_def}),
  ("I", @{thm I_def}),
  ("K", @{thm K_def}),
  ("S", @{thm S_def}),
  ("T", @{thm T_def}),
  ("W", @{thm W_def})]\<close>

attribute_setup combinator_eq =
  \<open>Scan.lift (Scan.option (Args.$$$ "weak" |--
    Scan.optional (Args.colon |-- Scan.repeat1 Args.name) []) >>
    Applicative.combinator_eq_attrib)\<close>

(* TODO: complete set of equations *)
lemma [combinator_eq]: "B \<equiv> S (K S) K" unfolding combinator_unfold .
lemma [combinator_eq]: "C \<equiv> S (S (K (S (K S) K)) S) (K K)" unfolding combinator_unfold .
lemma [combinator_eq]: "I \<equiv> W K" unfolding combinator_unfold .
lemma [combinator_eq]: "I \<equiv> C K ()" unfolding combinator_unfold .
lemma [combinator_eq]: "S \<equiv> B (B W) (B B C)" unfolding combinator_unfold .
lemma [combinator_eq]: "T \<equiv> C I" unfolding combinator_unfold .
lemma [combinator_eq]: "W \<equiv> S S (S K)" unfolding combinator_unfold .

lemma [combinator_eq weak: C]:
  "C \<equiv> C (B B (B B (B W (C (B C (B (B B) (C B (cuncurry (K I))))) (cuncurry K))))) cpair"
unfolding combinator_unfold uncurry_pair .

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
    Scan.optional (@{keyword "("} |-- Parse.list Parse.short_ident --| @{keyword ")"}) [] --
    (@{keyword "for"} |-- Parse.reserved "pure" |-- @{keyword ":"} |-- Parse.term) --
    (Parse.reserved "ap" |-- @{keyword ":"} |-- Parse.term) --
    Scan.option (Parse.reserved "rel" |-- @{keyword ":"} |-- Parse.term) >>
    Applicative.applicative_cmd) *}

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
