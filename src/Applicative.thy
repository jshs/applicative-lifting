theory Applicative
imports Fun
keywords "applicative" :: thy_goal
begin

ML_file "applicative.ML"

(* TODO parse optional functor name *)

method_setup applicative_unfold = {* Scan.succeed (fn ctxt =>
  SIMPLE_METHOD' (Applicative.unfold_wrapper_tac ctxt NONE)) *}

method_setup applicative_fold = {* Scan.succeed (fn ctxt =>
  SIMPLE_METHOD' (Applicative.fold_wrapper_tac ctxt NONE)) *}

method_setup applicative_nf = {* Scan.succeed (fn ctxt =>
  SIMPLE_METHOD' (Applicative.normalize_wrapper_tac ctxt NONE)) *}

method_setup applicative_lifting = {* Scan.succeed (fn ctxt =>
  SIMPLE_METHOD' (Applicative.lifting_wrapper_tac ctxt NONE)) *}

ML {* Outer_Syntax.local_theory_to_proof @{command_keyword "applicative"}
  "register applicative functors"
  (Parse.binding --
    Scan.optional (@{keyword "("} |-- Parse.list Parse.short_ident --| @{keyword ")"}) [] --|
    @{keyword "for"} --| Parse.reserved "pure" --| @{keyword ":"} -- Parse.term --|
    Parse.reserved "ap" --| @{keyword ":"} -- Parse.term >>
    (fn (((name, combs), pure), ap) => Applicative.applicative_cmd name pure ap combs)) *}

attribute_setup applicative_unfold =
  {* Scan.lift (Scan.option Parse.xname >> Applicative.add_unfold_attrib) *}

end
