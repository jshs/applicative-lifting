theory Applicative
imports Fun
keywords "applicative" :: thy_goal
begin

ML_file "applicative.ML"

method_setup lifting_nf = {* Scan.succeed (fn ctxt =>
  SIMPLE_METHOD' (Applicative.lifting_nf_tac ctxt NONE)) *}

method_setup general_lifting = {* Scan.succeed (fn ctxt =>
  SIMPLE_METHOD' (Applicative.general_lifting_tac ctxt NONE)) *}

ML {* Outer_Syntax.local_theory_to_proof @{command_keyword "applicative"}
  "register applicative functors"
  (Scan.option Parse.name --
    Scan.optional (@{keyword "("} |-- Parse.list Parse.short_ident --| @{keyword ")"}) [] --|
    @{keyword "for"} --| Parse.reserved "pure" --| @{keyword ":"} -- Parse.term --|
    Parse.reserved "ap" --| @{keyword ":"} -- Parse.term >>
    (fn (((_, combs), pure), ap) => Applicative.applicative_cmd "" pure ap combs)) *}

end
