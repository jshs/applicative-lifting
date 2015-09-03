theory Applicative
imports Fun
keywords "applicative" :: thy_goal
begin

ML_file "applicative.ML"

method_setup applicative_unfold ={*
  Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.unfold_wrapper_tac ctxt opt_af)) *}

method_setup applicative_fold = {*
  Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.fold_wrapper_tac ctxt opt_af)) *}

method_setup applicative_nf = {*
  Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.normalize_wrapper_tac ctxt opt_af)) *}

method_setup applicative_lifting = {*
  Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.lifting_wrapper_tac ctxt opt_af)) *}

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
