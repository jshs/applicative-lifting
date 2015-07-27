theory Applicative
imports Fun
begin

ML_file "applicative.ML"

method_setup lifting_nf = {* Scan.succeed (fn ctxt =>
  SIMPLE_METHOD' (Applicative.lifting_nf_tac ctxt NONE)) *}

method_setup general_lifting = {* Scan.succeed (fn ctxt =>
  SIMPLE_METHOD' (Applicative.general_lifting_tac ctxt NONE)) *}

end
