theory Extensionality imports Pure begin

lemma extensionality:
      assumes "!!x. f x == g x"
      shows "f == g"
    using assms[abs_def] .

end