theory Tree_Traversal
imports
  "../src/Applicative_Functor"
begin

(*
  Inspired by G. Hutton and D. Fulger, "Reasoning About Effects: Seeing the Wood Through the Trees".
    In Proceedings of the Symposium on Trends in Functional Programming (Nijmegen, The Netherlands,
    2008).
*)

datatype 'a tree = Leaf 'a | Node "'a tree" "'a tree"

primrec labels :: "'a tree \<Rightarrow> 'a list"
where
    "labels (Leaf x) = [x]"
  | "labels (Node l r) = labels l @ labels r"

definition fresh :: "(nat, nat) state"
where "fresh n = (n, n + 1)"

primrec number_tree :: "'a tree \<Rightarrow> (nat tree, nat) state"
where
    "number_tree (Leaf _) = pure_state Leaf \<diamond> fresh"
  | "number_tree (Node l r) = pure_state Node \<diamond> number_tree l \<diamond> number_tree r"

primrec number_list :: "'a list \<Rightarrow> (nat list, nat) state"
where
    "number_list [] = pure_state []"
  | "number_list (x # xs) = pure_state op # \<diamond> fresh \<diamond> number_list xs"

lemma number_list_append: "number_list (a @ b) = pure_state op @ \<diamond> number_list a \<diamond> number_list b"
proof (induction a)
  case Nil
  have "number_list b = pure_state op @ \<diamond> pure_state [] \<diamond> number_list b"
    by applicative_lifting simp
  thus ?case by simp
next
  case (Cons a1 a2)
  let ?la2 = "number_list a2"
  let ?lb = "number_list b"
  have "pure_state op # \<diamond> fresh \<diamond> (pure_state op @ \<diamond> ?la2 \<diamond> ?lb) =
        pure_state op @ \<diamond> (pure_state op # \<diamond> fresh \<diamond> ?la2) \<diamond> ?lb"
    by applicative_lifting simp
  thus ?case using Cons.IH by simp
qed

lemma number_tree_list: "pure_state labels \<diamond> number_tree t = number_list (labels t)"
proof (induction t)
  case (Leaf x)
  have "pure_state labels \<diamond> (pure_state Leaf \<diamond> fresh) = pure_state op # \<diamond> fresh \<diamond> pure_state []"
    by applicative_lifting simp
  thus ?case by simp
next
  case (Node l r)
  let ?ll = "pure_state labels \<diamond> number_tree l"
  let ?lr = "pure_state labels \<diamond> number_tree r"
  have "pure_state labels \<diamond> (pure_state Node \<diamond> number_tree l \<diamond> number_tree r) =
        pure_state op @ \<diamond> ?ll \<diamond> ?lr"
    by applicative_lifting simp
  thus ?case using Node.IH by (simp add: number_list_append)
qed

end