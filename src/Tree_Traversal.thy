(* Author: Joshua Schneider, ETH Zurich
   Author: Andreas Lochbihler, ETH Zurich *)

theory Tree_Traversal
imports
  Applicative_State
begin

(*
  Inspired by G. Hutton and D. Fulger, "Reasoning About Effects: Seeing the Wood Through the Trees".
    In Proceedings of the Symposium on Trends in Functional Programming (Nijmegen, The Netherlands,
    2008).
*)

interpretation applicative_syntax .
adhoc_overloading Applicative.pure pure_state


datatype 'a tree = Leaf 'a | Node "'a tree" "'a tree"

primrec labels :: "'a tree \<Rightarrow> 'a list"
where
    "labels (Leaf x) = [x]"
  | "labels (Node l r) = labels l @ labels r"

locale labelling =
  fixes fresh :: "('x, 's) state"
begin

primrec label_tree :: "'a tree \<Rightarrow> ('x tree, 's) state"
where
    "label_tree (Leaf _) = pure Leaf \<diamond> fresh"
  | "label_tree (Node l r) = pure Node \<diamond> label_tree l \<diamond> label_tree r"

primrec label_list :: "'a list \<Rightarrow> ('x list, 's) state"
where
    "label_list [] = pure []"
  | "label_list (x # xs) = pure (op #) \<diamond> fresh \<diamond> label_list xs"

lemma label_append: "label_list (a @ b) = pure (op @) \<diamond> label_list a \<diamond> label_list b"
proof (induction a)
  case Nil
  show "label_list ([] @ b) = pure op @ \<diamond> label_list [] \<diamond> label_list b"
    (* FIXME: "show ?case" does not work because "?case" is eta-expanded *)
    unfolding append.simps label_list.simps by applicative_lifting simp
next
  case (Cons a1 a2)
  show "label_list ((a1 # a2) @ b) = pure op @ \<diamond> label_list (a1 # a2) \<diamond> label_list b"
    (* FIXME: "show ?case" does not work because "?case" is eta-expanded *)
    unfolding append.simps label_list.simps Cons.IH
    by applicative_lifting simp
qed

lemma label_tree_list: "pure labels \<diamond> label_tree t = label_list (labels t)"
proof (induction t)
  case (Leaf x)
  show "pure labels \<diamond> label_tree (Leaf x) = label_list (labels (Leaf x))"
    (* FIXME: "show ?case" does not work because "?case" is eta-expanded *)
    unfolding label_tree.simps labels.simps label_list.simps
    by applicative_lifting simp
next
  case (Node l r)
  show "pure labels \<diamond> label_tree (Node l r) = label_list (labels (Node l r))"
    (* FIXME: "show ?case" does not work because "?case" is eta-expanded *)
    unfolding label_tree.simps labels.simps label_append Node.IH[symmetric]
    by applicative_lifting simp
qed

end

end