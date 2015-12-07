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

definition [applicative_unfold]: "liftSt1 f x = Pair f \<diamond> x"
definition [applicative_unfold]: "liftSt2 f x y = Pair f \<diamond> x \<diamond> y"

definition "fresh n = (n, n + 1)"

primrec number_tree :: "'a tree \<Rightarrow> nat \<Rightarrow> nat tree \<times> nat"
where
    "number_tree (Leaf _) = liftSt1 Leaf fresh"
  | "number_tree (Node l r) = liftSt2 Node (number_tree l) (number_tree r)"

primrec number_list :: "'a list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat"
where
    "number_list [] = pure []"
  | "number_list (x # xs) = liftSt2 (op #) fresh (number_list xs)"

lemma label_append: "number_list (a @ b) = liftSt2 (op @) (number_list a) (number_list b)"
proof (induction a)
  case Nil
  have "number_list b = liftSt2 (op @) (pure []) (number_list b)"
    by applicative_lifting simp
  thus ?case by simp
next
  case (Cons a1 a2)
  let ?la2 = "number_list a2"
  let ?lb = "number_list b"
  have "liftSt2 (op #) fresh (liftSt2 (op @) ?la2 ?lb) = liftSt2 (op @) (liftSt2 (op #) fresh ?la2) ?lb"
    by applicative_lifting simp
  thus ?case using Cons.IH by simp
qed

lemma number_tree_list: "liftSt1 labels (number_tree t) = number_list (labels t)"
proof (induction t)
  case (Leaf x)
  have "liftSt1 labels (liftSt1 Leaf fresh) = liftSt2 (op #) fresh (Pair [])"
    by applicative_lifting simp
  thus ?case by simp
next
  case (Node l r)
  let ?ll = "liftSt1 labels (number_tree l)"
  let ?lr = "liftSt1 labels (number_tree r)"
  have "liftSt1 labels (liftSt2 Node (number_tree l) (number_tree r)) = liftSt2 (op @) ?ll ?lr"
    by applicative_lifting simp
  thus ?case using Node.IH by (simp add: label_append)
qed

experiment begin
lemmas [simp] = liftSt1_def liftSt2_def

lemma "Pair labels \<diamond> number_tree t = number_list (labels t)"
proof (induction t)
  case (Leaf x)
  have "Pair labels \<diamond> (Pair Leaf \<diamond> fresh) = Pair op # \<diamond> fresh \<diamond> Pair []"
    by applicative_lifting simp
  thus ?case by simp
next
  case (Node l r)
  let ?ll = "Pair labels \<diamond> number_tree l"
  let ?lr = "Pair labels \<diamond> number_tree r"
  have "Pair labels \<diamond> (Pair Node \<diamond> number_tree l \<diamond> number_tree r) = Pair op @ \<diamond> ?ll \<diamond> ?lr"
    by applicative_lifting simp
  thus ?case using Node.IH by (simp add: label_append)
qed

end

end