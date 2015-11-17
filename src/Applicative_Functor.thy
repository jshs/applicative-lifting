section \<open>Common applicative functors\<close>

theory Applicative_Functor
imports
  Main
  "~~/src/Tools/Adhoc_Overloading"
  Applicative
begin

subsection \<open>Overloaded applicative operators\<close>

consts
  pure :: "'a \<Rightarrow> 'b"
  ap :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<diamond>" 70)


subsection \<open>Environment functor\<close>

definition "const x = (\<lambda>_. x)"
definition "apf x y = (\<lambda>z. x z (y z))"

adhoc_overloading pure const
adhoc_overloading ap apf

lemmas [simp] = const_def apf_def

applicative env (C, K, W)
for
  pure: const
  ap: apf
by simp_all


subsection \<open>Option\<close>

fun ap_option :: "('a \<Rightarrow> 'b) option \<Rightarrow> 'a option \<Rightarrow> 'b option"
where
    "ap_option (Some f) (Some x) = Some (f x)"
  | "ap_option _ _ = None"

adhoc_overloading pure Some
adhoc_overloading ap ap_option

lemma some_ap_option: "ap_option (Some f) x = map_option f x"
by (cases x) simp_all

lemma ap_some_option: "ap_option f (Some x) = map_option (\<lambda>g. g x) f"
by (cases f) simp_all

applicative option (C, W)
for
  pure: Some
  ap: ap_option
proof -
  fix x :: "'a option"
  show "pure (\<lambda>x. x) \<diamond> x = x" by (cases x) simp_all
next
  fix g :: "('c \<Rightarrow> 'b) option" and f :: "('a \<Rightarrow> 'c) option" and x
  show "pure (\<lambda>g f x. g (f x)) \<diamond> g \<diamond> f \<diamond> x = g \<diamond> (f \<diamond> x)"
  by (cases g, simp, cases f, simp, cases x, simp_all)
next
  fix f :: "('c \<Rightarrow> 'b \<Rightarrow> 'a) option" and x y
  show "pure (\<lambda>f x y. f y x) \<diamond> f \<diamond> x \<diamond> y = f \<diamond> y \<diamond> x"
  by (cases f, simp, cases x, simp, cases y, simp_all)
next
  fix f :: "('b \<Rightarrow> 'b \<Rightarrow> 'a) option" and x
  show "pure (\<lambda>f x. f x x) \<diamond> f \<diamond> x = f \<diamond> x \<diamond> x"
  by (cases f, simp, cases x, simp_all)
qed (simp_all add: some_ap_option ap_some_option)


subsection \<open>Sum types\<close>

text \<open>
  There are several ways to define an applicative functor based on sum types. First, we can choose
  whether the left or the right type is fixed. Both cases are isomorphic, of course. Next, what
  should happen if two values of the fixed type are combined? The corresponding operator must be
  associative, or the idiom laws don't hold true.

  We focus on the cases where the right type is fixed. We define two concrete functors: One based
  on Haskell's \textsf{Either} datatype, which prefers the value of the left operand, and a generic
  one using the @{class semigroup_add} class. Only the former lifts the \textbf{W} combinator,
  though.
\<close>

fun ap_sum :: "('e \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> 'b) + 'e \<Rightarrow> 'a + 'e \<Rightarrow> 'b + 'e"
where
    "ap_sum _ (Inl f) (Inl x) = Inl (f x)"
  | "ap_sum _ (Inl _) (Inr e) = Inr e"
  | "ap_sum _ (Inr e) (Inl _) = Inr e"
  | "ap_sum c (Inr e1) (Inr e2) = Inr (c e1 e2)"

abbreviation "ap_either \<equiv> ap_sum const"
abbreviation "ap_plus \<equiv> ap_sum (plus :: 'a::semigroup_add \<Rightarrow> _)"

adhoc_overloading pure Inl
adhoc_overloading ap ap_either (* ap_plus *)

lemma ap_sum_id: "ap_sum c (Inl id) x = x"
by (cases x) simp_all

lemma ap_sum_ichng: "ap_sum c f (Inl x) = ap_sum c (Inl (\<lambda>f. f x)) f"
by (cases f) simp_all

lemma (in semigroup) ap_sum_comp:
  "ap_sum f (ap_sum f (ap_sum f (Inl op o) h) g) x = ap_sum f h (ap_sum f g x)"
apply (cases h, cases g, cases x)
apply simp_all
apply (cases x)
apply simp_all
apply (cases g, cases x)
apply simp_all
apply (cases x)
apply simp_all
apply (rule local.assoc)
done

interpretation const: semigroup const
by unfold_locales simp

applicative either (W)
for
  pure: Inl
  ap: ap_either
using
  ap_sum_id[simplified id_def]
  ap_sum_ichng
  const.ap_sum_comp[simplified comp_def[abs_def]]
proof -
  fix f :: "('b \<Rightarrow> 'b \<Rightarrow> 'a) + 'c" and x
  show "pure (\<lambda>f x. f x x) \<diamond> f \<diamond> x = f \<diamond> x \<diamond> x"
    apply (cases f, cases x)
    apply simp_all
    apply (cases x)
    apply simp_all
    done
qed auto

applicative semigroup_sum
for
  pure: "Inl :: (_ \<Rightarrow> _ + 'e::semigroup_add)"
  ap: ap_plus
using
  ap_sum_id[simplified id_def]
  ap_sum_ichng
  add.ap_sum_comp[simplified comp_def[abs_def]]
by auto


subsection \<open>Set with cross product\<close>

definition ap_set :: "('a \<Rightarrow> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set"
  where "ap_set F X = {f x | f x. f \<in> F \<and> x \<in> X}"

adhoc_overloading ap ap_set

applicative set (C)
for
  pure: "\<lambda>x. {x}"
  ap: ap_set
unfolding single_def ap_set_def
by fastforce+


subsection \<open>Lists\<close>

definition "ap_list fs xs = List.bind fs (\<lambda>f. List.bind xs (\<lambda>x. [f x]))"

adhoc_overloading ap ap_list

lemma Nil_ap[simp]: "ap_list [] xs = []"
unfolding ap_list_def by simp

lemma ap_Nil[simp]: "ap_list fs [] = []"
unfolding ap_list_def by (induction fs) simp_all

lemma cons_ap_list: "(f # fs) \<diamond> xs = map f xs @ fs \<diamond> xs"
unfolding ap_list_def by (induction xs) simp_all

lemma append_ap_distrib: "(fs @ gs) \<diamond> xs = fs \<diamond> xs @ gs \<diamond> xs"
unfolding ap_list_def by (induction fs) simp_all

applicative list
for
  pure: "\<lambda>x. [x]"
  ap: ap_list
proof -
  fix x :: "'a list"
  show "[\<lambda>x. x] \<diamond> x = x" unfolding ap_list_def by (induction x) simp_all
next
  fix g :: "('c \<Rightarrow> 'b) list" and f :: "('a \<Rightarrow> 'c) list" and x
  let ?B = "\<lambda>g f x. g (f x)"
  show "[?B] \<diamond> g \<diamond> f \<diamond> x = g \<diamond> (f \<diamond> x)"
    proof (induction g)
      case Nil show ?case by simp
    next
      case (Cons g gs)
      have g_comp: "[?B g] \<diamond> f \<diamond> x = [g] \<diamond> (f \<diamond> x)"
        proof (induction f)
          case Nil show ?case by simp
        next
          case (Cons f fs)
          have "[?B g] \<diamond> (f # fs) \<diamond> x = [g] \<diamond> ([f] \<diamond> x) @ [?B g] \<diamond> fs \<diamond> x"
            by (simp add: cons_ap_list)
          also have "... = [g] \<diamond> ([f] \<diamond> x) @ [g] \<diamond> (fs \<diamond> x)" using Cons.IH ..
          also have "... = [g] \<diamond> ((f # fs) \<diamond> x)" by (simp add: cons_ap_list)
          finally show ?case .
        qed
      have "[?B] \<diamond> (g # gs) \<diamond> f \<diamond> x = [?B g] \<diamond> f \<diamond> x @ [?B] \<diamond> gs \<diamond> f \<diamond> x"
        by (simp add: cons_ap_list append_ap_distrib)
      also have "... = [g] \<diamond> (f \<diamond> x) @ gs \<diamond> (f \<diamond> x)" using g_comp Cons.IH by simp
      also have "... = (g # gs) \<diamond> (f \<diamond> x)" by (simp add: cons_ap_list)
      finally show ?case .
    qed
next
  fix f :: "('a \<Rightarrow> 'b) list" and x
  show "f \<diamond> [x] = [\<lambda>f. f x] \<diamond> f" unfolding ap_list_def by simp
qed (simp add: cons_ap_list)


subsection \<open>State monad\<close>

definition "ap_state f x = (\<lambda>s. case f s of (g, s') \<Rightarrow> case x s' of (y, s'') \<Rightarrow> (g y, s''))"

adhoc_overloading pure Pair
adhoc_overloading ap ap_state

applicative state
for
  pure: Pair
  ap: "ap_state :: ('s \<Rightarrow> ('a \<Rightarrow> 'b) \<times> 's) \<Rightarrow> ('s \<Rightarrow> 'a \<times> 's) \<Rightarrow> 's \<Rightarrow> 'b \<times> 's"
unfolding ap_state_def
by (auto split: split_split)

end