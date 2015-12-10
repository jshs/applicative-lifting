(* Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Tree traversals following Gibbons and Bird \cite{backwards}\<close>

theory Tree_Traversal2 imports
  Applicative_State
  "~~/src/HOL/Library/Stream"
begin

text \<open>Dual version of an applicative functor with effects composed in the opposite order\<close>

typedef 'a dual = "UNIV :: 'a set" morphisms un_B B by blast
setup_lifting type_definition_dual

lift_definition pure_dual :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b dual"
is "\<lambda>pure. pure" .

lift_definition ap_dual :: "(('a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b) \<Rightarrow> 'af1) \<Rightarrow> ('af1 \<Rightarrow> 'af3 \<Rightarrow> 'af13) \<Rightarrow> ('af13 \<Rightarrow> 'af2 \<Rightarrow> 'af) \<Rightarrow> 'af2 dual \<Rightarrow> 'af3 dual \<Rightarrow> 'af dual"
is "\<lambda>pure ap1 ap2 f x. ap2 (ap1 (pure (\<lambda>x f. f x)) x) f" .

type_synonym ('a, 's) state_rev = "('a, 's) state dual"

definition pure_state_rev :: "'a \<Rightarrow> ('a, 's) state_rev"
where "pure_state_rev = pure_dual pure_state"

definition ap_state_rev :: "('a \<Rightarrow> 'b, 's) state_rev \<Rightarrow> ('a, 's) state_rev \<Rightarrow> ('b, 's) state_rev"
where "ap_state_rev = ap_dual pure_state ap_state ap_state"

adhoc_overloading Applicative.pure pure_state_rev
adhoc_overloading Applicative.ap ap_state_rev

applicative state_rev
for
  pure: pure_state_rev
  ap: ap_state_rev
unfolding pure_state_rev_def ap_state_rev_def by(transfer, applicative_nf, rule refl)+


type_synonym ('a, 's) state_rev_rev = "('a, 's) state_rev dual"

definition pure_state_rev_rev :: "'a \<Rightarrow> ('a, 's) state_rev_rev"
where "pure_state_rev_rev = pure_dual pure_state_rev"

definition ap_state_rev_rev :: "('a \<Rightarrow> 'b, 's) state_rev_rev \<Rightarrow> ('a, 's) state_rev_rev \<Rightarrow> ('b, 's) state_rev_rev"
where "ap_state_rev_rev = ap_dual pure_state_rev ap_state_rev ap_state_rev"

adhoc_overloading Applicative.pure pure_state_rev_rev
adhoc_overloading Applicative.ap ap_state_rev_rev

applicative state_rev_rev
for
  pure: pure_state_rev_rev
  ap: ap_state_rev_rev
unfolding pure_state_rev_rev_def ap_state_rev_rev_def by(transfer, applicative_nf, rule refl)+


context begin interpretation applicative_syntax .
lemma ap_state_rev_B: "B f \<diamond> B x = B (pure_state (\<lambda>x f. f x) \<diamond> x \<diamond> f)"
unfolding ap_state_rev_def by(fact ap_dual.abs_eq)

lemma ap_state_rev_pure_B: "pure f \<diamond> B x = B (pure_state f \<diamond> x)"
unfolding ap_state_rev_def pure_state_rev_def
by transfer(applicative_nf, rule refl)

lemma ap_state_rev_rev_B: "B f \<diamond> B x = B (pure_state_rev (\<lambda>x f. f x) \<diamond> x \<diamond> f)"
unfolding ap_state_rev_rev_def by(fact ap_dual.abs_eq)

lemma ap_state_rev_rev_pure_B: "pure f \<diamond> B x = B (pure_state_rev f \<diamond> x)"
unfolding ap_state_rev_rev_def pure_state_rev_rev_def
by transfer(applicative_nf, rule refl)

end







interpretation applicative_syntax .
adhoc_overloading Applicative.pure pure_state

(* Using the monad is ugly, but I do not (yet) see a way around it if we want to talk about Kleisli composition *)

definition bind_state :: "('s \<Rightarrow> 'a \<times> 's) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'b \<times> 's) \<Rightarrow> 's \<Rightarrow> 'b \<times> 's"
where "bind_state x f s = (let (a, s') = x s in f a s')"

lemma bind_state_assoc: "bind_state (bind_state x f) g = bind_state x (\<lambda>x. bind_state (f x) g)"
by(simp add: fun_eq_iff bind_state_def split_def Let_def)

lemma bind_state_return1: "bind_state (Pair x) f = f x"
by(simp add: bind_state_def fun_eq_iff)

lemma ap_conv_bind_state: "ap_state f x = bind_state f (\<lambda>f. bind_state x (Pair \<circ> f))"
by(simp add: ap_state_def bind_state_def Let_def split_def o_def fun_eq_iff)

lemma ap_pure_bind_state: "pure x \<diamond> bind_state y f = bind_state y (op \<diamond> (pure x) \<circ> f)"
by(simp add: ap_conv_bind_state bind_state_return1 bind_state_assoc o_def)

definition kleisli_state :: "('b \<Rightarrow> ('c, 's) state) \<Rightarrow> ('a \<Rightarrow> ('b, 's) state) \<Rightarrow> 'a \<Rightarrow> ('c, 's) state" (infixl "\<bullet>" 55)
where [simp]: "kleisli_state g f a = bind_state (f a) g"




datatype 'a tree = Leaf 'a | Node "'a tree" "'a tree"

definition fetch :: "('a, 'a stream) state"
where "fetch s = (shd s, stl s)"

primrec traverse :: "('a \<Rightarrow> ('b, 's) state) \<Rightarrow> 'a tree \<Rightarrow> ('b tree, 's) state"
where
  "traverse f (Leaf x) = pure Leaf \<diamond> f x"
| "traverse f (Node l r) = pure Node \<diamond> traverse f l \<diamond> traverse f r"

text \<open>As we cannot abstract over the applicative functor in definitions, we define
  traversal on the transformed applicative function once again.\<close>
primrec traverse_rev :: "('a \<Rightarrow> ('b, 's) state_rev) \<Rightarrow> 'a tree \<Rightarrow> ('b tree, 's) state_rev"
where
  "traverse_rev f (Leaf x) = pure Leaf \<diamond> f x"
| "traverse_rev f (Node l r) = pure Node \<diamond> traverse_rev f l \<diamond> traverse_rev f r"

definition recurse :: "('a \<Rightarrow> ('b, 's) state) \<Rightarrow> 'a tree \<Rightarrow> ('b tree, 's) state"
where "recurse f = un_B \<circ> traverse_rev (B \<circ> f)"

lemma recurse_Leaf: "recurse f (Leaf x) = pure Leaf \<diamond> f x"
unfolding recurse_def traverse_rev.simps o_def ap_state_rev_pure_B
by(simp add: B_inverse)

lemma recurse_Node:
  "recurse f (Node l r) = pure (\<lambda>r l. Node l r) \<diamond> recurse f r \<diamond> recurse f l"
proof -
  have "recurse f (Node l r) = un_B (traverse_rev (B \<circ> f) (Node l r))"
    by(simp add: recurse_def)
  also have "\<dots> = un_B (pure Node \<diamond> traverse_rev (B \<circ> f) l \<diamond> traverse_rev (B \<circ> f) r)"
    by simp
  also have "\<dots> = un_B (B (pure Node) \<diamond> B (recurse f l) \<diamond> B (recurse f r))"
    by(simp add: un_B_inverse recurse_def pure_state_rev_def pure_dual_def)
  also have "\<dots> = un_B (B (pure (\<lambda>x f. f x) \<diamond> recurse f r \<diamond> (pure (\<lambda>x f. f x) \<diamond> recurse f l \<diamond> pure Node)))"
    by(simp add: ap_state_rev_B)
  also have "\<dots> = pure (\<lambda>x f. f x) \<diamond> recurse f r \<diamond> (pure (\<lambda>x f. f x) \<diamond> recurse f l \<diamond> pure Node)"
    by(simp add: B_inverse)
  also have "\<dots> = pure (\<lambda>r l. Node l r) \<diamond> recurse f r \<diamond> recurse f l"
    -- \<open>These are 13 steps in \cite{backwards}\<close>
    by(applicative_nf) simp
  finally show ?thesis .
qed

lemma traverse_pure: "traverse pure t = pure t"
proof(induction t)
  case (Leaf x)
  show "traverse pure (Leaf x) = pure (Leaf x)"
    (* FIXME: "show ?case" does not work because "?case" is eta-expanded *)
    unfolding traverse.simps by applicative_nf simp
next
  case (Node l r)
  show "traverse (pure :: 'b \<Rightarrow> 'a \<Rightarrow> _) (Node l r) = pure (Node l r)"
    (* FIXME: "show ?case" does not work because "?case" is eta-expanded *)
    unfolding traverse.simps Node.IH by applicative_nf simp
qed


text \<open>@{term "B \<circ> B"} is an idiom morphism\<close>

lemma B_pure: "pure x = B (pure_state x)"
unfolding pure_state_rev_def by transfer simp

lemma BB_pure: "pure x = B (B (pure x))"
unfolding pure_state_rev_rev_def B_pure[symmetric] by transfer(rule refl)

lemma BB_ap: "B (B f) \<diamond> B (B x) = B (B (f \<diamond> x))"
proof -
  have "B (B f) \<diamond> B (B x) = B (B (pure (\<lambda>x f. f x) \<diamond> f \<diamond> (pure (\<lambda>x f. f x) \<diamond> x \<diamond> pure (\<lambda>x f. f x))))"
    (is "_ = B (B ?exp)")
    unfolding ap_state_rev_rev_B B_pure ap_state_rev_B ..
  also have "?exp = f \<diamond> x" -- \<open>This takes 15 steps in \cite{backwards}.\<close>
    by(applicative_nf)(rule refl)
  finally show ?thesis .
qed

primrec traverse_rev_rev :: "('a \<Rightarrow> ('b, 's) state_rev_rev) \<Rightarrow> 'a tree \<Rightarrow> ('b tree, 's) state_rev_rev"
where
  "traverse_rev_rev f (Leaf x) = pure Leaf \<diamond> f x"
| "traverse_rev_rev f (Node l r) = pure Node \<diamond> traverse_rev_rev f l \<diamond> traverse_rev_rev f r"

definition recurse_rev :: "('a \<Rightarrow> ('b, 's) state_rev) \<Rightarrow> 'a tree \<Rightarrow> ('b tree, 's) state_rev"
where "recurse_rev f = un_B \<circ> traverse_rev_rev (B \<circ> f)"

lemma traverse_B_B: "traverse_rev_rev (B \<circ> B \<circ> f) = B \<circ> B \<circ> traverse f" (is "?lhs = ?rhs")
proof
  fix t
  show "?lhs t = ?rhs t" by induction(simp_all add: BB_pure BB_ap)
qed

lemma traverse_recurse: "traverse f = un_B \<circ> recurse_rev (B \<circ> f)" (is "?lhs = ?rhs")
proof -
  have "?lhs = un_B \<circ> un_B \<circ> B \<circ> B \<circ> traverse f" by(simp add: o_def B_inverse)
  also have "\<dots> = un_B \<circ> un_B \<circ> traverse_rev_rev (B \<circ> B \<circ> f)" unfolding traverse_B_B by(simp add: o_assoc)
  also have "\<dots> = ?rhs" by(simp add: recurse_rev_def o_assoc)
  finally show ?thesis .
qed



lemma recurse_traverse:
  assumes "f \<bullet> g = pure"
  shows "recurse f \<bullet> traverse g = pure"
-- \<open>Gibbons and Bird impose this as an additional requirement on traversals, but they write
  that they have not found a way to derive this fact from other axioms. So we prove it directly.\<close>
(* Unfortunately, this is where the monad comes back *)
proof
  fix t
  from assms have *: "\<And>x. bind_state (g x) f = Pair x" by(simp add: fun_eq_iff)
  hence **: "\<And>x h. bind_state (g x) (\<lambda>x. bind_state (f x) h) = h x"
    by(fold bind_state_assoc)(simp add: bind_state_return1)
  show "(recurse f \<bullet> traverse g) t = pure t" unfolding kleisli_state_def
  proof(induction t)
    case (Leaf x)
    show ?case
      by(simp add: ap_conv_bind_state bind_state_assoc bind_state_return1 recurse_Leaf **)
  next
    case (Node l r)
    show ?case
      by(simp add: ap_conv_bind_state bind_state_assoc bind_state_return1 recurse_Node)
        (simp add: bind_state_assoc[symmetric] Node.IH bind_state_return1)
  qed
qed

text \<open>Apply traversals to labelling\<close>

definition strip :: "'a \<times> 'b \<Rightarrow> ('a, 'b stream) state"
where "strip = (\<lambda>(a, b) s. (a, SCons b s))"

definition adorn :: "'a \<Rightarrow> ('a \<times> 'b, 'b stream) state"
where "adorn a = pure (Pair a) \<diamond> fetch"

abbreviation label :: "'a tree \<Rightarrow> (('a \<times> 'b) tree, 'b stream) state"
where "label \<equiv> traverse adorn"

abbreviation unlabel :: "('a \<times> 'b) tree \<Rightarrow> ('a tree, 'b stream) state"
where "unlabel \<equiv> recurse strip"

lemma strip_adorn: "strip \<bullet> adorn = pure"
by(simp add: strip_def adorn_def fun_eq_iff fetch_def[abs_def] bind_state_def ap_conv_bind_state)

lemma unlabel_label: "unlabel \<bullet> label = pure"
by(rule recurse_traverse)(rule strip_adorn)

end