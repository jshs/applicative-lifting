theory Free_Idempotent_Monoid imports
  Main
begin



lemma wlog_linorder_le [consumes 0, case_names le symmetry]:
  assumes le: "\<And>a b :: 'a :: linorder. a \<le> b \<Longrightarrow> P a b"
  and sym: "\<And>a b. P b a \<Longrightarrow> P a b"
  shows "P a b"
proof(cases "a \<le> b")
  case True thus ?thesis by(rule le)
next
  case False
  hence "b \<le> a" by simp
  hence "P b a" by(rule le)
  thus ?thesis by(rule sym)
qed

text \<open>The free idempotent monoid does not have unique normal forms if we just use the cancellation law\<close>


inductive cancel1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where cancel1: "xs \<noteq> [] \<Longrightarrow> cancel1 (gs @ xs @ xs @ gs') (gs @ xs @ gs')"

lemma cancel1_append_same1: 
  assumes "cancel1 xs ys"
  shows "cancel1 (zs @ xs) (zs @ ys)"
using assms
proof cases
  case (cancel1 ys gs gs')
  from \<open>ys \<noteq> []\<close> have "cancel1 ((zs @ gs) @ ys @ ys @ gs') ((zs @ gs) @ ys @ gs')" ..
  with cancel1 show ?thesis by simp
qed

lemma cancel1_append_same2: "cancel1 xs ys \<Longrightarrow> cancel1 (xs @ zs) (ys @ zs)"
by(cases rule: cancel1.cases)(auto intro: cancel1.intros)

lemma cancel1_same:
  assumes "xs \<noteq> []"
  shows "cancel1 (xs @ xs) xs"
proof -
  have "cancel1 ([] @ xs @ xs @ []) ([] @ xs @ [])" using assms ..
  thus ?thesis by simp
qed

definition sclp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where "sclp r x y \<longleftrightarrow> r x y \<or> r y x"

lemma sclpI [simp, intro?]: 
  shows sclpI1: "r x y \<Longrightarrow> sclp r x y"
  and sclpI2: "r y x \<Longrightarrow> sclp r x y"
by(simp_all add: sclp_def)

lemma sclpE:
  assumes "sclp r x y"
  obtains (base) "r x y" | (sym) "r y x"
using assms by(auto simp add: sclp_def)

abbreviation eq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where "eq \<equiv> (sclp cancel1)\<^sup>*\<^sup>*"

lemma eq_sym: "eq x y \<Longrightarrow> eq y x"
by(induction rule: rtranclp_induct)(auto intro: sclpI converse_rtranclp_into_rtranclp elim!: sclpE)

lemma equivp_eq: "equivp eq"
by(intro equivpI reflpI sympI transpI)(auto intro: eq_sym)

lemma eq_append_same1: "eq xs' ys' \<Longrightarrow> eq (xs @ xs') (xs @ ys')"
by(induction rule: rtranclp_induct)(auto intro: cancel1_append_same1 rtranclp.rtrancl_into_rtrancl sclpI elim!: sclpE)

lemma append_eq_cong: "\<lbrakk>eq xs ys; eq xs' ys'\<rbrakk> \<Longrightarrow> eq (xs @ xs') (ys @ ys')"
by(induction rule: rtranclp_induct)(auto intro: eq_append_same1 rtranclp.rtrancl_into_rtrancl cancel1_append_same2 elim!: sclpE intro: sclpI)

quotient_type 'a fim = "'a list" / eq
by(rule equivp_eq)

instantiation fim :: (type) monoid_add begin
lift_definition zero_fim :: "'a fim" is "[]" .
lift_definition plus_fim :: "'a fim \<Rightarrow> 'a fim \<Rightarrow> 'a fim" is "op @" by(rule append_eq_cong)
instance by(intro_classes; transfer; simp)
end

lemma plus_idem_fim [simp]: fixes x :: "'a fim" shows "x + x = x"
proof transfer
  fix xs :: "'a list"
  show "eq (xs @ xs) xs"
  proof(cases "xs = []")
    case False thus ?thesis using cancel1_same[of xs] by(auto intro: sclpI1)
  qed simp
qed



type_synonym ('a, 'b) af = "'a fim \<times> 'b"

definition pure :: "'b \<Rightarrow> ('a, 'b) af"
where "pure x = (0, x)"

fun ap :: "('a, 'b \<Rightarrow> 'c) af \<Rightarrow> ('a, 'b) af \<Rightarrow> ('a, 'c) af" (infixl "\<diamond>" 60)
where "ap (u, f) (v, x) = (u + v, f x)"

lemma af_identity: "pure id \<diamond> x = x"
unfolding pure_def by(cases x) simp

lemma af_homomorphism: "pure f \<diamond> pure x = pure (f x)"
unfolding pure_def by simp

lemma af_composition: "\<And>g f x. pure comp \<diamond> g \<diamond> f \<diamond> x = g \<diamond> (f \<diamond> x)"
unfolding pure_def by(clarsimp simp add: add_ac)

lemma af_interchange: "f \<diamond> pure x = pure (\<lambda>g. g x) \<diamond> f"
unfolding pure_def by(cases f) simp

definition W :: "('x, ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) af"
where "W = pure (\<lambda>f x. f x x)"

lemma ap_W: "W \<diamond> f \<diamond> x = f \<diamond> x \<diamond> x"
unfolding W_def pure_def
apply(cases f)
apply(cases x)
apply(rename_tac u f' v g')
apply(simp add: add_ac)
done

text \<open> There is no combinator H because fim is the free idempotent monoid\<close>

end
