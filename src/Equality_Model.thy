(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Deep embedding of term equality\<close>

theory Equality_Model
imports Beta_Eta
begin

type_synonym trm = dB

locale eq_model =
  fixes trm_eq :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "=\<^sub>\<Omega>" 50)
  assumes refl[simp, intro]: "t =\<^sub>\<Omega> t"
  assumes sym[sym]: "s =\<^sub>\<Omega> t \<Longrightarrow> t =\<^sub>\<Omega> s"
  assumes trans[trans]: "s =\<^sub>\<Omega> t \<Longrightarrow> t =\<^sub>\<Omega> u \<Longrightarrow> s =\<^sub>\<Omega> u"
  assumes abs: "s =\<^sub>\<Omega> t \<Longrightarrow> Abs s =\<^sub>\<Omega> Abs t"
  assumes appL: "s =\<^sub>\<Omega> t \<Longrightarrow> s \<degree> u =\<^sub>\<Omega> t \<degree> u"
  assumes appR: "s =\<^sub>\<Omega> t \<Longrightarrow> u \<degree> s =\<^sub>\<Omega> u \<degree> t"
  assumes beta: "Abs s \<degree> t =\<^sub>\<Omega> s[t/0]"
  assumes eta: "\<not>free t 0 \<Longrightarrow> Abs (t \<degree> Var 0) =\<^sub>\<Omega> t[dummy/0]"
begin

lemmas rules = refl sym trans abs appL appR beta eta

lemma equiv: "equivp op =\<^sub>\<Omega>"
using refl sym trans by (blast intro: equivpI reflpI sympI transpI)

lemma rtranclp_to_eq:
  assumes "R \<le> op =\<^sub>\<Omega>"
  shows "R\<^sup>*\<^sup>* \<le> op =\<^sub>\<Omega>"
proof (rule predicate2I)
  fix s t assume "R\<^sup>*\<^sup>* s t"
  then show "s =\<^sub>\<Omega> t" proof induction
    case base show "s =\<^sub>\<Omega> s" ..
    case (step u v)
      note `s =\<^sub>\<Omega> u`
      also from assms `R u v` have "u =\<^sub>\<Omega> v" ..
      finally show "s =\<^sub>\<Omega> v" .
  qed
qed

lemma beta_to_eq: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> s =\<^sub>\<Omega> t"
by (induction pred: beta) (auto intro: abs appL appR beta)

lemma beta_reds_to_eq: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> s =\<^sub>\<Omega> t"
using beta_to_eq rtranclp_to_eq by blast

lemma eta_to_eq: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> s =\<^sub>\<Omega> t"
by (induction pred: eta) (auto intro: abs appL appR eta)

lemma eta_reds_to_eq: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> s =\<^sub>\<Omega> t"
using eta_to_eq rtranclp_to_eq by blast

lemma beta_eta_to_eq: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> s =\<^sub>\<Omega> t"
using beta_to_eq eta_to_eq by blast

lemma beta_eta_reds_to_eq: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> s =\<^sub>\<Omega> t"
using rtranclp_to_eq[OF predicate2I, OF beta_eta_to_eq] ..

end

definition least_eq :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "=\<^sub>E" 50)
where "s =\<^sub>E t \<longleftrightarrow> (\<forall>R. eq_model R \<longrightarrow> R s t)"

interpretation least_eq: eq_model "op =\<^sub>E"
unfolding least_eq_def[abs_def]
by (unfold_locales) (iprover dest: eq_model.rules)+

lemma least_eq_induct[case_names refl sym trans abs appL appR beta eta, induct pred: least_eq]:
  assumes eq: "s =\<^sub>E t"
      and cases: "\<And>t. P t t"
            "\<And>s t. P s t \<Longrightarrow> P t s"
            "\<And>s t u. P s t \<Longrightarrow> P t u \<Longrightarrow> P s u"
            "\<And>s t. P s t \<Longrightarrow> P (Abs s) (Abs t)"
            "\<And>s t u. P s t \<Longrightarrow> P (s \<degree> u) (t \<degree> u)"
            "\<And>s t u. P s t \<Longrightarrow> P (u \<degree> s) (u \<degree> t)"
            "\<And>s t. P (Abs s \<degree> t) (s[t/0])"
            "\<And>t dummy. P (Abs (t \<degree> Var 0)) (t[dummy/0])"
  shows "P s t"
proof -
  from cases have "eq_model P" by (rule eq_model.intro)
  then show ?thesis using eq unfolding least_eq_def by blast
qed

end
