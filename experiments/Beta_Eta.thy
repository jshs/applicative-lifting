theory Beta_Eta
imports "~~/src/HOL/Proofs/Lambda/Eta" Joinable
begin

section \<open>Combined beta and eta reduction of lambda terms\<close>

subsection \<open>Reduction\<close>

abbreviation beta_eta :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infixl "\<rightarrow>\<^sub>\<beta>\<^sub>\<eta>" 50)
where
  "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta> t \<equiv> s \<rightarrow>\<^sub>\<beta> t \<or> s \<rightarrow>\<^sub>\<eta> t"

abbreviation beta_eta_reds :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infixl "\<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>*" 50)
where
  "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<equiv> (beta_eta)\<^sup>*\<^sup>* s t"

lemma beta_eta_appL: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* s' \<Longrightarrow> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* s' \<degree> t"
by (induction set: rtranclp) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma beta_eta_appR: "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t' \<Longrightarrow> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* s \<degree> t'"
by (induction set: rtranclp) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma beta_eta_abs[intro]: "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t' \<Longrightarrow> Abs t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Abs t'"
by (induction set: rtranclp) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma beta_into_beta_eta: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t"
by (auto intro: rtranclp_mono[THEN predicate2D])

lemma eta_into_beta_eta: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t"
by (auto intro: rtranclp_mono[THEN predicate2D])

lemma beta_eta_confluent: "Commutation.confluent beta_eta"
proof -
  have "beta_eta = sup beta eta" by blast
  with Eta.confluent_beta_eta show ?thesis by simp
qed

lemma beta_eta_confluent_rel: "Joinable.confluent {(s, t). s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t}"
using beta_eta_confluent
unfolding diamond_def commute_def square_def
by (blast intro!: confluentI)


subsection \<open>Equivalence\<close>

definition term_equiv :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infixl "\<leftrightarrow>" 50)
where
  "term_equiv = joinablep beta_eta_reds"

lemma red_into_equiv[elim]: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> s \<leftrightarrow> t"
unfolding term_equiv_def
by (blast intro: reflp_le_joinablep[THEN predicate2D] reflpI)

lemma term_refl[simp, intro]: "t \<leftrightarrow> t"
unfolding term_equiv_def by (blast intro: joinablep_refl reflpI)

lemma term_sym[sym]: "(s \<leftrightarrow> t) \<Longrightarrow> (t \<leftrightarrow> s)"
unfolding term_equiv_def by (rule joinable_sym[to_pred])

lemma term_trans[trans]: "s \<leftrightarrow> t \<Longrightarrow> t \<leftrightarrow> u \<Longrightarrow> s \<leftrightarrow> u"
unfolding term_equiv_def
using trans_joinable[to_pred] trans_rtrancl[to_pred] beta_eta_confluent_rel
by (blast elim: transpE)

lemma equiv_appL: "s \<leftrightarrow> s' \<Longrightarrow> s \<degree> t \<leftrightarrow> s' \<degree> t"
unfolding term_equiv_def using beta_eta_appL
by (iprover intro: joinable_subst[to_pred])

lemma equiv_appR: "t \<leftrightarrow> t' \<Longrightarrow> s \<degree> t \<leftrightarrow> s \<degree> t'"
unfolding term_equiv_def using beta_eta_appR
by (iprover intro: joinable_subst[to_pred])

lemma equiv_abs[intro]: "t \<leftrightarrow> t' \<Longrightarrow> Abs t \<leftrightarrow> Abs t'"
unfolding term_equiv_def using beta_eta_abs
by (iprover intro: joinable_subst[to_pred])

lemma equiv_sym_red: "term_equiv = (sup beta_eta beta_eta\<inverse>\<inverse>)\<^sup>*\<^sup>*"
unfolding term_equiv_def
using beta_eta_confluent_rel
by (rule joinable_eq_rtscl[to_pred])

end