theory NSA_Test
imports "~~/src/HOL/NSA/StarDef" "../src/Applicative"
begin

lemma star_interchange: "f \<star> star_of x = star_of (\<lambda>f. f x) \<star> f"
proof -
  have "\<forall>f x. f \<star> x = star_of (\<lambda>x f. f x) \<star> x \<star> f" by transfer simp
  hence "\<forall>f x. f \<star> star_of x = star_of (\<lambda>x f. f x) \<star> star_of x \<star> f" by blast
  hence "\<forall>f x. f \<star> star_of x = star_of (\<lambda>f. f x) \<star> f" by (simp only: Ifun_star_of)
  thus ?thesis by auto
qed

applicative star (C, K, W)
for
  pure: star_of
  ap: Ifun
apply (transfer, simp)
apply (transfer, simp)
apply (rule Ifun_star_of)
apply (rule star_interchange)
apply (transfer, simp)+
done

end