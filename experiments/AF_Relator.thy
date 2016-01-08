theory AF_Relator imports 
  "$AFP/Applicative_Lifting/Abstract_AF"
  "~~/src/HOL/Library/Rewrite"
begin

interpretation applicative_syntax .

section \<open>Alternative set of applicative operations\<close>

definition unit :: "unit af"
where unit_conv [applicative_unfold]: "unit = pure ()"

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a af \<Rightarrow> 'b af"
where map_conv [applicative_unfold]: "map f x = pure f \<diamond> x"

definition zip :: "'a af \<Rightarrow> 'b af \<Rightarrow> ('a \<times> 'b) af"
where zip_conv [applicative_unfold]: "zip x y = pure Pair \<diamond> x \<diamond> y"

lemma pure_conv: "pure x = map (\<lambda>_. x) unit"
by applicative_nf simp

lemma ap_conv: "f \<diamond> x = map (\<lambda>(f, x). f x) (zip f x)"
by applicative_nf simp

lemma map_id: "map (\<lambda>a. a) x = x"
by applicative_nf simp

lemma map_comp: "map f (map g x) = map (f \<circ> g) x"
by applicative_nf simp

lemma map_zip: "map (map_prod f g) (zip x y) = zip (map f x) (map g y)"
by applicative_nf simp

lemma map_snd: "map snd (zip unit x) = x"
by applicative_nf simp

lemma map_fst: "map fst (zip x unit) = x"
by applicative_nf simp

lemma map_assoc: "zip (zip a b) c = map (\<lambda>(a, (b, c)). ((a, b), c)) (zip a (zip b c))"
by applicative_nf simp

section \<open>The set function\<close>

consts set :: "'a af \<Rightarrow> 'a set"
axiomatization
  where map_cong: "\<And>f g x. (\<forall>a\<in>set x. f a = g a) \<Longrightarrow> map f x = map g x"
  and set_natural: "\<And>f x. set (map f x) \<subseteq> f ` set x"
  -- \<open>This is only half of the usual naturality. Does this direction follow already from @{thm map_cong}?\<close>

lemma set_pure_subset: "set (pure x) \<subseteq> {x}"
proof
  fix a
  assume "a \<in> set (pure x)"
  with set_natural have "a \<in> (\<lambda>_. x) ` set unit" unfolding pure_conv ..
  hence "a = x" by blast
  then show "a \<in> {x}" by simp
qed

abbreviation pred :: "('a \<Rightarrow> bool) \<Rightarrow> 'a af \<Rightarrow> bool"
where "pred P x \<equiv> \<forall>a\<in>set x. P a"

(*axiomatization where set_unit: "() \<in> set unit" This forbids applicative functors without elements (phantom type variables)*)


section \<open>Relator\<close>

definition rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a af \<Rightarrow> 'b af \<Rightarrow> bool"
where "rel P x y \<longleftrightarrow> (\<exists>z. (\<forall>(a, b)\<in>set z. P a b) \<and> map fst z = x \<and> map snd z = y)"

lemma rel_mono:
  assumes "P \<le> Q"
  shows "rel P \<le> rel Q"
proof(intro le_funI le_boolI) 
  fix x y
  assume "rel P x y"
  then obtain z where "\<forall>(a, b)\<in>set z. P a b" and x: "map fst z = x" and y: "map snd z = y"
    unfolding rel_def by blast
  from assms this(1) have "\<forall>(a, b)\<in>set z. Q a b" unfolding le_fun_def le_bool_def by blast
  with x y show "rel Q x y" unfolding rel_def by blast
qed

corollary rel_mono':
  "\<lbrakk> rel P x y; \<And>a b. P a b \<Longrightarrow> Q a b \<rbrakk> \<Longrightarrow> rel Q x y"
using rel_mono unfolding le_fun_def le_bool_def by blast

lemma rel_reflI:
  assumes "\<forall>a\<in>set x. P a a"
  shows "rel P x x"
proof -
  let ?z = "map (\<lambda>a. (a, a)) x"
  have "\<forall>(a, b)\<in>set ?z. P a b" using assms set_natural[where f="\<lambda>a. (a, a)"] by blast
  moreover have "map fst ?z = x" unfolding map_comp o_def fst_conv map_id ..
  moreover have "map snd ?z = x" unfolding map_comp o_def snd_conv map_id ..
  ultimately show "rel P x x" unfolding rel_def by blast
qed

lemma rel_eq: "rel (op =) = op ="
proof(intro ext iffI)
  fix x y :: "'a af"
  assume *: "x = y"
  show "rel op = x y" unfolding * by(rule rel_reflI) blast
next
  fix x y :: "'a af"
  assume "rel op = x y"
  then obtain z where z: "\<forall>(a, b)\<in>set z. a = b" and x: "map fst z = x" and y: "map snd z = y"
    unfolding rel_def by blast
  show "x = y" using z unfolding x[symmetric] y[symmetric] split_def
    by(rule map_cong)
qed

lemma rel_pureI:
  assumes "P x y"
  shows "rel P (pure x) (pure y)"
proof -
  let ?z = "pure (x, y)"
  { fix a b 
    assume "(a, b) \<in> set (pure (x, y))"
    with set_pure_subset have "(a, b) \<in> {(x, y)}" ..
    with assms have "P a b" by simp }
  moreover have "map fst ?z = pure x" unfolding pure_conv map_comp o_def fst_conv ..
  moreover have "map snd ?z = pure y" unfolding pure_conv map_comp o_def snd_conv ..
  ultimately show ?thesis unfolding rel_def by blast
qed

lemma rel_Grp:
  "rel (BNF_Def.Grp P f) = BNF_Def.Grp (Collect (pred (\<lambda>x. x \<in> P))) (map f)"
unfolding Grp_def
apply(rule ext iffI)+

 apply(subst (asm) rel_def)
 apply(erule exE conjE)+
 apply clarify
 apply(rule conjI)
  apply(subst map_comp)
  apply(rule map_cong)
  apply fastforce
 apply clarify
 apply(drule subsetD[OF set_natural])
 apply clarify
 apply(drule (1) bspec)
 apply(simp add: Grp_def)

apply(subst rel_def)
apply clarify
apply(rename_tac x y)
apply(rule_tac x="map (\<lambda>x. (x, f x)) x" in exI)
apply(intro conjI)
  apply clarify
  apply(drule subsetD[OF set_natural])
  apply blast
 apply(subst map_comp)
 apply(simp add: o_def map_id)
apply(subst map_comp)
apply(simp add: o_def map_id)
done

lemma rel_conversep: "rel P\<inverse>\<inverse> = (rel P)\<inverse>\<inverse>"
apply(rule ext iffI)+
 apply(clarsimp simp add: rel_def)
 apply(rule_tac x="map (\<lambda>(x, y). (y, x)) z" in exI)
 apply(intro conjI)
   apply(clarify)
   apply(drule subsetD[OF set_natural])
   apply fastforce
  apply(subst map_comp)
  apply(simp add: o_def split_def map_id)
 apply(subst map_comp)
 apply(simp add: o_def split_def map_id)
apply(clarsimp simp add: rel_def)
apply(rule_tac x="map (\<lambda>(x, y). (y, x)) z" in exI)
apply(intro conjI)
  apply(clarify)
  apply(drule subsetD[OF set_natural])
  apply fastforce
 apply(subst map_comp)
 apply(simp add: o_def split_def map_id)
apply(subst map_comp)
apply(simp add: o_def split_def map_id)
done

text \<open>We say that two effects are compatible iff they can be related ignoring their elements,
  i.e., they have the same structure or effects\<close>

abbreviation compat :: "'a af \<Rightarrow> 'b af \<Rightarrow> bool"
where "compat \<equiv> rel (\<lambda>_ _. True)"

text \<open>
  What is the difference between structure and effect? Is effect just more general than structure
  and structure means that we can swap effects?

  Examples:
  - set, pmf, option, llist are commutative, they have structure
  - state, reader, writer monads are not commutative, so this feels more like an effect. 
\<close>

lemma compat_self: "compat x x"
by(rule rel_reflI) blast


axiomatization
  where set_zip_subset: "\<And>x y. set (zip x y) \<subseteq> set x \<times> set y"
  -- \<open>We should not require equality here.
    For example on coinductive lists with the canonical zip, only the subset relation holds.\<close>
  -- \<open>TODO: Does this somehow follow from the applicative axioms and the previous set axioms?\<close>

lemma rel_apI:
  assumes fg: "rel (rel_fun P Q) f g"
  and xy: "rel P x y"
  shows "rel Q (f \<diamond> x) (g \<diamond> y)"
proof -
  from fg obtain fg where fg: "\<forall>(a, b)\<in>set fg. rel_fun P Q a b"
    and f: "map fst fg = f"
    and g: "map snd fg = g"
    unfolding rel_def by blast
  from xy obtain xy where xy: "\<forall>(a, b)\<in>set xy. P a b"
    and x: "map fst xy = x"
    and y: "map snd xy = y"
    unfolding rel_def by blast
  let ?z = "map (\<lambda>((f, g), (x, y)). (f x, g y)) (zip fg xy)"
  { have "map fst ?z = map (\<lambda>(f, x). f x) (map (map_prod fst fst) (zip fg xy))"
      unfolding map_comp by(simp add: o_def split_def)
    also have "\<dots> = map (\<lambda>(f, x). f x) (zip (map fst fg) (map fst xy))"
      unfolding map_zip ..
    also have "\<dots> = map (\<lambda>(f, x). f x) (zip f x)" unfolding f x ..
    also have "\<dots> = f \<diamond> x" unfolding ap_conv ..
    finally have "map fst ?z = f \<diamond> x" . }
  moreover
  { have "map snd ?z = map (\<lambda>(g, y). g y) (map (map_prod snd snd) (zip fg xy))"
      unfolding map_comp by(simp add: o_def split_def)
    also have "\<dots> = map (\<lambda>(g, y). g y) (zip (map snd fg) (map snd xy))"
      unfolding map_zip ..
    also have "\<dots> = map (\<lambda>(g, y). g y) (zip g y)" unfolding g y ..
    also have "\<dots> = g \<diamond> y" unfolding ap_conv ..
    finally have "map snd ?z = g \<diamond> y" . }
  moreover
  { fix a b
    assume "(a, b) \<in> set ?z"
    with set_natural have "(a, b) \<in> (\<lambda>((f, g), (x, y)). (f x, g y)) ` set (zip fg xy)" ..
    then obtain f' g' x' y'
      where a: "a = f' x'" and b: "b = g' y'"
      and "((f', g'), (x', y')) \<in> set (zip fg xy)" by auto
    from set_zip_subset this(3) have "((f', g'), (x', y')) \<in> set fg \<times> set xy" ..
    hence f'g': "(f', g') \<in> set fg" and x'y': "(x', y') \<in> set xy" by blast+
    from f'g' fg have "rel_fun P Q f' g'" by blast
    moreover from x'y' xy have "P x' y'" by blast
    ultimately have "Q (f' x') (g' y')" by(rule rel_funD)
    hence "Q a b" unfolding a b . }
  ultimately show ?thesis unfolding rel_def by blast
qed

subsection \<open>Lifting of relations\<close>

text \<open>
  With @{const rel}, we can generalise lifting to arbitrary binary relations on the base level.
  1. First, normalise both idiomatic expressions according to the normalisation laws available.
  Both idiomatic expressions should be pure applied to the same list of impure terms.
  2. Use @{thm [source] rel_apI} to strip off the impure terms with reflexivity on the argument.
  3. Use @{thm [source] rel_pureI} to strip off pure.
  4. Use @{thm [source] rel_funI} to get back the universal quantifiers.

  Equality is just a special case due to @{thm [source] rel_eq}.
\<close>

lemma lifting_relations_example:
  assumes "\<forall>x y. R (f x y) (g x y)"
  shows "rel R (pure f \<diamond> x \<diamond> y) (pure g \<diamond> x \<diamond> y)"
apply(rule rel_apI[where P="op ="])+
  apply(rule rel_pureI)
  apply(rule rel_funI)+
  apply clarify
  apply(simp add: assms)
 apply(rule rel_reflI; blast)
apply(rule rel_reflI; blast)
done

text \<open>
  We can add compatible effects that the pure function ignores.
\<close>

lemma rel_addI: -- \<open>add at the end\<close>
  assumes "rel P f g"
  and "compat x y"
  shows "rel P (pure (\<lambda>x y. x) \<diamond> f \<diamond> x) (pure (\<lambda>x y. x) \<diamond> g \<diamond> y)"
using _ assms(2)
apply(rule rel_apI)
using _ assms(1)
apply(rule rel_apI)
apply(rule rel_pureI)
apply(rule rel_funI)+
apply assumption
done

lemma rel_addI': -- \<open>add at the front\<close>
  assumes "rel P x y"
  and "compat f g"
  shows "rel P (pure (\<lambda>x y. y) \<diamond> f \<diamond> x) (pure (\<lambda>x y. y) \<diamond> g \<diamond> y)"
using _ assms(1)
apply(rule rel_apI)
using _ assms(2)
apply(rule rel_apI)
apply(rule rel_pureI)
apply(rule rel_funI)+
apply assumption
done


subsection \<open>Lifting implication\<close>

text \<open>
  Implication lifting does not hold in general.
  Consider integer addition modulo 2 over the set functor.
  We have @{lemma "rel_set (\<lambda>x y :: int. x = (y + 1) mod 2) {0,1} {0,1}" by(auto simp add: rel_set_def)}
  and @{lemma "\<forall>x :: int. x = (x + 1) mod 2 \<longrightarrow> False" by arith},
  yet @{lemma "~ rel_set (\<lambda>x y. False) {0,1} {0,1}" by(auto simp add: rel_set_def)}.

  The problem is that @{thm rel_reflI} is only sufficient, not necessary. Among others, 
  @{term "rel P x y"} says that each element of @{term x} is related to an element in @{term y}
  and vice versa. However, if @{term "y = x"}, there is no requirement that every element be
  related to itself.

  Therefore, we need more machinery. Initially, suppose that @{const rel} preserves weak pullbacks,
  i.e., it distributes over composition and commutes with @{const map}.
\<close>

axiomatization
  where rel_compp: "rel (P OO Q) = rel P OO rel Q"
  -- \<open>preservation of weak pullbacks required for @{const rel} distributing over @{const map} (naturality of @{const rel})}\<close>

lemma rel_map1 [unfolded vimage2p_def id_apply]: "rel P (map f x) y = rel (BNF_Def.vimage2p f id P) x y"
apply(tactic \<open>BNF_Def_Tactics.mk_rel_map0_tac @{context} 1 @{thm rel_compp} @{thm rel_conversep} @{thm rel_Grp} @{thm map_id}\<close>)
apply(simp add: Grp_def)
apply(rule iffI)
 apply(rule relcomppI)
  apply(rule refl)
 apply(erule relcomppI)
 apply(simp add: map_id id_def)
apply clarify
apply(simp add: map_id id_def)
done

lemma rel_map2 [unfolded vimage2p_def id_apply]: "rel P x (map f y) = rel (BNF_Def.vimage2p id f P) x y"
apply(tactic \<open>BNF_Def_Tactics.mk_rel_map0_tac @{context} 1 @{thm rel_compp} @{thm rel_conversep} @{thm rel_Grp} @{thm map_id}\<close>)
apply(simp add: Grp_def)
apply(rule iffI)
 apply(rule relcomppI)
  apply(rule refl)
 apply(rule relcomppI)
  apply(simp add: map_id id_def)
 apply simp
apply clarify
apply(simp add: map_id id_def)
done

lemma rel_map:
  "rel P (map f x) (map g y) \<longleftrightarrow> rel (\<lambda>x y. P (f x) (g y)) x y"
unfolding rel_map1 rel_map2 ..

text \<open>
  Now, we can also lift conditional equations and relations.
  However, as we cannot double effects yet, we must require that the idiomatic expressions
  (assumption and conclusion) of the left-hand side use the same variables in the same order,
  and similarly for the right-hand side, and both sides do not share variables.

  1. If necessary, expand the assumed relation with the additional variables.
  2. Zip all impure arguments into one for each side of assumed and stated relation.
  3. Apply @{thm "rel_mono"}.
\<close>

lemma lift_implication:
  assumes base: "\<forall>a b c d e f''. P (f a b) (g d e) \<longrightarrow> Q (f' a b c) (g' d e f'')"
  and assm: "rel P (pure f \<diamond> x \<diamond> y) (pure g \<diamond> u \<diamond> v)"
  and zw: "compat z w" -- \<open>We can always add compatible effects at the end\<close>
  -- \<open>we could relax compatibility such that z and w have compatible effects given the effects of x and y -- how to express this?\<close>
  shows "rel Q (pure f' \<diamond> x \<diamond> y \<diamond> z) (pure g' \<diamond> u \<diamond> v \<diamond> w)"
proof -
  from assm have "rel P (pure (\<lambda>x y. x) \<diamond> (pure f \<diamond> x \<diamond> y) \<diamond> z) (pure (\<lambda>x y. x) \<diamond> (pure g \<diamond> u \<diamond> v) \<diamond> w)"
    using zw by(rule rel_addI)
  also have "pure (\<lambda>x y. x) \<diamond> (pure f \<diamond> x \<diamond> y) \<diamond> z = pure (\<lambda>x y z. f x y) \<diamond> x \<diamond> y \<diamond> z"
    unfolding af_composition[symmetric] af_homomorphism o_def ..
  also have "\<dots> = map (\<lambda>(x, y, z). f x y) (zip x (zip y z))"
    unfolding zip_conv map_conv af_composition[symmetric] af_homomorphism o_def prod.simps
    by(subst af_interchange)(simp add: af_composition[symmetric] af_homomorphism o_def)
  also have "pure (\<lambda>x y. x) \<diamond> (pure g \<diamond> u \<diamond> v) \<diamond> w = pure (\<lambda>x y z. g x y) \<diamond> u \<diamond> v \<diamond> w"
    unfolding af_composition[symmetric] af_homomorphism o_def ..
  also have "\<dots> = map (\<lambda>(x, y, z). g x y) (zip u (zip v w))"
    unfolding zip_conv map_conv af_composition[symmetric] af_homomorphism o_def prod.simps
    by(subst af_interchange)(simp add: af_composition[symmetric] af_homomorphism o_def)
  finally have "rel (\<lambda>(x, y, z) (x', y', z'). P (f x y) (g x' y')) (zip x (zip y z)) (zip u (zip v w))"
    unfolding rel_map by(simp add: split_def)
  hence "rel (\<lambda>(x, y, z) (x', y', z'). Q (f' x y z) (g' x' y' z')) (zip x (zip y z)) (zip u (zip v w))"
    apply(rule rel_mono') -- \<open>This is the key step: exploit monotonicity\<close>
    using base by auto
  hence "rel Q (map (\<lambda>(x, y, z). f' x y z) (zip x (zip y z))) (map (\<lambda>(x, y, z). g' x y z) (zip u (zip v w)))"
    unfolding rel_map by(simp add: split_def)
  also have "map (\<lambda>(x, y, z). f' x y z) (zip x (zip y z)) = pure f' \<diamond> x \<diamond> y \<diamond> z"
    unfolding zip_conv map_conv af_composition[symmetric] af_homomorphism
    by(subst af_interchange)(simp add: af_composition[symmetric] af_homomorphism o_def)
  also have "map (\<lambda>(x, y, z). g' x y z) (zip u (zip v w)) = pure g' \<diamond> u \<diamond> v \<diamond> w"
    unfolding zip_conv map_conv af_composition[symmetric] af_homomorphism
    by(subst af_interchange)(simp add: af_composition[symmetric] af_homomorphism o_def)
  finally show ?thesis .
qed

text \<open>
  Intuition for the requirement for distinct variables on the left and on the right in the case of equality:
  The relator does not ensure that in the reflexive case, every element is related to itself.
  Hinze's lifting relies on @{thm rel_reflI} plus equality being reflexive,
  but @{thm rel_reflI} is only sufficient, not necessary. This means that equality between
  lifted terms does not imply point-wise equality between terms.
\<close>



subsection \<open>Doubling effects\<close>

text \<open> If we can double effects, products are unique. \<close>

axiomatization W :: "(('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) af"
where ap_W: "W \<diamond> f \<diamond> x = f \<diamond> x \<diamond> x"
  and W_def: "W = pure (\<lambda>f x. f x x)"

lemma product_unique:
   assumes x: "map fst z = x"
   and y: "map snd z = y"
   shows "z = zip x y"
proof -
  have "zip x y = zip (map fst z) (map snd z)" by(simp add: assms)
  also have "\<dots> = map (map_prod fst snd) (zip z z)" unfolding map_zip ..
  also have "zip z z = W \<diamond> pure Pair \<diamond> z" unfolding zip_conv ap_W af_identity ..
  also have "\<dots> = pure (\<lambda>W. W Pair) \<diamond> W \<diamond> z"
    apply(subst af_interchange) ..
  also have "map (map_prod fst snd) \<dots> = pure (\<lambda>W z. map_prod fst snd (W Pair z)) \<diamond> W \<diamond> z"
    unfolding map_conv af_composition[symmetric] af_homomorphism o_def ..
  also have "\<dots> = z" unfolding W_def af_homomorphism by(simp add: af_identity[unfolded id_def])
  finally show ?thesis by simp
qed

text \<open>
  Unfortunately, doubling adjacent effects is not enough for lifting with shared variables.
  We also want to be able to duplicate effects with other stuff in between.
\<close>

axiomatization H :: "(('a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c) af"
where ap_H: "H \<diamond> f \<diamond> x \<diamond> y = f \<diamond> x \<diamond> y \<diamond> x"
  and H_def: "H = pure (\<lambda>f x y. f x y x)"
  -- \<open>Hummingbird combinator taken from "To Mock a Mockingbird"\<close>

text \<open>If there is H, then there is W\<close>

lemma "W \<diamond> f \<diamond> x = H \<diamond> (pure (\<lambda>f x y. f x) \<diamond> f) \<diamond> x \<diamond> pure id"
unfolding H_def W_def
apply(subst af_interchange)
apply(subst af_composition[symmetric])
apply(subst af_homomorphism)
apply(subst af_composition[symmetric])
apply(subst af_homomorphism)+
apply(subst af_composition[symmetric])
apply(subst af_homomorphism)+
apply(simp add: o_def)
done

text \<open>Lifting with shared variables\<close>

axiomatization where set_natural2: "\<And>f x. set (map f x) \<supseteq> f ` set x"
  -- \<open>This is is the other half to @{thm set_natural}\<close>

text \<open>
  General approach:
  1. obtain the product from the assumption
  2. eliminate the shared variables using @{const H}
  3. push pure term into the predicator
  4. use monotonicity of the predicator
  5. pull pure term out of the predicator
  6. show that the projections are as expected
\<close>

lemma
  assumes *: "rel P (pure f \<diamond> x \<diamond> y) (pure g \<diamond> x \<diamond> y)"
  and base: "\<forall>x y. P (f x y) (g x y) \<longrightarrow> Q (f' x y) (g' x y)"
  shows "rel Q (pure f' \<diamond> x \<diamond> y) (pure g' \<diamond> x \<diamond> y)"
proof -
  txt \<open>This unfolding of @{const rel} is ugly. Can we find a more abstract rule for reasoning?\<close>
  from * obtain z where z: "pred (\<lambda>(x, y). P x y) z"
    and proj: "map fst z = pure f \<diamond> x \<diamond> y" "map snd z = pure g \<diamond> x \<diamond> y"
    unfolding rel_def by blast
  from proj have "z = zip (pure f \<diamond> x \<diamond> y) (pure g \<diamond> x \<diamond> y)" by(rule product_unique)
  also have "\<dots> = pure (\<lambda>x y x' y'. (f x y, g x' y')) \<diamond> x \<diamond> y \<diamond> x \<diamond> y"
    unfolding zip_conv af_composition[symmetric] af_homomorphism o_def
    by(subst af_interchange)(simp add: af_composition[symmetric] af_homomorphism o_def)
  also have "\<dots> = H \<diamond> pure (\<lambda>x y x' y'. (f x y, g x' y')) \<diamond> x \<diamond> y \<diamond> y" unfolding ap_H ..
  also have "\<dots> = W \<diamond> (H \<diamond> pure (\<lambda>x y x' y'. (f x y, g x' y')) \<diamond> x) \<diamond> y" unfolding ap_W ..
  also have "\<dots> = pure (\<lambda>x y. (f x y, g x y)) \<diamond> x \<diamond> y"
    unfolding W_def H_def af_composition[symmetric] af_homomorphism o_def ..
  also have "\<dots> = map (\<lambda>(x, y). (f x y, g x y)) (zip x y)" unfolding map_conv zip_conv 
    af_composition[symmetric] af_homomorphism o_def split_beta fst_conv snd_conv ..
  finally have "pred (\<lambda>(x, y). P (f x y) (g x y)) (zip x y)" using z
    -- \<open>uses distributivity of predicator over map\<close>
    apply clarsimp
    apply(drule bspec)
     apply(rule subsetD[OF set_natural2])
     apply(erule imageI)
    apply simp
    done
  with base have "pred (\<lambda>(x, y). Q (f' x y) (g' x y)) (zip x y)" 
    -- \<open>uses monotonicity of the predicator\<close>
    by auto
  txt \<open>And now we are essentially there: push @{term f'} and @{term g'} back into the product and then project\<close>
  hence 1: "pred (\<lambda>(x, y). Q x y) (map (\<lambda>(x, y). (f' x y, g' x y)) (zip x y))" (is "pred _ ?z")
    apply clarsimp
    apply(drule subsetD[OF set_natural])
    apply auto
    done
  moreover have "map fst ?z = pure f' \<diamond> x \<diamond> y"
    unfolding zip_conv map_conv af_composition[symmetric] af_homomorphism o_def prod.simps fst_conv ..
  moreover have "map snd ?z = pure g' \<diamond> x \<diamond> y"
    unfolding zip_conv map_conv af_composition[symmetric] af_homomorphism o_def prod.simps snd_conv ..
  ultimately show ?thesis unfolding rel_def by blast
qed

text \<open>
  Doubling is really the crucial property here.
  The above example with set also works for pmfs, which have K and C. 
\<close>

subsection \<open>Discarding effects\<close>

text \<open>
  If we can discard effects, products exist (@{const zip}!), but they need not be unique
  (example @{text pair_pmf}). Thus, all effects are compatible.
\<close>

axiomatization K :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) af"
  where ap_K: "K \<diamond> x \<diamond> y = x"
  and K_def: "K = pure (\<lambda>x y. x)"

lemma map_fst_zip_K: "map fst (zip x y) = x" -- \<open>see Hinze, Eq. (1)\<close>
unfolding map_conv zip_conv af_composition[symmetric] af_homomorphism o_def fst_conv
by(fold K_def)(fact ap_K)

lemma map_snd_zip_K: "map snd (zip x y) = y" -- \<open>see Hinze, Eq. (2)\<close>
proof -
  have "map snd (zip x y) = K \<diamond> pure id \<diamond> x \<diamond> y"
    unfolding map_conv zip_conv af_composition[symmetric] af_homomorphism o_def snd_conv K_def id_def ..
  also have "\<dots> = pure id \<diamond> y" unfolding ap_K ..
  also have "\<dots> = y" unfolding af_identity ..
  finally show ?thesis .
qed

lemma compat_K: "compat x y"
unfolding rel_def
apply(rule_tac x="zip x y" in exI)
apply(unfold map_fst_zip_K map_snd_zip_K)
apply blast
done


text \<open>If we have K and W, we can reify equality.\<close>

text \<open>Intuition: We want to exploit equality here, so we need W. We also need K because K ensures
  that x and y are always compatible in their effects.
\<close>
lemma af_eq_reify: "x = y \<longleftrightarrow> pure (op =) \<diamond> x \<diamond> y = pure True" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  have "pure (op =) \<diamond> x \<diamond> y = W \<diamond> pure (op =) \<diamond> y" unfolding \<open>?lhs\<close> ap_W ..
  also have "\<dots> = pure (\<lambda>_. True) \<diamond> y" unfolding W_def by applicative_nf simp
  also have "\<dots> = K \<diamond> pure True \<diamond> y" unfolding K_def by applicative_nf simp
  also have "\<dots> = pure True" unfolding ap_K ..
  finally show ?rhs .
next
  assume ?rhs
  have "x = K \<diamond> x \<diamond> y" unfolding ap_K ..
  also have "\<dots> = pure (\<lambda>x y. if x = y then y else x) \<diamond> x \<diamond> y" unfolding K_def by applicative_nf simp
  also have "\<dots> = W \<diamond> (W \<diamond> (pure (\<lambda>x x' y y'. if x' = y then y' else x)) \<diamond> x) \<diamond> y" unfolding W_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>x x' y y'. if x' = y then y' else x) \<diamond> x \<diamond> x \<diamond> y \<diamond> y" unfolding ap_W ..
  also have "\<dots> = pure (\<lambda>x b y'. if b then y' else x) \<diamond> x \<diamond> (pure op = \<diamond> x \<diamond> y) \<diamond> y" by applicative_nf simp
  also have "\<dots> = pure (\<lambda>x y'. y') \<diamond> x \<diamond> y" unfolding \<open>?rhs\<close> by applicative_nf simp
  also have "\<dots> = K \<diamond> pure (\<lambda>x. x) \<diamond> x \<diamond> y" unfolding K_def by applicative_nf simp
  also have "\<dots> = y" unfolding ap_K by applicative_nf simp
  finally show ?lhs .
qed

text \<open>
  If we have K and W, then we also have C.
\<close>

lemma ap_C_KW: "pure (\<lambda>f x y. f y x) \<diamond> f \<diamond> x \<diamond> y = f \<diamond> y \<diamond> x" (is "?lhs = ?rhs")
proof -
  have "?lhs = (pure (\<lambda>f x y. f y x) \<diamond> f) \<diamond> (K \<diamond> pure (\<lambda>x. x) \<diamond> y \<diamond> x) \<diamond> y" unfolding ap_K by applicative_nf simp
  also have "\<dots> = K \<diamond> \<dots> \<diamond> x" unfolding ap_K ..
  also have "\<dots> = pure (\<lambda>f y' x y x'. f (if y = y' then y' else y) (if x = x' then x' else x)) \<diamond> f \<diamond> y \<diamond> x \<diamond> y \<diamond> x" unfolding K_def
    by applicative_nf simp
  also have "\<dots> = W \<diamond> (pure (\<lambda>f (y', x) (y, x'). f (if y = y' then y' else y) (if x = x' then x' else x)) \<diamond> f) \<diamond> zip y x"
    unfolding ap_W by applicative_nf simp
  also have "\<dots> = pure (\<lambda>f (y', x). f y' x) \<diamond> f \<diamond> zip y x"
    unfolding W_def by applicative_nf simp
  also have "\<dots> = ?rhs" by applicative_nf simp
  finally show ?thesis .
qed


subsection \<open>Swapping\<close>

text \<open>
  Is there an applicative functor that has a K but not a C?
\<close>

axiomatization C :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c) af"
  where ap_C: "C \<diamond> f \<diamond> x \<diamond> y = f \<diamond> y \<diamond> x"
  and C_def: "C = pure (\<lambda>f x y. f y x)"

text \<open>With swapping, we can add effects in the middle.\<close>

lemma rel_add_middle:
  assumes "rel P (f \<diamond> y) (f' \<diamond> y')"
  and "rel (\<lambda>_ _. True) x x'"
  shows "rel P (pure (\<lambda>f x y. f y) \<diamond> f \<diamond> x \<diamond> y) (pure (\<lambda>f x y. f y) \<diamond> f' \<diamond> x' \<diamond> y')"
apply(rule rel_apI)
apply(rule rel_apI)
prefer 2
apply(rule assms(2))
apply(rule rel_apI)
apply(rule rel_apI)+
prefer 3
apply(rule assms)
oops

end