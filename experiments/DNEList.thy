theory DNEList imports
  "$AFP/Applicative_Lifting/Applicative_List"
begin

lemma bind_eq_Nil_iff [simp]: "List.bind xs f = [] \<longleftrightarrow> (\<forall>x\<in>set xs. f x = [])"
by(simp add: List.bind_def)

lemma zip_eq_Nil_iff [simp]: "zip xs ys = [] \<longleftrightarrow> xs = [] \<or> ys = []"
by(cases xs ys rule: list.exhaust[case_product list.exhaust]) simp_all

lemma fst_swap [simp]: "fst (prod.swap x) = snd x"
by(cases x) simp

lemma snd_swap [simp]: "snd (prod.swap x) = fst x"
by(cases x) simp

lemma remdups_append1: "remdups (remdups xs @ ys) = remdups (xs @ ys)"
by(induction xs) simp_all

lemma remdups_append2: "remdups (xs @ remdups ys) = remdups (xs @ ys)"
by(induction xs) simp_all

lemma remdups_append1_drop: "set xs \<subseteq> set ys \<Longrightarrow> remdups (xs @ ys) = remdups ys"
by(induction xs) auto

lemma remdups_concat_map: "remdups (concat (map remdups xss)) = remdups (concat xss)"
by(induction xss)(simp_all add: remdups_append1, metis remdups_append2)

lemma remdups_concat_remdups: "remdups (concat (remdups xss)) = remdups (concat xss)"
apply(induction xss)
apply(auto simp add: remdups_append1_drop)
 apply(subst remdups_append1_drop; auto)
apply(metis remdups_append2)
done

lemma remdups_replicate: "remdups (replicate n x) = (if n = 0 then [] else [x])"
by(induction n) simp_all


typedef 'a dnelist = "{xs::'a list. distinct xs \<and> xs \<noteq> []}"
  morphisms list_of_dnelist Abs_dnelist
proof
  show "[x] \<in> ?dnelist" for x by simp
qed

setup_lifting type_definition_dnelist

context begin
qualified lift_definition single :: "'a \<Rightarrow> 'a dnelist" is "\<lambda>x. [x]" by simp
qualified lift_definition insert :: "'a \<Rightarrow> 'a dnelist \<Rightarrow> 'a dnelist" is "\<lambda>x xs. if x \<in> set xs then xs else x # xs" by auto
qualified lift_definition append :: "'a dnelist \<Rightarrow> 'a dnelist \<Rightarrow> 'a dnelist" is "\<lambda>xs ys. remdups (xs @ ys)" by auto
qualified lift_definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a dnelist \<Rightarrow> 'b dnelist" is "\<lambda>f xs. remdups (List.map f xs)" by auto
qualified lift_definition bind :: "'a dnelist \<Rightarrow> ('a \<Rightarrow> 'b dnelist) \<Rightarrow> 'b dnelist" is "\<lambda>xs f. remdups (List.bind xs f)" by auto

abbreviation (input) pure_dnelist :: "'a \<Rightarrow> 'a dnelist"
where "pure_dnelist \<equiv> single"

end

lift_definition ap_dnelist :: "('a \<Rightarrow> 'b) dnelist \<Rightarrow> 'a dnelist \<Rightarrow> 'b dnelist"
is "\<lambda>f x. remdups (ap_list f x)"
by(auto simp add: ap_list_def)

adhoc_overloading Applicative.ap ap_dnelist

lemma ap_pure_list [simp]: "ap_list [f] xs = map f xs"
by(simp add: ap_list_def List.bind_def)

context begin interpretation applicative_syntax .

lemma ap_pure_dlist: "pure_dnelist f \<diamond> x = DNEList.map f x"
by transfer simp

applicative dnelist (K)
for pure: pure_dnelist
    ap: ap_dnelist
proof -
  show "pure_dnelist (\<lambda>x. x) \<diamond> x = x" for x :: "'a dnelist"
    by transfer simp
  show "pure_dnelist (\<lambda>g f x. g (f x)) \<diamond> g \<diamond> f \<diamond> x = g \<diamond> (f \<diamond> x)"
    for g :: "('c \<Rightarrow> 'b) dnelist" and f :: "('a \<Rightarrow> 'c) dnelist" and x
    apply transfer
    apply(simp add: ap_list_def List.bind_def)
    apply(subst (2) remdups_concat_remdups[symmetric])
    apply(subst remdups_map_remdups)
    apply simp
    apply(subst remdups_concat_remdups)
    apply(subst (1) remdups_concat_remdups[symmetric])
    apply(subst remdups_map_remdups)
    apply(subst remdups_concat_remdups)
    apply(subst (2) remdups_concat_map[symmetric])
    apply(simp add: o_def)
    apply(subst remdups_map_remdups)
    apply(subst (5) list.map_comp[symmetric, unfolded o_def]) back back back back
    apply(subst remdups_concat_map)
    subgoal for g f x using list.afun_comp[of g f x]
      by(simp add: ap_list_def List.bind_def o_def)
    done
  show "pure_dnelist f \<diamond> pure_dnelist x = pure_dnelist (f x)" for f :: "'a \<Rightarrow> 'b" and x
    by transfer simp
  show "f \<diamond> pure_dnelist x = pure_dnelist (\<lambda>f. f x) \<diamond> f" for f :: "('a \<Rightarrow> 'b) dnelist" and x
    by transfer(simp add: list.afun_ichng)
  show "pure_dnelist (\<lambda>x y. x) \<diamond> x \<diamond> y = x" 
    for x :: "'b dnelist" and y :: "'a dnelist"
    apply transfer
    apply(simp add: ap_list_def List.bind_def)
    apply(subst (2) distinct_remdups_id)
    apply(simp add: distinct_map)
    apply(rule inj_onI)
    apply(simp add: fun_eq_iff)
    apply(simp add: o_def map_replicate_const)
    apply(subst remdups_concat_map[symmetric])
    apply(simp add: o_def remdups_replicate)
    done
qed


text \<open>@{typ "_ dnelist"} does not have combinator C, so it cannot have W either.\<close>

context begin 
private lift_definition x :: "int dnelist" is "[2,3]" by simp
private lift_definition y :: "int dnelist" is "[5,7]" by simp
private lemma "pure_dnelist (\<lambda>f x y. f y x) \<diamond> pure_dnelist (op *) \<diamond> x \<diamond> y \<noteq> pure_dnelist (op *) \<diamond> y \<diamond> x"
  by transfer(simp add: ap_list_def fun_eq_iff)
end

end


text \<open>@{typ "_ dnelist"} preserves weak pullbacks\<close>

fun wpull :: "('a \<times> 'b) list \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> ('a \<times> 'c) list"
where
  "wpull [] ys = []"
| "wpull xs [] = []"
| "wpull ((a, b) # xs) ((b', c) # ys) =
  (if b \<in> snd ` set xs then
     (a, the (map_of (rev ((b', c) # ys)) b)) # wpull xs ((b', c) # ys)
   else if b' \<in> fst ` set ys then
     (the (map_of (map prod.swap (rev ((a, b) # xs))) b'), c) # wpull ((a, b) # xs) ys
   else (a, c) # wpull xs ys)"

lemma wpull_eq_Nil_iff: "wpull xs ys = [] \<longleftrightarrow> xs = [] \<or> ys = []"
by(cases "(xs, ys)" rule: wpull.cases) simp_all

lemma set_wpull_subset:
  assumes "remdups (map snd xs) = remdups (map fst ys)"
  shows "set (wpull xs ys) \<subseteq> set xs O set ys"
using assms
proof(induction xs ys rule: wpull.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case Cons: (3 a b xs b' c ys)
  let ?xs = "(a, b) # xs" and ?ys = "(b', c) # ys"
  consider (xs) "b \<in> snd ` set xs" | (ys) "b \<notin> snd ` set xs" "b' \<in> fst ` set ys"
    | (step) "b \<notin> snd ` set xs" "b' \<notin> fst ` set ys" by auto
  then show ?case
  proof(cases)
    case xs
    with Cons.prems have eq: "remdups (map snd xs) = remdups (map fst ?ys)" by auto
    have "set (wpull xs ((b', c) # ys)) \<subseteq> set ?xs O set ?ys" 
      using Cons.IH(1)[OF xs eq] by auto
    moreover from xs eq have "b \<in> fst ` set ?ys" by (metis list.set_map set_remdups)
    hence "map_of (rev ?ys) b \<noteq> None" unfolding map_of_eq_None_iff by auto
    then obtain c' where "map_of (rev ?ys) b = Some c'" by blast
    then have "(b, the (map_of (rev ?ys) b)) \<in> set ?ys" by(auto dest: map_of_SomeD split: split_if_asm)
    then have "(a, the (map_of (rev ((b', c) # ys)) b)) \<in> set ?xs O set ?ys" by auto
    ultimately show ?thesis using xs by simp
  next
    case ys
    from ys Cons.prems have eq: "remdups (map snd ?xs) = remdups (map fst ys)" by auto
    have "set (wpull ((a, b) # xs) ys) \<subseteq> set ?xs O set ?ys" using Cons.IH(2)[OF ys eq] by auto
    moreover from ys eq have "b' \<in> snd ` set ?xs" by (metis list.set_map set_remdups)
    hence "map_of (map prod.swap (rev ?xs)) b' \<noteq> None"
      unfolding map_of_eq_None_iff by(auto simp add: image_image)
    then obtain a' where "map_of (map prod.swap (rev ?xs)) b' = Some a'" by blast
    then have "(the (map_of (map prod.swap (rev ?xs)) b'), b') \<in> set ?xs"
      by(auto dest: map_of_SomeD split: split_if_asm)
    then have "(the (map_of (map prod.swap (rev ?xs)) b'), c) \<in> set ?xs O set ?ys" by auto
    ultimately show ?thesis using ys by simp
  next
    case step
    thus ?thesis using Cons.IH(3)[OF step] Cons.prems by auto
  qed
qed

lemma set_fst_wpull:
  assumes "remdups (map snd xs) = remdups (map fst ys)"
  shows "fst ` set (wpull xs ys) = fst ` set xs"
using assms
proof(induction xs ys rule: wpull.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by(simp split: split_if_asm)
next
  case Cons: (3 a b xs b' c ys)
  let ?xs = "(a, b) # xs" and ?ys = "(b', c) # ys"
  consider (xs) "b \<in> snd ` set xs" | (ys) "b \<notin> snd ` set xs" "b' \<in> fst ` set ys"
    | (step) "b \<notin> snd ` set xs" "b' \<notin> fst ` set ys" by auto
  then show ?case
  proof(cases)
    case xs
    with Cons.prems have "remdups (map snd xs) = remdups (map fst ?ys)" by auto
    with Cons.IH(1)[OF xs this] xs show ?thesis by simp
  next
    case ys
    with Cons.prems have eq: "remdups (map snd ?xs) = remdups (map fst ys)" by auto
    note Cons.IH(2)[OF ys this]
    moreover from ys eq have "b' \<in> snd ` set ?xs" by (metis list.set_map set_remdups)
    hence "map_of (map prod.swap (rev ?xs)) b' \<noteq> None"
      unfolding map_of_eq_None_iff by(auto simp add: image_image)
    then obtain a' where "map_of (map prod.swap (rev ?xs)) b' = Some a'" by blast
    then have "(the (map_of (map prod.swap (rev ?xs)) b'), b') \<in> set ?xs"
      by(auto dest: map_of_SomeD split: split_if_asm)
    hence "the (map_of (map prod.swap (rev ?xs)) b') \<in> fst ` set ?xs" by(auto intro: rev_image_eqI)
    ultimately show ?thesis using ys by auto
  next
    case step
    hence "remdups (map snd xs) = remdups (map fst ys)" using Cons.prems by auto
    from Cons.IH(3)[OF step this] step show ?thesis by simp
  qed
qed

lemma set_snd_wpull:
  assumes "remdups (map snd xs) = remdups (map fst ys)"
  shows "snd ` set (wpull xs ys) = snd ` set ys"
using assms
proof(induction xs ys rule: wpull.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by(simp split: split_if_asm)
next
  case Cons: (3 a b xs b' c ys)
  let ?xs = "(a, b) # xs" and ?ys = "(b', c) # ys"
  consider (xs) "b \<in> snd ` set xs" | (ys) "b \<notin> snd ` set xs" "b' \<in> fst ` set ys"
    | (step) "b \<notin> snd ` set xs" "b' \<notin> fst ` set ys" by auto
  then show ?case
  proof(cases)
    case xs
    with Cons.prems have eq: "remdups (map snd xs) = remdups (map fst ?ys)" by auto
    note Cons.IH(1)[OF xs eq]
    moreover from xs eq have "b \<in> fst ` set ?ys" by (metis list.set_map set_remdups)
    hence "map_of (rev ?ys) b \<noteq> None" unfolding map_of_eq_None_iff by auto
    then obtain c' where "map_of (rev ?ys) b = Some c'" by blast
    then have "(b, the (map_of (rev ?ys) b)) \<in> set ?ys" by(auto dest: map_of_SomeD split: split_if_asm)
    hence "the (map_of (rev ?ys) b) \<in> snd ` set ?ys" by(auto intro: rev_image_eqI)
    ultimately show ?thesis using xs by auto
  next
    case ys
    with Cons.prems have "remdups (map snd ?xs) = remdups (map fst ys)" by auto
    with Cons.IH(2)[OF ys this] ys show ?thesis by simp
  next
    case step
    hence "remdups (map snd xs) = remdups (map fst ys)" using Cons.prems by auto
    from Cons.IH(3)[OF step this] step show ?thesis by simp
  qed
qed
  

lemma wpull:
  assumes "distinct xs"
  and "distinct ys"
  and "xs \<noteq> []"
  and "ys \<noteq> []"
  and "set xs \<subseteq> {(x, y). R x y}"
  and "set ys \<subseteq> {(x, y). S x y}"
  and "remdups (map snd xs) = remdups (map fst ys)"
  shows "\<exists>zs. distinct zs \<and>
          zs \<noteq> [] \<and>
          set zs \<subseteq> {(x, y). (R OO S) x y} \<and>
          remdups (map fst zs) = remdups (map fst xs) \<and>
          remdups (map snd zs) = remdups (map snd ys)"
proof(intro exI conjI)
  let ?zs = "remdups (wpull xs ys)"
  show "distinct ?zs" by simp
  show "?zs \<noteq> []" using assms(3-4) by(simp add: wpull_eq_Nil_iff)
  show "set ?zs \<subseteq> {(x, y). (R OO S) x y}" using assms(5-6) set_wpull_subset[OF assms(7)] by fastforce
  show "remdups (map fst ?zs) = remdups (map fst xs)" unfolding remdups_map_remdups using assms(7)
  proof(induction xs ys rule: wpull.induct)
    case 1 thus ?case by simp
  next
    case 2 thus ?case by(simp split: split_if_asm)
  next
    case Cons: (3 a b xs b' c ys)
    let ?xs = "(a, b) # xs" and ?ys = "(b', c) # ys"
    consider (xs) "b \<in> snd ` set xs" | (ys) "b \<notin> snd ` set xs" "b' \<in> fst ` set ys"
      | (step) "b \<notin> snd ` set xs" "b' \<notin> fst ` set ys" by auto
    then show ?case
    proof(cases)
      case xs
      with Cons.prems have eq: "remdups (map snd xs) = remdups (map fst ?ys)" by auto
      show ?thesis using xs Cons.IH(1)[OF xs eq] by(simp add: set_fst_wpull[OF eq])
    next
      case ys
      with Cons.prems have eq: "remdups (map snd ?xs) = remdups (map fst ys)" by auto
      from ys eq have "b' \<in> snd ` set ?xs" by (metis list.set_map set_remdups)
      hence "map_of (map prod.swap (rev ?xs)) b' \<noteq> None"
        unfolding map_of_eq_None_iff by(auto simp add: image_image)
      then obtain a' where "map_of (map prod.swap (rev ?xs)) b' = Some a'" by blast
      then have "(the (map_of (map prod.swap (rev ?xs)) b'), b') \<in> set ?xs"
        by(auto dest: map_of_SomeD split: split_if_asm)
      hence "the (map_of (map prod.swap (rev ?xs)) b') \<in> fst ` set ?xs" by(auto intro: rev_image_eqI)
      then show ?thesis using ys Cons.IH(2)[OF ys eq] by(simp add: set_fst_wpull[OF eq])
    next
      case step
      with Cons.prems have eq: "remdups (map snd xs) = remdups (map fst ys)" by auto
      show ?thesis using step Cons.IH(3)[OF step eq] by(simp add: set_fst_wpull[OF eq])
    qed
  qed

  show "remdups (map snd ?zs) = remdups (map snd ys)" unfolding remdups_map_remdups using assms(7)
  proof(induction xs ys rule: wpull.induct)
    case 1 thus ?case by simp
  next
    case 2 thus ?case by(simp split: split_if_asm)
  next
    case Cons: (3 a b xs b' c ys)
    let ?xs = "(a, b) # xs" and ?ys = "(b', c) # ys"
    consider (xs) "b \<in> snd ` set xs" | (ys) "b \<notin> snd ` set xs" "b' \<in> fst ` set ys"
      | (step) "b \<notin> snd ` set xs" "b' \<notin> fst ` set ys" by auto
    then show ?case
    proof(cases)
      case xs
      with Cons.prems have eq: "remdups (map snd xs) = remdups (map fst ?ys)" by auto
      from xs eq have "b \<in> fst ` set ?ys" by (metis list.set_map set_remdups)
      hence "map_of (rev ?ys) b \<noteq> None" unfolding map_of_eq_None_iff by auto
      then obtain c' where "map_of (rev ?ys) b = Some c'" by blast
      then have "(b, the (map_of (rev ?ys) b)) \<in> set ?ys" by(auto dest: map_of_SomeD split: split_if_asm)
      hence "the (map_of (rev ?ys) b) \<in> snd ` set ?ys" by(auto intro: rev_image_eqI)
      then show ?thesis using xs Cons.IH(1)[OF xs eq] by(simp add: set_snd_wpull[OF eq])
    next
      case ys
      with Cons.prems have eq: "remdups (map snd ?xs) = remdups (map fst ys)" by auto
      show ?thesis using ys Cons.IH(2)[OF ys eq] by(simp add: set_snd_wpull[OF eq])
    next
      case step
      with Cons.prems have eq: "remdups (map snd xs) = remdups (map fst ys)" by auto
      show ?thesis using step Cons.IH(3)[OF step eq] by(simp add: set_snd_wpull[OF eq])
    qed
  qed
qed

end