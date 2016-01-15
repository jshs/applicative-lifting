theory BIW imports "$AFP/Applicative_Lifting/Applicative" "~~/src/Tools/Adhoc_Overloading" begin

typedecl 'a af
consts pure :: "'a \<Rightarrow> 'a af"
consts ap :: "('a \<Rightarrow> 'b) af \<Rightarrow> 'a af \<Rightarrow> 'b af"

applicative af (W)
for pure: pure
    ap: ap
sorry

adhoc_overloading Applicative.ap ap

interpretation applicative_syntax .

lemma
  "pure g \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> c = pure (\<lambda>a b c. g a b c a c b a b c) \<diamondop> a \<diamondop> b \<diamondop> c"
  (is "?lhs = ?rhs")
proof -
  def abc \<equiv> "pure (\<lambda>a b c. (a, b, c)) \<diamondop> a \<diamondop> b \<diamondop> c"
  def ca \<equiv> "pure (\<lambda>c a. (c, a)) \<diamondop> c \<diamondop> a"
  def bcac \<equiv> "pure (\<lambda>b c a c'. (b, c, a, c')) \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c"
  def acb \<equiv> "pure (\<lambda>a c b. (a, c, b)) \<diamondop> a \<diamondop> c \<diamondop> b"
  def ba \<equiv> "pure (\<lambda>b a. (b, a)) \<diamondop> b \<diamondop> a"
  def cbab \<equiv> "pure (\<lambda>c b a b'. (c, b, a, b')) \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b"
  def abcacbabc \<equiv> "pure (\<lambda>a1 b1 c1 a2 c2 b2 a3 b3 c3. (a1, b1, c1, a2, c2, b2, a3, b3, c3)) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> c"
  
  have "?lhs = pure (\<lambda>a1 b1 c1 a2 c2 b2 (a3, b3, c3). g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> abc"
    unfolding abc_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 b2 (a3, b3, c3). g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> (pure (\<lambda>x _ _. x) \<diamondop> abc \<diamondop> abc \<diamondop> abc)"
    by applicative_lifting simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 b2 a3 b3 c3 a4 b4 (c4, a5) b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> ca \<diamondop> b \<diamondop> c"
    unfolding abc_def ca_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 b2 a3 b3 c3 a4 b4 (c4, a5) (c4', a5') b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> ca \<diamondop> ca \<diamondop> b \<diamondop> c"
    by applicative_lifting simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 b2 a3 b3 c3 a4 (b4, c4, a5, c4') a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> bcac \<diamondop> a \<diamondop> b \<diamondop> c"
    unfolding ca_def bcac_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 b2 a3 b3 c3 a4 (b4, c4, a5, c4') (b4', c4', a5', c4'') a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> bcac \<diamondop> bcac \<diamondop> a \<diamondop> b \<diamondop> c"
    by applicative_lifting simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 b2 a3 b3 c3 a4 b4 c4 (a5, c4', b4') c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> acb \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    unfolding bcac_def acb_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 b2 a3 b3 c3 a4 b4 c4 (a5, c4', b4') (a5', c4''', b4'') c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> acb \<diamondop> acb \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    by applicative_lifting simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 b2 a3 b3 c3 a4 b4 c4 a5 c4' (b4', a5') c4''' b4'' c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> ba \<diamondop> c \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    unfolding acb_def ba_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 b2 a3 b3 c3 a4 b4 c4 a5 c4' (b4', a5') (b4''', a5''') c4''' b4'' c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> ba \<diamondop> ba \<diamondop> c \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    by applicative_lifting simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 b2 a3 b3 c3 a4 b4 c4 a5 (c4', b4', a5', b4''') a5''' c4''' b4'' c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> cbab \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    unfolding ba_def cbab_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 b2 a3 b3 c3 a4 b4 c4 a5 (c4', b4', a5', b4''') (c4''', b4'''', a5'''', b4''''') a5''' c4''' b4'' c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> cbab \<diamondop> cbab \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    by applicative_lifting simp
  also have "\<dots> = pure (\<lambda>(a1, b1, c1, a2, c2, b2, a3, b3, c3) (a4, b4, c4, a5, c4', b4', a5', b4''', c4''') b4'''' a5'''' b4''''' a5''' c4''' b4'' c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> abcacbabc \<diamondop> abcacbabc \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    unfolding cbab_def abcacbabc_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>(a1, b1, c1, a2, c2, b2, a3, b3, c3) b4'''' a5'''' b4''''' a5''' c4''' b4'' c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> abcacbabc \<diamondop> b \<diamondop> a \<diamondop> b \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    by applicative_lifting clarsimp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 (c2, b2, a3, b3) (c3, b4'''', a5'''', b4''''') a5''' c4''' b4'' c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c3) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> cbab \<diamondop> cbab \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    unfolding cbab_def abcacbabc_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 (c2, b2, a3, b3) a5''' c4''' b4'' c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c2) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> cbab \<diamondop> a \<diamondop> c \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    by applicative_lifting clarsimp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 (b2, a3) (b3, a5''') c4''' b4'' c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b3 c2) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> ba \<diamondop> ba \<diamondop> c \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    unfolding ba_def cbab_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 a2 c2 (b2, a3) c4''' b4'' c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b2 c2) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> ba \<diamondop> c \<diamondop> b \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    by applicative_lifting clarsimp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 (a2, c2, b2) (a3, c4''', b4'') c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a3 b2 c2) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> acb \<diamondop> acb \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    unfolding acb_def ba_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>a1 b1 c1 (a2, c2, b2) c4' a5' c4'' a5' b5 c5. g a1 b1 c1 a2 c2 b2 a2 b2 c2) \<diamondop> a \<diamondop> b \<diamondop> c \<diamondop> acb \<diamondop> c \<diamondop> a \<diamondop> c \<diamondop> a \<diamondop> b \<diamondop> c"
    by applicative_lifting clarsimp
  also have "\<dots> = pure (\<lambda>a1 (b1, c1, a2, c2) (b2, c4', a5', c4'') a5' b5 c5. g a1 b1 c1 a2 c2 b2 a2 b2 c2) \<diamondop> a \<diamondop> bcac \<diamondop> bcac \<diamondop> a \<diamondop> b \<diamondop> c"
    unfolding bcac_def acb_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>a1 (b1, c1, a2, c2) a5' b5 c5. g a1 b1 c1 a2 c2 b1 a2 b1 c2) \<diamondop> a \<diamondop> bcac \<diamondop> a \<diamondop> b \<diamondop> c"
    by applicative_lifting clarsimp
  also have "\<dots> = pure (\<lambda>a1 b1 (c1, a2) (c2, a5') b5 c5. g a1 b1 c1 a2 c2 b1 a2 b1 c2) \<diamondop> a \<diamondop> b \<diamondop> ca \<diamondop> ca \<diamondop> b \<diamondop> c"
    unfolding ca_def bcac_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>a1 b1 (c1, a2) b5 c5. g a1 b1 c1 a2 c1 b1 a2 b1 c1) \<diamondop> a \<diamondop> b \<diamondop> ca \<diamondop> b \<diamondop> c"
    by applicative_lifting clarsimp
  also have "\<dots> = pure (\<lambda>(a1, b1, c1) (a2, b5, c5). g a1 b1 c1 a2 c1 b1 a2 b1 c1) \<diamondop> abc \<diamondop> abc"
    unfolding abc_def ca_def by applicative_nf simp
  also have "\<dots> = pure (\<lambda>(a, b, c). g a b c a c b a b c) \<diamondop> abc"
    by applicative_lifting clarsimp
  also have "\<dots> = ?rhs" unfolding abc_def by applicative_nf simp
  finally show ?thesis .
qed

end