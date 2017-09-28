theory Ex2_3
  imports Main 
begin 
  
datatype tree = Tp | Nd tree tree 
  
primrec tips :: "tree \<Rightarrow> nat " where 
  "tips Tp = 1"|
  "tips (Nd l r) = op + (tips l) (tips r)"
  
  
primrec height :: "tree \<Rightarrow> nat" where
  "height Tp = 0"|
  "height (Nd l r) = 1 +  max (height l) (height r)"
  
  
primrec cbt :: "nat \<Rightarrow> tree" where
  "cbt 0 = Tp"|
  "cbt (Suc n) = (let tmp = (cbt n) in Nd tmp tmp)"

  
primrec iscbt :: " (tree \<Rightarrow> 'a) \<Rightarrow> tree  \<Rightarrow> bool" where
  "iscbt f Tp = True"|
  "iscbt f (Nd l r) = (iscbt f l \<and> iscbt f r \<and> (f l = f r))"
 
lemma helper1 : "iscbt height t \<Longrightarrow>  tips t = 2 ^ height t" by (induction t , simp_all)

lemma helper1_arith : fixes n::nat and m::nat shows  "((2 ^ n :: nat) = (2 ^ m)) = (n = m)" by simp
    
theorem "iscbt height t = iscbt tips t"
proof (induction t)
  case Tp
  then show ?case by simp
next
  case (Nd t1 t2)
  assume h1:"iscbt height t1 = iscbt tips t1"
    and h2:"iscbt height t2 = iscbt tips t2"
  show ?case 
  proof (cases "iscbt height (Nd t1 t2)")
    case True
    assume c1:"iscbt height (Nd t1 t2)"
    show ?thesis 
    proof (cases "iscbt tips (Nd t1 t2)")
      case True
      with c1 show ?thesis by simp
    next
      case False
      assume c2:"\<not> iscbt tips (Nd t1 t2)"
      from c1 have tmp:"height t1 = height t2" by simp
      from c1 have tmp2:"iscbt height t1" by simp
      from c1 have tmp3:"iscbt height t2" by simp
      then have tmp4:"tips t2 = 2 ^ height t2" by (rule helper1[of t2])
          
      have  "iscbt tips (Nd t1 t2) = (iscbt tips t1 \<and> iscbt tips t2 \<and> (tips t1 = tips t2))"  by simp
      also have "\<dots> = (iscbt height t1 \<and> iscbt height t2 \<and> (tips t1 = tips t2))" using h1 h2 by simp
      also have "\<dots> = (iscbt height t1 \<and> iscbt height t2 \<and> (2 ^ height t1 = tips t2 ))" using helper1[of t1]  tmp2  by simp
      also have "\<dots> = (iscbt height t1 \<and> iscbt height t2 \<and> (2 ^ height t1 = (2 ^ height t2 :: nat)))" by (subst tmp4, rule refl)
      also have  "\<dots> = (iscbt height t1 \<and> iscbt height t2 \<and> (height t1 = height t2 ))" by (simp add : helper1_arith)
      also have "\<dots> = True" using tmp tmp2 tmp3 by simp
      finally have False using c2 by simp
      then show ?thesis by (rule FalseE)
    qed
  next
    case False
    assume c1:"\<not> iscbt height (Nd t1 t2)"
    then show ?thesis 
    proof (cases "iscbt tips (Nd t1 t2)")
      case True
      then show ?thesis using h1 h2 helper1 by simp
    next
      case False
      then show ?thesis using c1 by auto
    qed    
  qed
qed
  
    