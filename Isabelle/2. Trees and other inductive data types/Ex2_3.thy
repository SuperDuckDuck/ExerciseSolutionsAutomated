theory Ex2_3
  imports Main 
begin 
  
datatype tree = Tp | Nd tree tree 
  
primrec tips :: "tree \<Rightarrow> nat " where 
  "tips Tp = 1"|
  "tips (Nd l r) = op + (tips l) (tips r)"
  
  
primrec height :: "tree \<Rightarrow> nat" where
  "height Tp = 1"|
  "height (Nd l r) = 1 +  max (height l) (height r)"
  
  
primrec cbt :: "nat \<Rightarrow> tree" where
  "cbt 0 = Tp"|
  "cbt (Suc n) = (let tmp = (cbt n) in Nd tmp tmp)"
  
  
primrec iscbt :: " (tree \<Rightarrow> 'a) \<Rightarrow> tree  \<Rightarrow> bool" where
  "iscbt f Tp = True"|
  "iscbt f (Nd l r) = (iscbt f l \<and> iscbt f r \<and> (f l = f r))"
  
theorem "iscbt tips t = iscbt height t" 
proof (induction  t)
  case Tp
  then show ?case by simp
next
  case (Nd t1 t2)
  assume h1:"iscbt tips t1 = iscbt height t1"
     and h2:"iscbt tips t2 = iscbt height t2"
  have "iscbt tips (Nd t1 t2) = (iscbt tips t1 \<and> iscbt tips t2 \<and> (tips t1 = tips t2))" by simp
      
  then show ?case 
qed
  