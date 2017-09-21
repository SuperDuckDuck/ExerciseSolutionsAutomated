theory Ex1_9
  imports Main 
begin 
  
  
primrec zip1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "zip1 [] rest  = rest"|
  "zip1 (x#xs) rest = (case rest of  [] \<Rightarrow> (x#xs) | (y#ys) \<Rightarrow> x # y # zip1 xs ys)"
  
primrec zip2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "zip2 rest [] = rest"|
  "zip2 rest (x#xs) = (case rest of [] \<Rightarrow> (x#xs) | (y#ys) \<Rightarrow> y # x # zip2 ys xs)"
  
fun zipr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "zipr [] ys = ys"|
  "zipr xs [] = xs"|
  "zipr (x#xs) (y#ys) = x # y # zipr xs ys"
  
lemma "zip1 xs ys = zip2 xs ys" 
proof (induct xs ys rule : list_induct2')
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by simp
next
  case (3 y ys)
  then show ?case by simp
next
  case (4 x xs y ys)
  then show ?case by simp
qed  
  
lemma "zip1 xs ys = zipr xs ys" by (induct xs ys rule : list_induct2', simp_all)
    
lemma "zip2 xs ys = zipr xs ys" by (induct xs ys rule : list_induct2', simp_all)
  
  
lemma "\<lbrakk> length p = length u ; length q = length v\<rbrakk> \<Longrightarrow> zipr (p@q) (u@v) = zipr p u @ zipr q v" 
proof (induct p u rule : list_induct2)
  case Nil
  then show ?case  by simp
next
  case (Cons x xs y ys)
  assume hyp1:"length xs = length ys"
  assume hyp2:" length q = length v \<Longrightarrow> zipr (xs @ q) (ys @ v) = zipr xs ys @ zipr q v"
  assume hyp3:"length q = length v"
  show ?case using hyp3 hyp2 by simp
qed

  
  

  
