theory Ex5_1 
  imports Main 
begin 
  
primrec insort :: "nat \<Rightarrow> nat list \<Rightarrow> nat list " where 
  "insort val [] = [val]"|
  "insort val (x#xs) = (if val \<le> x then val#x#xs else x # insort val xs)"
  
  
fun sorted :: "nat list \<Rightarrow> bool" where 
  "sorted [] = True"|
  "sorted [x] = True"|
  "sorted (x#y#xs) =  ((x \<le>  y) \<and>  sorted (y#xs))"
  
  
  