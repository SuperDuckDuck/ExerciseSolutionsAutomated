theory Ex1_6
  imports Main 
begin 

  
primrec sum :: "nat list \<Rightarrow> nat" where 
  "sum [] = 0"|
  "sum (x#xs) = x + sum xs"
  

primrec flatten :: "'a list list \<Rightarrow> 'a list" where 
  "flatten [] = []"|
  "flatten (x#xs) = x @ flatten xs"
  
lemma "sum [2::nat ,4,8] = 14" by simp

lemma "flatten [[2::nat, 3], [4,5], [7,9]] = [2,3,4,5,7,9]" by simp
    
lemma "length (flatten xs) = sum (map length xs)" by (induct xs; simp)
    
lemma sum_append : "sum (xs @ ys) = sum xs + sum ys" by (induct xs; simp)
    
lemma flatten_append : "flatten (xs @ ys) = flatten xs @ flatten ys" by (induct xs; simp)
    
lemma "flatten (map rev (rev xs)) = rev (flatten xs)" by (induct xs; simp add : flatten_append)

lemma "flatten (rev (map rev xs)) = rev (flatten xs)" by (induct xs; simp add : flatten_append)    
    
lemma "list_all (list_all P) xs = list_all P (flatten xs)" by (induct xs; simp)
    
(*lemma "flatten (rev xs) = flatten xs" quickcheck *)
    
lemma "flatten (rev [[1::nat,2],[3::nat,4]]) = flatten [[1::nat,2],[3::nat,4]] \<Longrightarrow> False" by simp
    
lemma "sum (rev xs) = sum xs" by (induct xs; simp add : sum_append)
    
lemma "list_all (op \<le> 1) xs \<longrightarrow> length xs \<le> sum xs" by (induct xs; auto)
    
primrec list_exists :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool)" where
  "list_exists _ [] = False"|
  "list_exists P (x#xs) = (P x \<or> list_exists P xs)"
  
lemma "list_exists (\<lambda>n .  n < 3 ) [4::nat , 3, 7] = False" by simp
 
lemma "list_exists (\<lambda>n .  n < 4 ) [4::nat , 3, 7] = True" by simp
    
lemma list_exists_append : "list_exists P (xs @ ys) = (list_exists P xs \<or> list_exists P ys)" by (induct xs; simp)
    
lemma "list_exists (list_exists P) xs = list_exists P (flatten xs)" by (induct xs; simp add : list_exists_append)
    
definition "list_exists2 P ls = (\<not> (list_all (\<lambda>x . \<not>(P x))) ls)"

lemma "list_exists P xs = list_exists2 P xs" by (induct xs; simp add : list_exists2_def)