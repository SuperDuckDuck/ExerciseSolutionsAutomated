theory Ex5_2 
  imports Main 
begin 

primrec le :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
"le _ [] = True"|
"le val (x#xs) = (val \<le> x \<and> le val xs)"


primrec sorted :: "nat list \<Rightarrow> bool" where
"sorted [] = True"|
"sorted (x#xs) = (le x xs \<and> sorted xs)"

primrec count :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
"count [] _ = 0"|
"count (x#xs) val = (if val = x then 1 else 0) + count xs val"

