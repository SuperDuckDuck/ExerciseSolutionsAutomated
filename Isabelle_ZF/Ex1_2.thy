theory Ex1_2 
  imports ZF
begin 


consts 
  replace :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"


notation 
  Cons (infix "$$" 55)

primrec 
"replace (old, new, []) = []"
"replace (old ,new, x$$xs) = (if (old = x) then new  else x) $$ replace(old,new,xs)"

