theory Ex5_3
  imports Main
begin 


datatype ('a , 'v) trie = Trie "'v option" "('a \<times> ('a , 'v) trie) list"


primrec "value" :: "('a , 'v) trie \<Rightarrow> 'v option" where 
"value (Trie ov al) = ov"

primrec alist ::  "('a , 'v)trie \<Rightarrow> ('a \<times> ('a , 'v)trie) list" where
"alist (Trie v ls) = ls"

primrec assoc :: "('key \<times> 'val)list \<Rightarrow> 'key \<Rightarrow> 'val option" where
"assoc [] x = None"|
"assoc (x#xs) key = (if key=  fst x then Some (snd x) else assoc xs key)"

primrec lookup :: "" where 
"lookup "
