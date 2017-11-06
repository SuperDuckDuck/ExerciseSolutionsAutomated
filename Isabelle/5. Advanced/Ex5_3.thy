theory Ex5_3
  imports Main
begin 


datatype ('a , 'v) trie = Trie "'v option" "('a \<times> ('a , 'v) trie) list"

primrec "value" :: "('a , 'v) trie \<Rightarrow> 'v option" where 
"value (Trie ov al) = ov"

primrec