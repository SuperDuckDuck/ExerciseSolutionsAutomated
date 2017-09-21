theory Ex2_1
  imports Main 
begin 
  
  
datatype 'a tree = Leaf (nval  :'a) | Node (nval : 'a) (lft : "'a tree") (rgt : "'a tree")
  
primrec preOrder :: "'a tree \<Rightarrow> 'a list " where 
  "preOrder (Leaf val) = [val]"|
  "preOrder (Node val lt rt) =  val # preOrder lt @ preOrder rt"
  
primrec postOrder :: "'a tree \<Rightarrow> 'a list" where 
  "postOrder (Leaf val) = [val]"|
  "postOrder (Node val lt rt) = postOrder lt @ postOrder rt @ [val]"
  
primrec inOrder :: "'a tree  \<Rightarrow> 'a list" where 
  "inOrder (Leaf val) = [val]"|
  "inOrder (Node val lt rt) = inOrder lt @ val # inOrder rt"
  
primrec mirror :: "'a tree \<Rightarrow> 'a tree" where 
  "mirror (Leaf val) = (Leaf val)"|
  "mirror (Node val lt rt) = Node val (mirror rt) (mirror lt)"
  
(*lemma "preOrder (mirror xt) = rev (preOrder xt)"  quickcheck *)
  
lemma "let xt = Node (1::int) (Node 2 (Leaf 3) (Leaf 4)) (Leaf 5)  in preOrder (mirror xt) = rev (preOrder xt) \<Longrightarrow> False" by simp
    
lemma "preOrder (mirror xt) = rev (postOrder xt)"  
proof (induct xt)
  case (Leaf x)
  then show ?case by simp
next
  case (Node x1a xt1 xt2)
  assume hyp1:" preOrder (mirror xt1) = rev (postOrder xt1)"
     and hyp2:"preOrder (mirror xt2) = rev (postOrder xt2)"
  then show ?case by simp
qed
    
lemma "postOrder (mirror xt) = rev (preOrder xt)" 
proof (induct xt)
  case (Leaf x)
  then show ?case by simp
next
  case (Node x1a xt1 xt2)
  then show ?case by simp
qed
      
lemma "let xt =  Node (1::int) (Node 2 (Leaf 3) (Leaf 4)) (Leaf 5)   in preOrder (mirror xt) = rev (inOrder xt) \<Longrightarrow> False" by simp
    
lemma "let xt =  Node (1::int) (Node 2 (Leaf 3) (Leaf 4)) (Leaf 5)   in inOrder (mirror xt) = rev (preOrder xt) \<Longrightarrow> False" by simp
    
lemma "let xt =  Node (1::int) (Node 2 (Leaf 3) (Leaf 4)) (Leaf 5)   in postOrder (mirror xt) = rev (postOrder xt) \<Longrightarrow> False" by simp
    
lemma "let xt =  Node (1::int) (Node 2 (Leaf 3) (Leaf 4)) (Leaf 5)   in postOrder (mirror xt) = rev (inOrder xt) \<Longrightarrow> False" by simp
    
lemma "let xt =  Node (1::int) (Node 2 (Leaf 3) (Leaf 4)) (Leaf 5)   in inOrder (mirror xt) = rev (postOrder xt) \<Longrightarrow> False" by simp
    
lemma "inOrder (mirror xt) = rev (inOrder xt)" 
proof (induct xt)
  case (Leaf x)
  then show ?case by simp
next
  case (Node x1a xt1 xt2)
  then show ?case by simp
qed
  
definition root :: "'a tree \<Rightarrow> 'a" where 
  "root xt = nval xt"
  
primrec leftmost :: "'a tree \<Rightarrow> 'a" where 
  "leftmost (Leaf val) = val"|
  "leftmost (Node _ lt _) = leftmost lt"
  
primrec rightmost :: "'a tree \<Rightarrow> 'a" where 
  "rightmost (Leaf val) = val"|
  "rightmost (Node _ _ rt) = rightmost rt"
  
lemma helper1 : "length (inOrder xt) > 0" 
proof (cases xt)
  case (Leaf x1)
  then show ?thesis  by simp
next
  case (Node x21 x22 x23)
  then show ?thesis by simp
qed
  
  
    
theorem "last (inOrder xt) = rightmost xt" 
proof (induct xt)
  case (Leaf x)
  then show ?case by simp
next
  case (Node x1a xt1 xt2)
  assume hyp:"last (inOrder xt2) = rightmost xt2"
  have "last (inOrder (Node x1a xt1 xt2)) = last (inOrder xt1 @ x1a  #  inOrder xt2)" by simp
  also have "\<dots> = last (inOrder xt2)" using helper1 by auto     
  finally show ?case using hyp by auto
qed
  
lemma helper2 : "length xs > 0 \<Longrightarrow> hd (xs @ ys) = hd xs" by (induct xs, auto)  
  
theorem "hd (inOrder xt) = leftmost xt" 
proof (induct xt)
  case (Leaf x)
  then show ?case by simp
next
  case (Node x1a xt1 xt2)
  assume hyp:"hd (inOrder xt1) = leftmost xt1"
  have " hd (inOrder (Node x1a xt1 xt2)) = hd (inOrder xt1 @ x1a # inOrder xt2)" by simp
  also have "\<dots> = hd (inOrder xt1)" using helper1 helper2 by auto
  then show ?case using hyp by auto
qed
  
theorem "hd (preOrder xt) = last (postOrder xt)" 
proof (induct xt)
  case (Leaf x)
  then show ?case by simp
next
  case (Node x1a xt1 xt2)
  then show ?case by simp
qed
  
theorem "hd (preOrder xt)  = root xt" 
proof (induct xt)
  case (Leaf x)
  then show ?case by (auto simp add : root_def)
next
  case (Node x1a xt1 xt2)
  then show ?case by (auto simp add: root_def) 
qed
  
lemma "let xt = Node (1 :: int) (Leaf 2) (Leaf 3) in (hd (inOrder xt) = root xt) \<Longrightarrow> False" by (simp add : root_def)
    
theorem "last (postOrder xt) = root xt" by (induct xt, auto simp add : root_def)
  