theory Ex2_2
  imports Main 
begin 
  
primrec sum :: "nat list \<Rightarrow> nat"  where 
  "sum [] = 0"|
  "sum (x#xs) = x + sum xs"


  
lemma sum_foldr: "sum xs = foldr (op +) xs 0" by (induct xs, simp_all)
    
lemma length_foldr : "length xs = foldr (\<lambda>x res . 1 + res) xs 0" by (induct xs, simp_all)
    
lemma "sum (map (\<lambda>x . x +  3) xs) = foldr (\<lambda> x res . res + x + 3) xs 0" by (induct xs, simp_all)
    
lemma "foldr g (map f xs) a  = foldr (g o f) xs a" by (induct xs , simp_all)
    
primrec rev_acc :: "['a list , 'a list] \<Rightarrow> 'a list" where 
  "rev_acc [] res = res"|
  "rev_acc (x#xs) res = rev_acc xs (x#res)"
  
lemma rev_acc_foldl : "rev_acc xs a = foldl (\<lambda> ys x . x # ys) a xs" 
proof (induct xs arbitrary : a)
  case Nil
  then show ?case by simp
next
  case (Cons aa xs)
  assume hyp:"\<And> a . rev_acc xs a = foldl (\<lambda>ys x. x # ys) a xs"
  then show ?case by simp
qed
  
lemma sum_append [simp]: "sum (xs @ ys) = sum xs + sum ys" by (induct xs; simp)
    
lemma foldr_append : "\<forall>e . f a e = e \<Longrightarrow> \<forall>b c d . f d (f b c) = f (f d b) c \<Longrightarrow>foldr f (xs @ ys) a = f (foldr f xs a) (foldr f ys a)"  
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

definition prod :: "nat list \<Rightarrow> nat" where 
  "prod ls = fold (op *) ls 1"
  
declare prod_def [simp]

lemma helper1 :"fold (op *) xs (a::nat) = a * fold (op *) xs 1"   
proof (induct xs arbitrary : a)
  case Nil
  then show ?case by simp
next
  case (Cons aa xs)
  assume hyp:"\<And> a . fold op * xs a = a * fold op * xs 1"
  have "a * fold op * (aa # xs) 1 = a * fold op * xs aa" by simp
  also have "\<dots> = a * aa * fold op * xs 1" by (subst hyp, simp)
  finally have "a * fold op * (aa # xs) 1 = a * aa * fold op * xs 1" by assumption
  note tmp=this
  have "fold op * (aa # xs) a =   fold op * xs (aa*a)" by simp
  also have "\<dots> = (aa * a) * fold op * xs 1" by (subst hyp, simp)
  finally  show ?case using tmp by auto
qed
  
  
lemma helper2 : "fold (op *) (xs @ ys) (1::nat) = fold (op *) xs 1 * fold (op *) ys 1" 
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume hyp:"fold op * (xs @ ys) 1 = fold op * xs 1 * fold op * ys 1"
  have "fold op * ((a # xs) @ ys) 1 =  fold op * (a # (xs @ ys)) 1 " by simp
  also have "\<dots> = ( fold (op * ) (xs @ ys) \<circ> (op * a)) 1" by simp
  also have "\<dots> =  fold (op * ) (xs @ ys)  (op * a 1) " by simp
  also have "\<dots> = fold (op * ) (xs @ ys) a" by simp
  also have "\<dots> =a * fold (op * ) (xs @ ys) 1" by (subst helper1, rule refl)
  also have "\<dots> = a * fold (op * ) xs 1 * fold (op * ) ys 1" by (simp only : hyp)
  also have "\<dots> = fold (op * ) xs a * fold (op * ) ys 1" by (subst (3) helper1, rule refl)
  finally show ?case by simp 
qed
  
  
lemma "prod (xs @ ys) = prod xs * prod ys" 
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume hyp:"Ex2_2.prod (xs @ ys) = Ex2_2.prod xs * Ex2_2.prod ys"
  have "Ex2_2.prod ((a # xs) @ ys) = fold  (op *) ((a # xs) @ ys) 1" by (simp)
  also have "\<dots> = fold (op *) (a # xs) 1 * fold (op *) ys 1" by (subst helper2, rule refl)
  finally show ?case by simp 
qed
  
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
  
primrec preorder :: "'a tree \<Rightarrow> 'a list" where
  "preorder Tip  = []"|
  "preorder (Node lt val rt) = val # preorder lt @ preorder rt "
  
  
primrec postorder :: "'a tree \<Rightarrow> 'a list" where 
  "postorder Tip = []"|
  "postorder (Node lt val rt) = postorder lt @ postorder rt @ [val]"
  
  
primrec postorder_acc :: "['a tree , 'a list] \<Rightarrow> 'a list" where 
  "postorder_acc Tip acc = acc"|
  "postorder_acc (Node lt val rt) acc = (let tmp = postorder_acc rt (val # acc) in postorder_acc lt tmp)"
  
lemma "postorder_acc t xs = postorder t @ xs" 
proof (induct t arbitrary : xs)
  case Tip
  then show ?case by simp
next
  case (Node t1 x2 t2)
  then show ?case by simp
qed

primrec foldl_tree :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a tree \<Rightarrow> 'b" where 
  "foldl_tree _ acc Tip = acc"|
  "foldl_tree f acc (Node lt val rt) = (let tmp = foldl_tree f (f acc val) rt in foldl_tree f tmp lt) "
  
  
lemma "\<forall> a. postorder_acc t a = foldl_tree (\<lambda> xs x . Cons x xs) a t" by (induct t, simp_all)
    
definition tree_sum :: "nat tree \<Rightarrow> nat" where 
  "tree_sum = foldl_tree (op +) 0"
  
declare tree_sum_def [simp]  
  
lemma helper3 : fixes x::nat shows  " x + foldl_tree (op +) 0 t = foldl_tree (op +) x t"
proof (induction t arbitrary : x)
  case Tip
  then show ?case by simp
next
  case (Node t1 x2 t2)
    
  assume h1:"\<And>x .x + foldl_tree op + 0 t1 = foldl_tree op + x t1"
     and h2:"\<And>x. x + foldl_tree op + 0 t2 = foldl_tree op + x t2"
     
  have "x + foldl_tree op + 0 (Node t1 x2 t2)  = x + foldl_tree op + (foldl_tree op + x2 t2) t1" by simp
  also have "\<dots> = x + (foldl_tree op + x2 t2 + foldl_tree op + 0 t1)" by (subst h1, rule refl)
  also have "\<dots> = x + foldl_tree op + x2 t2 + foldl_tree op + 0 t1" by simp
  also have "\<dots> = x + (x2 + foldl_tree op + 0 t2) + foldl_tree op + 0 t1" by (simp add : h2)
  also have "\<dots> =  x + x2 + foldl_tree op + 0 t2 + foldl_tree op + 0 t1" by simp
  also have "\<dots> = foldl_tree op + (op + x x2) t2 + foldl_tree op + 0 t1" by (simp add : h2)
  also have "\<dots> = foldl_tree op + (foldl_tree op + (op + x x2) t2) t1" by (simp add : h1)
  also have "\<dots> =  foldl_tree op + x (Node t1 x2 t2)" by simp
  finally show ?case by assumption
qed
  
  
lemma "tree_sum t = sum (preorder t)"
proof (induct t)
  case Tip
  then show ?case by simp 
next
  case (Node t1 x2 t2)
  assume hyp1:" tree_sum t1 = Ex2_2.sum (preorder t1)"
     and hyp2:"tree_sum t2 = Ex2_2.sum (preorder t2)"
  have "Ex2_2.sum (preorder (Node t1 x2 t2)) = x2 + sum (preorder t1) + sum (preorder t2)" by simp
  also have "\<dots> = x2 + tree_sum t1 + tree_sum t2" by (subst hyp1, subst hyp2, rule refl)
  also have "\<dots> = x2 + foldl_tree (op +) 0 t1 + foldl_tree (op +) 0 t2" by simp
  also have "\<dots> =  x2 + foldl_tree (op +) 0 t2 + foldl_tree (op +) 0 t1" by simp
  also have "\<dots> = foldl_tree (op +) x2 t2 + foldl_tree (op +) 0 t1" by (simp add : helper3)
  also have "\<dots> = foldl_tree (op +) (foldl_tree (op +) x2 t2) t1" by (simp add : helper3)
  also have "\<dots> = foldl_tree (op +) 0 (Node t1 x2 t2)" by simp
  finally show ?case by simp
qed
  
  