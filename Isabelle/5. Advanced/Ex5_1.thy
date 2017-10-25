theory Ex5_1 
  imports Main 
begin 
  
primrec insort :: "nat \<Rightarrow> nat list \<Rightarrow> nat list " where 
  "insort val [] = [val]"|
  "insort val (x#xs) = (if val \<le> x then val#x#xs else x # insort val xs)"
  
primrec le :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where 
  "le _ [] =  True"|
  "le val (x#xs) = ((val \<le> x)  \<and>   le val xs)"

primrec sorted :: "nat list \<Rightarrow> bool" where 
"sorted [] = True"|
"sorted (x#xs) = (le  x xs \<and> sorted xs)"

primrec sort :: "nat list \<Rightarrow> nat list" where 
  "sort [] = [] "|
  "sort (x#xs) = insort x (sort xs)"



lemma lem1 [simp]: "x \<le> y \<Longrightarrow> le y xs \<longrightarrow> le x xs" 
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases "y \<le> a"; simp)
qed

lemma helper:"le x xs \<Longrightarrow> insort x xs = x # xs" by (induction xs ; simp)

lemma helper2: "le a xs \<Longrightarrow> a \<le> x \<Longrightarrow> le a (insort x xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons aa xs)
  then show ?case by (cases "a \<le> aa" ; simp)
qed

lemma helper3:"\<not> le a xs \<Longrightarrow> le  a (insort x xs) = False" by (induction xs; simp)


lemma helper4:"sorted (insort x xs) = sorted xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume hyp:"sorted (Ex5_1.insort x xs) = sorted xs"
  then show ?case 
  proof (cases "x \<le> a")
    case True
    then show ?thesis by (cases "le a xs"; simp)
  next
    case False
    assume c1:"\<not> x \<le> a"
    hence tmp:"x > a" by simp
    then show ?thesis 
    proof (cases "le x xs")
      case True
      assume c2:"le x xs"
      have tmp2:"a \<le> x" using tmp by simp
      have "sorted (Ex5_1.insort x (a # xs)) = sorted (a # Ex5_1.insort x  xs)" using c1 by simp
      also have "\<dots> = sorted (a # x # xs)" using helper c2 by simp
      also have "\<dots> = (le a (x#xs)  \<and> sorted (x # xs))" by simp
      also have "\<dots> = ((a \<le> x \<and> le a xs) \<and> sorted (x #xs))" by simp
      also have "\<dots> = (le a xs \<and> sorted (x#xs))" using c1 by simp
      also have "\<dots> = sorted xs" using c2 tmp2 by simp
      finally have a:"sorted (Ex5_1.insort x (a # xs)) = sorted xs" by assumption

      have  "Ex5_1.sorted (a # xs) = (le a xs \<and> sorted xs)" by simp
      also have "\<dots> = sorted xs" using tmp2 c2 by simp
      
      finally show ?thesis using a by simp
    next
      case False
      assume c2:"\<not> le x xs"
      show ?thesis  
      proof  (cases "le a xs")
        case True
        then show ?thesis using c1 hyp helper2 by simp
      next
        case False
        assume c3:"\<not>le a xs"
        have f1:"sorted (a # xs)  =  (le a xs \<and> sorted xs)" by simp
        also have "\<dots> = (False \<and> sorted xs)" using c3 by simp
        also have "\<dots> = False" by simp
        finally have res1:"sorted (a # xs) = False" by assumption

        have "sorted (insort x (a # xs)) = sorted (a # insort x xs)" using c1 by simp
        also have "\<dots> =False" using c3 helper3 by simp
        finally show ?thesis using res1 by simp
      qed
    qed
  qed
qed



theorem "sorted (sort xs)" 
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume "sorted (sort xs)"
  have "sorted (sort (a#xs)) = sorted (insort a (sort xs))" by simp
  then show ?case using helper4 Cons.IH by simp
qed

primrec count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where 
  "count [] _ = 0"|
  "count (x#xs) val = (if val = x then 1 else 0) + count xs val"

lemma helper5: "count (insort x xs) y= count (x# xs) y" by (induction xs ; auto)

theorem "count (sort xs) x = count xs x" by (induction xs ; auto simp add : helper5)


datatype bintree = leaf | node nat (l:"bintree") (r:"bintree")

primrec tge :: "nat \<Rightarrow> bintree \<Rightarrow> bool" where 
"tge _ leaf = True"|
"tge val (node val2 lft rgt) = (val \<ge> val2 \<and> tge val lft \<and> tge val rgt)"

primrec tle :: "nat \<Rightarrow> bintree \<Rightarrow> bool" where 
"tle _ leaf = True"|
"tle val (node val2 lft rgt) = (val \<le> val2 \<and> tle val lft \<and> tle val rgt)"

primrec tsorted :: "bintree \<Rightarrow> bool" where 
"tsorted leaf = True"|
"tsorted (node val lft rgt) =  (tsorted lft \<and> tsorted rgt \<and> tge val lft \<and>  tle val rgt)"

primrec ins :: "nat \<Rightarrow> bintree \<Rightarrow> bintree" where 
"ins val leaf = node val leaf leaf"|
"ins val (node val2 lft rgt) = (if val < val2 then node val2 (ins val lft ) rgt else node val2 lft (ins val rgt))"

primrec tree_of :: "nat list \<Rightarrow> bintree" where 
"tree_of [] = leaf"|
"tree_of (x#xs) = ins x (tree_of xs)"

lemma helper6:"x < y \<Longrightarrow> tge y t \<Longrightarrow> tge y (ins x t)" by (induction t ; simp)

lemma helper7:"x \<ge> y \<Longrightarrow> tle y t \<Longrightarrow> tle y (ins x t)" by (induction t; simp)

lemma helper8:"\<not>tge x t \<Longrightarrow>  \<not>tge x (ins y t)" by (induction t ; auto)

lemma helper9:"\<not>tle x t \<Longrightarrow> \<not>tle x (ins y t)" by (induction t; auto)

lemma helper10: "tsorted (ins x t) = tsorted t" 
proof (induction t)
  case leaf
  then show ?case by simp
next
  case (node x1 t1 t2)
  assume hyp1:"tsorted (ins x t1) = tsorted t1"
     and hyp2:"tsorted (ins x t2) = tsorted t2"
  show ?case  
  proof (cases "x < x1")
    case True
    assume c1:"x < x1"
    have tmp:"tsorted (ins x (node x1 t1 t2)) = tsorted  (node x1 (ins x t1) t2)" by (simp add : True)
    show ?thesis 
    proof (cases "tge x1 t1")
      case True
      then show ?thesis using hyp1 helper6[of x x1 t1] c1 by (cases "tle x1 t1" ; simp) 
    next
      case False
      then show ?thesis using helper8[of x1 t1 x] c1 by (cases "tle x1 t2" ; simp)
    qed
  next
    case False
    assume "\<not> x < x1"
    hence c1:"x1 \<le> x" by simp
    then show ?thesis using helper7[of x1 x t2] helper9[of x1 t2 x] hyp2 by (cases "tge x1 t1" ; cases "tle x1 t2" ; auto) 
  qed
qed

theorem [simp] : "tsorted (tree_of xs)" 
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case using helper10 by simp
qed

primrec tcount :: "bintree \<Rightarrow> nat  \<Rightarrow> nat" where 
"tcount leaf _  = 0"|
"tcount (node val2 lft rgt) val = (if val = val2 then 1 else 0) + tcount lft val + tcount rgt val"

lemma helper11: "tcount (ins x t) y = (if y = x then 1 else 0) + tcount t y" by (induction t ; auto)

theorem "tcount (tree_of xs) x = count xs x" using helper11 by (induction xs ; simp)

primrec list_of :: "bintree \<Rightarrow> nat list" where 
"list_of leaf = []"|
"list_of (node val lft rgt) = list_of lft @ val # list_of rgt"
(*
lemma helper12:"sorted (xs @ ys) = (sorted xs \<and> sorted ys)" quickcheck
*)
lemma helper111:"list_of (tree_of xs) = sort xs" 
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
qed

lemma helper12:"sorted (list_of (ins x t)) = sorted (list_of t)" 
proof (induction t)
  case leaf
  then show ?case by simp
next
  case (node x1 t1 t2)
  assume hyp1:"sorted (list_of (ins x t1)) = sorted (list_of t1)"
     and hyp2:"sorted (list_of (ins x t2)) = sorted (list_of t2)"
(*  have "sorted (list_of (ins x (node x1 t1 t2))) =  sorted (list_of t1 @ x1 # list_of())"*)
  show ?case 
  proof (cases "x < x1")
    case True
    hence  "sorted (list_of (ins x (node x1 t1 t2))) =  sorted (list_of (ins x t1) @ x1 # list_of t2)" by simp
    then show ?thesis 
  next
    case False
    then show ?thesis sorry
  qed

qed


theorem "sorted (list_of (tree_of xs))" 