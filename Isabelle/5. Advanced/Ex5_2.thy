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

fun merge  :: "nat list \<times> nat list \<Rightarrow> nat list" where
"merge (l1 , []) = l1"|
"merge ([] , l2) = l2"|
"merge ((x # xs),(y # ys)) = (if x \<le> y then x # merge (xs ,(y#ys)) else y # merge ((x#xs), ys) ) "

fun msort :: "nat list \<Rightarrow> nat list" where
"msort [] = []"|
"msort [x] = [x]"|
"msort xs =  merge (msort (take (length xs div 2) xs) , msort (drop (length xs div 2) xs))"


lemma lem1: "le x xs \<Longrightarrow> le x ys \<Longrightarrow> le x (xs @ ys)" by (induction xs ; auto)

lemma lem2: "\<not>le x xs \<Longrightarrow> le x (xs @ ys) = False" by (induction xs ;auto)

lemma lem3:"\<forall>x . x \<in> set xs \<longrightarrow> le x ys \<Longrightarrow> sorted (xs @ ys) = (sorted xs \<and> sorted ys)" 
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume hyp1:"\<forall>x. x \<in> set xs \<longrightarrow> le x ys \<Longrightarrow> Ex5_2.sorted (xs @ ys) = (Ex5_2.sorted xs \<and> Ex5_2.sorted ys)"
     and hyp2:"\<forall>x. x \<in> set (a # xs) \<longrightarrow> le x ys"
  from hyp1 hyp2 have tmp:"Ex5_2.sorted (xs @ ys) = (Ex5_2.sorted xs \<and> Ex5_2.sorted ys)" by simp
  from hyp2 have tmp2:"le a ys" by simp
  show ?case using lem1[of a xs ys] lem2[of a xs ys] tmp tmp2  by (cases "le a xs"; simp)
qed


lemma lem4:"sorted (a#xs) \<Longrightarrow> a \<le> b \<Longrightarrow> merge (a#xs , b#ys) = merge (xs , a#b#ys)" 
proof (induction xs arbitrary : ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by auto
qed

lemma lem5 : "le y ys \<Longrightarrow> x \<le> y \<Longrightarrow> le x ys" by (induction ys ; auto)

lemma lem6:"sorted (x#xs) \<Longrightarrow> sorted (y#ys) \<Longrightarrow> merge (x#xs , y#ys) = x # merge (xs , y#ys) \<Longrightarrow> le x (y#ys)" 
proof -
  assume hyp1:"sorted (x#xs)"
     and hyp2:"sorted (y#ys)"
     and hyp3:"merge (x#xs , y#ys) = x # merge (xs , y#ys)"
  from hyp3 have "x \<le> y" by (cases "x \<le> y" ; auto)
  with hyp1 hyp2 show ?thesis using lem5 by auto
qed

lemma lem7:"sorted (x#xs) \<Longrightarrow> sorted ys \<Longrightarrow> merge (x#xs , ys) = x # merge (xs ,ys) \<Longrightarrow> le x ys" 
proof -
  assume hyp1:"sorted (x#xs)"
     and hyp2:"sorted ys"
     and hyp3:"merge (x#xs , ys) = x # merge (xs , ys)"
  show ?thesis 
  proof (cases ys)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a list)
    assume c1:"ys = a # list"
    with hyp3 have "x \<le> a" by (cases "x \<le> a" ; auto)
    with hyp2 hyp1 show ?thesis using lem5 c1 by auto
  qed
qed

lemma lem8:"le x xs \<Longrightarrow> le x ys \<Longrightarrow> sorted (x #merge (xs ,ys)) = sorted (merge (xs,ys))" 
proof -
  assume hyp1:"le x xs"
    and hyp2:"le x ys"
  show ?thesis 
  proof (cases xs)
    case Nil
    assume c1:"xs = []"
    then show ?thesis 
    proof (cases ys)
      case Nil
      then show ?thesis using c1 by simp
    next
      case (Cons a list)
      then show ?thesis by (metis c1 Cons merge.simps(2) sorted.simps(2) hyp2)
    qed
  next
    case (Cons a list)
    assume c1:"xs = a # list"
    show ?thesis 
    proof(cases ys)
      case Nil
      show ?thesis by (metis merge.simps(1) sorted.simps(2) Nil hyp1)
    next
      case (Cons aa list2)
      have tmp:"le x (a # list)" using c1 hyp1 by simp
      have tmp2:"le x (aa#list2)" using Cons hyp2 by simp
      show ?thesis 
      proof (cases "a \<le> aa")
        case True   
        have "sorted (x # merge (xs, ys)) = sorted (x # merge (a#list, aa#list2)) " using Cons c1 by simp
        also have "\<dots> =  sorted (x # a # merge (list, aa#list2))" using True by simp
        also have "\<dots> = sorted (a # merge (list , aa#list2))" by (metis tmp le.simps(2) sorted.simps(2) lem5[of a "merge (list , aa#list2)" x])
        finally show ?thesis using c1 True Cons by simp
      next
        case False
        have "sorted (x # merge (xs, ys)) = sorted (x # merge (a#list , aa#list2)) " using c1 Cons by simp
        also have "\<dots> = sorted (aa # merge (a#list , list2))" by (metis lem5[of aa "merge (a#list , list2)" x] le.simps(2) tmp2 sorted.simps(2) False merge.simps(3))
        finally show ?thesis using c1 Cons False by simp
      qed
    qed
  qed
qed

lemma lem9:"(x \<in> set (merge t)) = (x \<in> set (fst t) \<or> x \<in> set (snd t))" by (induct t rule : merge.induct ; auto)

lemma "(x \<in> set (merge (xs,ys))) = (x \<in> set xs \<or> x \<in> set ys)" by (induct "(xs,ys)" arbitrary : xs ys rule : merge.induct ; auto)

lemma lem10:"(x \<in> set (merge (xs,ys))) = (x \<in> set xs \<or> x \<in> set ys)" using lem9 by auto

lemma "set (merge (xs,ys)) = set xs \<union> set ys" using lem10 by auto

lemma lem11:"le x (merge (xs,ys)) = (le x xs \<and> le x ys)" 
proof (induction "(xs,ys)" arbitrary : xs ys rule : merge.induct )
case (1 l1)
  then show ?case by simp
next
  case (2 v va)
  then show ?case by simp
next
  case (3 x xs y ys)
  then show ?case by auto
qed

lemma lem12:"sorted (merge (xs,ys)) = (sorted (xs) \<and> sorted (ys))"
proof (induct "(xs,ys)" arbitrary : xs ys  rule : merge.induct )
  case (1 l1)
  then show ?case by simp
next
  case (2 v va)
  then show ?case by simp
next
  case (3 x xs y ys)
  assume hyp1:"x \<le> y \<Longrightarrow> Ex5_2.sorted (merge (xs, y # ys)) = (Ex5_2.sorted xs \<and> Ex5_2.sorted (y # ys))"
     and hyp2:"\<not> x \<le> y \<Longrightarrow> Ex5_2.sorted (merge (x # xs, ys)) = (Ex5_2.sorted (x # xs) \<and> Ex5_2.sorted ys)"
  show ?case 
  proof (cases "x \<le> y")
    case True
    assume c1:"x \<le> y"
    with hyp1 have tmp:"Ex5_2.sorted (merge (xs, y # ys)) = (Ex5_2.sorted xs \<and> Ex5_2.sorted (y # ys))" by simp
    show ?thesis
    proof(cases "le x (merge (xs , y #ys))")
      case True
      show ?thesis  by (metis True tmp c1 merge.simps(3) sorted.simps(2)  lem11)
    next
      case False
      then show ?thesis by (metis Ex5_2.sorted.simps(2) c1 lem11 lem6 merge.simps(3))
    qed
  next
    case False
    assume c1:"\<not> x \<le> y"
    with hyp2 have tmp:"Ex5_2.sorted (merge (x # xs, ys)) = (Ex5_2.sorted (x # xs) \<and> Ex5_2.sorted ys)" by simp
    show ?thesis 
    proof (cases "le y (merge (x#xs , ys))")
      case True
      show ?thesis by (metis True tmp c1 sorted.simps(2) merge.simps(3) lem11)
    next
      case False
      assume c2:"\<not> le y (merge (x # xs, ys))"
      show ?thesis 
      proof (cases  "sorted (x#xs)")
        case True
        assume c3:"sorted (x#xs)"
        then show ?thesis 
        proof (cases "sorted (y#ys)")
          case True
          from c1 c3 have "le y (x#xs)" using lem5 by auto
          then show ?thesis using c1 c2 c3 lem11[of y "x#xs" ys] by simp
        next
          case False
          then show ?thesis using c1 c2 by simp
        qed

      next
        case False
        then show ?thesis using c1 c2 by auto
      qed 
    qed
  qed
qed


theorem "sorted (msort xs)"
proof (induction xs rule : msort.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 v vb vc)
  then show ?case using lem12 by simp
qed


lemma helper:"count (merge (xs,ys)) x = count xs x + count ys x" 
proof (induction "(xs,ys)" arbitrary : xs ys rule : merge.induct)
case (1 l1)
  then show ?case by simp
  next
case (2 v va)
  then show ?case by simp
  next
  case (3 x xs y ys)
  then show ?case by auto
qed


lemma helper2:"count xs x + count ys x = count (xs@ys) x" by (induction xs ; auto)

theorem "count (msort xs) x = count xs x" 
proof (induction xs rule : msort.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 v vb vc)
  let ?ex1="msort (take (length (v # vb # vc) div 2) (v # vb # vc))"
  let ?ex2="msort (drop (length (v # vb # vc) div 2) (v # vb # vc))"
  let ?ex3="take (length (v # vb # vc) div 2) (v # vb # vc)"
  let ?ex4="drop (length (v # vb # vc) div 2) (v # vb # vc)"

  have "count (msort (v # vb # vc)) x = count (merge (?ex1, ?ex2)) x" by simp
  also have "\<dots>  = count ?ex1 x + count ?ex2 x" using helper by simp
  also have "\<dots> = count ?ex3 x + count ?ex4 x" using 3 by simp
  also have "\<dots> = count (?ex3@?ex4) x" using helper2 by simp
  also have "\<dots> = count (v#vb#vc) x" using append_take_drop_id[of "length (v#vb#vc) div 2" "(v#vb#vc)"]by simp
  finally show ?case by assumption
qed

fun merge2 :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list"
where
 "merge2 [] ys = ys" |
 "merge2 xs [] = xs" |
 "merge2 (x # xs) (y # ys) = (
   if x \<le> y
     then x # merge2 xs (y # ys)
     else y # merge2 (x # xs) ys)"

fun msort2 :: "nat list \<Rightarrow> nat list"
where
 "msort2 [] = []" |
 "msort2 [x] = [x]" |
 "msort2 xs = (
   let half = length xs div 2 in
   merge2 (msort2 (take half xs)) (msort2 (drop half xs)))"


lemma [simp]: "le x (merge2 xs ys) = (le x xs \<and> le x ys)" by (induction xs ys rule : merge2.induct ; auto)

lemma [simp]: "sorted (merge2 xs ys) = (sorted xs \<and> sorted ys)" 
proof (induction xs ys rule : merge2.induct)
  case (1 ys)
  then show ?case by simp
next
  case (2 v va)
  then show ?case by simp
next
  case (3 x xs y ys)
  then show ?case using lem5 by (cases "x \<le> y" ; auto) (*takes some time*)
qed

theorem "sorted (msort2 xs)" by (induction xs rule : msort2.induct ;auto)

lemma helper3:"count (merge2 xs ys) x = count xs x + count ys x" by (induction xs ys rule : merge2.induct ; simp)

theorem "count (msort2 xs) x = count xs x" 
proof (induction xs rule : msort.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 v vb vc)
  let ?ex1="take (length (v # vb # vc) div 2) (v # vb # vc)"
  let ?ex2="drop (length (v # vb # vc) div 2) (v # vb # vc)"
  have "count (msort2 (v # vb # vc)) x = count (merge2  (msort2 ?ex1) (msort2 ?ex2)) x" by simp
  also have "\<dots> = count (msort2 ?ex1) x + count (msort2 ?ex2) x" using helper3 by simp
  finally show ?case by (metis helper2 append_take_drop_id 3 )
qed


