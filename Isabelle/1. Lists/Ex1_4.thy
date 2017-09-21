theory Ex1_4
  imports Main 
begin 
  
primrec first_pos :: "('a \<Rightarrow> bool)  \<Rightarrow> 'a list \<Rightarrow> nat" where 
  "first_pos _ [] = 0"|
  "first_pos P (x#xs) = (if P x then 0 else (1 + first_pos P xs))"
  
value "first_pos (op = 3) [1::nat,3,5,3,1]"
  
value "first_pos (\<lambda>x .x  > 4 ) [1::nat , 3, 5, 7]"
  
value "first_pos (op < 1 o length ) [[] , [1,2], [3]]"
    (*thm Cons.hyps*)
  (*
lemma "\<forall>x. x \<in> set ls  \<and> (P x = False) \<Longrightarrow> first_pos P ls = length ls" 
proof (induct ls)
  case Nil
  then show ?case by simp
  next
    case (Cons a ls)
    assume hyp1:"\<forall>x. x \<in> set ls \<and> P x = False \<Longrightarrow> first_pos P ls = length ls"
       and hyp2:"\<forall>x. x \<in> set (a # ls) \<and> P x = False"
    show ?case 
    proof (cases "P a")
      case True
      assume a:"P a"
      show ?thesis using hyp2 and a by simp
    next
      case False
      assume a:"\<not> P a"
      show ?thesis 
      proof (cases "a \<in> set ls")
        case True
        assume "a \<in> set ls"
        then show ?thesis using hyp1 hyp2 by fastforce
      next
        case False
        assume b:"a \<notin> set ls"
        from hyp2 have c:"\<forall>x . (x = a \<or> x \<in> set ls) \<and> P x = False" by simp
        then show ?thesis 
      qed
        
    qed    
qed
  *)
lemma "list_all (\<lambda>x. \<not> (P x)) xs \<Longrightarrow> first_pos P xs = length xs"   by (induct xs, auto)
 
lemma "list_all (\<lambda>x. \<not> P x) (take (first_pos P xs) xs)" by (induct xs , auto)
    
lemma "first_pos (\<lambda>x . P x \<or> Q x) xs = min (first_pos P xs) (first_pos Q xs)" by (induct xs , auto)
(*    
lemma "let Q = (\<lambda>x. (x = 2) \<or> (x = 3) \<or> (x = 4)) ; P = (\<lambda>x . (x = 1) \<or> (x = 3) \<or> (x = 4)) ; xs = [1,2,3::nat] ; ys = [1,2,4::nat] in 
      \<not>(\<exists>Fn . (first_pos (\<lambda>x . P x \<and> Q x) xs = Fn (first_pos P xs) (first_pos Q xs)) \<and> (first_pos (\<lambda>x . P x \<and> Q x) ys = Fn (first_pos P ys) (first_pos Q ys)))"  
proof - 
  *)

lemma  " max (first_pos P xs) (first_pos Q xs) \<le> first_pos (\<lambda> x . P x \<and> Q x) xs" by (induct xs , simp_all)
(*    
lemma "\<forall>x  . P x \<longrightarrow> Q x \<Longrightarrow> first_pos P xs = first_pos (\<lambda>x . P x \<and> Q x) xs " by (induct xs , simp_all)
*)
lemma "\<forall>x . P x \<longrightarrow> Q x \<Longrightarrow> first_pos Q xs \<le> first_pos P xs" by (induct xs , simp_all)
    
primrec count :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count _ [] = 0"|
  "count P (x # xs) = (if P x then 1 else 0) + count P xs"
 
lemma helper : "count P (xs @ ys) = count P xs + count P ys" by (induct xs ; simp)   
  
lemma "count P xs = count P (rev xs) " by (induct xs ;  simp add : helper)
    
lemma "count P xs = length (filter P xs)" by (induct xs;  simp add : helper)