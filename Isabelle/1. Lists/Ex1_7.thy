theory Ex1_7
  imports Main 
begin 
  
  
primrec  list_union :: "['a list , 'a list] \<Rightarrow> 'a list" where 
  "list_union [] ys = ys"|
  "list_union (x # xs) ys = (let res = list_union xs ys in if x \<in> set res then res else x # res)"  


lemma "set (list_union xs ys) = set xs \<union> set ys" 
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume hyp:"set (list_union xs ys) = set xs \<union> set ys"
  let ?tmp = "list_union xs ys"
  have "set (list_union (a # xs) ys) =  set (if a \<in> set ?tmp then ?tmp else a # ?tmp )" by simp
  then show ?case 
  proof (cases "a \<in> set ?tmp")
    case True
    assume a:"a \<in> set (list_union xs ys)"
    then show ?thesis by (auto simp add : hyp)
  next
    case False
    then show ?thesis by (auto simp add : hyp)
  qed
qed
  
  
lemma [rule_format] : "distinct xs \<longrightarrow> distinct ys \<longrightarrow> (distinct (list_union xs ys))" 
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume hyp:"distinct xs \<longrightarrow> distinct ys \<longrightarrow> distinct (list_union xs ys)"
  show ?case  
  proof (cases "a \<in> set (list_union xs ys)")
    case True
    assume "a \<in> set (list_union xs ys)"    
    then show ?thesis using hyp by simp 
  next
    case False
    assume "a \<notin> set (list_union xs ys)"
    then show ?thesis using hyp by simp
  qed
qed
  
  
lemma "((\<forall> x \<in> A . P x) \<and> (\<forall> x \<in> B . P x)) \<longrightarrow> (\<forall> x \<in> A \<union> B  . P x)" 
  using [[simp_trace_new mode=full]]
proof -
  {
    assume a:"(\<forall> x \<in> A . P x) \<and> (\<forall> x \<in> B . P x)"
    hence b:"\<forall> x \<in> A . P x" by simp
    from a have c:"\<forall> x \<in> B . P x" by simp
    with b have "\<forall> x \<in> A \<union> B . P x" by auto
  }
  thus ?thesis by (rule impI)
qed
  
lemma "\<forall>x \<in> A . Q (f x) \<Longrightarrow> \<forall> y \<in> f ` A . Q y"  by blast