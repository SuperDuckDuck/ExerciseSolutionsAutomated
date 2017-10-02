theory Ex2_4 
  imports Main 
begin 
  
datatype bdd = Leaf bool | Branch bdd bdd 
  
primrec eval :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> bool" where 
  "eval _ _ (Leaf b) = b"|
  "eval P n (Branch l r) = (if P n  then eval P (Suc n) l else eval P (Suc n) r)"
  
primrec bdd_unop :: "(bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd" where
  "bdd_unop  f (Leaf b)=  (Leaf (f b))"|
  "bdd_unop f (Branch l r) = Branch (bdd_unop f l) (bdd_unop f r)"
  
fun bdd_binop :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd \<Rightarrow> bdd" where 
  "bdd_binop f (Leaf b) (Leaf b2) = (Leaf (f b b2))"|
  "bdd_binop f (Leaf b) (Branch l r) =  Branch (bdd_binop f (Leaf b) l) (bdd_binop f (Leaf b) r)"|
  "bdd_binop f (Branch l r) (Leaf b) = Branch (bdd_binop f l (Leaf b)) (bdd_binop f r (Leaf b))"|
  "bdd_binop f (Branch l1 r1) (Branch l2 r2) = Branch (bdd_binop f l1 l2) (bdd_binop f r1 r2)"
  
theorem "size (bdd_unop f bdd) = size bdd" by (induction bdd, simp_all)
    
theorem "bdd_unop id bdd = bdd" by (induction bdd, simp_all)

theorem main1 : "\<forall>i . eval f i (bdd_unop f2 bdd) = f2 (eval f i bdd)" by (induction bdd ; simp)
    
theorem main2: "\<forall> i . eval f i (bdd_binop f2 bdd1 bdd2) = f2 (eval f i bdd1) (eval f i bdd2)"
proof (rule allI)
  fix i
  show  "eval f i (bdd_binop f2 bdd1 bdd2) = f2 (eval f i bdd1) (eval f i bdd2)"
  proof (induction bdd1 arbitrary  : i bdd2)
    case (Leaf x)
    then show ?case 
    proof (induction bdd2 arbitrary : i)
      case (Leaf xx)
      then show ?case by simp
    next
      case (Branch bdd21 bdd22)
      then show ?case by simp
    qed
  next
    case (Branch bdd11 bdd12)
    assume hyp1:"\<And>i bdd2 . eval f i (bdd_binop f2 bdd11 bdd2) = f2 (eval f i bdd11) (eval f i bdd2)"
      and hyp2:"\<And> i bdd2 . eval f i (bdd_binop f2 bdd12 bdd2) = f2 (eval f i bdd12) (eval f i bdd2)"
    show ?case 
    proof (cases "f i")
      case True
        assume c1:"f i"
      then show ?thesis 
      proof (cases bdd2)
        case (Leaf x1)
        assume c2:"bdd2 = Leaf x1"
        have "eval f i (bdd_binop f2 (Branch bdd11 bdd12) bdd2) = eval f (Suc i) (bdd_binop f2 bdd11 bdd2)" using c1 c2 by simp
        also have "\<dots> = f2 (eval f (Suc i) bdd11) (eval f (Suc i) bdd2)" using hyp1 by simp
        also have "\<dots> = f2 (eval f i (Branch bdd11 bdd12)) (eval f i bdd2)" using c1 c2 by simp
        finally show ?thesis by assumption
      next
        case (Branch x21 x22)
        then show ?thesis using hyp1 c1 by simp
      qed
    next
      case False
      then show ?thesis using hyp1 hyp2 by (cases bdd2 , simp_all)
    qed
  qed
qed
  
definition bdd_and :: "bdd \<Rightarrow> bdd \<Rightarrow> bdd" where 
  "bdd_and bdd1 bdd2 = bdd_binop (op \<and>) bdd1 bdd2"
  
definition "bdd_or =  bdd_binop op \<or>"
 
definition "bdd_not = bdd_unop (\<lambda>x \<Rightarrow> \<not>x)"
  
definition "bdd_xor = bdd_binop  (\<lambda> x y . (x \<and> \<not>y) \<or> (\<not>x \<and> y))"
  
theorem lem1 : "eval f i (bdd_and t1 t2) = (eval f i t1 \<and> eval f i t2)"
proof - 
  have "\<forall> i . eval f i (bdd_binop op \<and> t1 t2) = op \<and> (eval f i t1) (eval f i t2)" by (rule main2)
  hence "eval f i (bdd_binop op \<and> t1 t2) = op \<and> (eval f i t1) (eval f i t2)" by (rule allE)
  thus ?thesis using bdd_and_def by simp    
qed
  
theorem "\<forall>i .eval f i (bdd_or t1 t2) = (eval f i t1 \<or> eval f i t2)" using main2 by (simp add : bdd_or_def)

definition bxor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "bxor a b = ((a \<and> \<not>b) \<or> (\<not>a \<and> b))" 
    
notation 
  bxor (infixl "<*>" 50)
  
theorem lem2 : "\<forall>i .eval f i (bdd_xor t1 t2) = (eval f i t1 <*> eval f i t2)" using main2 by (simp add : bdd_xor_def bxor_def)
    
theorem "\<forall>i .eval f i (bdd_not t1) = (\<not>(eval f i t1))" using  main1 by (simp add : bdd_not_def)

primrec bdd_var :: "nat \<Rightarrow> bdd" where
  "bdd_var 0 = Branch (Leaf True) (Leaf False)"|
  "bdd_var (Suc n) = Branch (bdd_var n) (bdd_var n)"

theorem "\<forall>i . eval f i (bdd_var n) = f (i + n)" by (induction n; simp)

    
datatype form = T | Var nat | And form form | Xor form form
  
definition "xor = bxor"
  
primrec evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool" where 
  "evalf e T = True"|
  "evalf e (Var i) = e i"|
  "evalf e (And f1 f2) = (evalf e f1 \<and> evalf e f2)"|
  "evalf e (Xor f1 f2) =  ((evalf e f1) <*> (evalf e f2))"
  
primrec mk_bdd :: "form \<Rightarrow> bdd" where 
  "mk_bdd T = Leaf True"|
  "mk_bdd (Var i) = bdd_var i"|
  "mk_bdd (And f1 f2) =  bdd_and (mk_bdd f1) (mk_bdd f2)"|
  "mk_bdd (Xor f1 f2) = bdd_xor (mk_bdd f1) (mk_bdd f2)"
  
lemma helper1 : "f x = evalf f (Var x)" by (induction x, simp_all)
    
lemma helper2 : "f (x + n) = eval f n (bdd_var x)" 
proof (induction x arbitrary : n)
  case 0
  then show ?case by simp
next
  case (Suc x)
    assume hyp:"\<And>n . f (x + n) = eval f n (bdd_var x)"
    then show ?case using hyp[of "Suc n"] by (cases "f (x + n)"; cases "f n" ; simp)
qed
  

  
theorem mk_bdd_correct : "eval e 0 (mk_bdd f) = evalf e f" 
proof (induction f)
  case T
  then show ?case by simp
next
  case (Var x)
  then show ?case 
  proof (induction x)
    case 0
    then show ?case by simp
  next
    case (Suc x)
    assume hyp:"eval e 0 (mk_bdd (Var x)) = evalf e (Var x)"
    then show ?case using helper1 helper2 by simp
  qed
next
  case (And f1 f2)
  assume hyp1:"eval e 0 (mk_bdd f1) = evalf e f1"
    and hyp2:"eval e 0 (mk_bdd f2) = evalf e f2"
  have "eval e 0 (mk_bdd (And f1 f2))  = eval e 0 (bdd_and (mk_bdd f1) (mk_bdd f2))" by simp
  also have "\<dots> = (eval e 0 (mk_bdd f1) \<and> eval e 0 (mk_bdd f2))" using lem1 by simp
  finally show ?case using hyp1 hyp2 by simp
next
  case (Xor f1 f2)
  then show ?case using lem2 by simp
qed
  