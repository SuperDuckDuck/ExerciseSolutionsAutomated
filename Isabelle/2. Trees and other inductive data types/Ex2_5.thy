theory Ex2_5
  imports Main 
begin 
  
datatype form = T | Var nat | And form form | Xor form form
  
definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor x y= ((x \<and> \<not>y) \<or> (\<not>x \<and> y))"
  
notation 
  xor (infixr "<**>" 50)
  
declare xor_def [simp]  
  
primrec evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool" where 
  "evalf _ T = True"|
  "evalf p (Var n) = p n"|
  "evalf p (And f1 f2) = (evalf p f1 \<and> evalf p f2)"|
  "evalf p (Xor f1 f2) = (evalf p f1 <**>  evalf p f2)"
  
primrec evalm :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> bool" where 
  "evalm P [] = True"|
  "evalm P (x#xs) = (P x \<and> evalm P xs)"
  
  
primrec evalp :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list list \<Rightarrow> bool" where
  "evalp P [] = False"|
  "evalp P (x#xs) = (evalm P x <**> evalp P xs)"
  
lemma "((a <**> b)  \<and> (c <**> d)) = ((a \<and> c) <**> (a \<and> d) <**> (b \<and> c) <**> (b \<and> d))" by auto
  
primrec mulpp :: "nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list " where 
  "mulpp [] _ = [] "|
  "mulpp (x#xs) ys = (map (op @ x) ys) @ mulpp xs ys"
  
primrec poly :: "form \<Rightarrow> nat list list" where
  "poly T = [[]]"|
  "poly (Var i)= [[i]]"|
  "poly (And f1 f2) = mulpp (poly f1) (poly f2)"|
  "poly (Xor f1 f2) = poly f1 @ poly f2"

lemma helper1 : "evalp e (xs @ ys) = (evalp e xs <**> evalp e ys)"  by (induction xs ; auto)
    
lemma helper2 : "evalp e (map (op @ a) f2) = (evalp e [a] \<and> evalp e f2)" 
proof (induction f2)
  case Nil
  then show ?case by simp
next
  case (Cons aa f2)
  assume hyp:"evalp e (map (op @ a) f2) = (evalp e [a] \<and> evalp e f2)"
  have "evalp e (map (op @ a) (aa # f2)) = evalp e ((a @ aa) # map (op @ a) f2)" by simp
  also have "\<dots> = (evalm e (a @ aa) <**> evalp e (map (op @ a) f2))" by simp
  also have "\<dots> =  (evalm e (a @ aa) <**> (evalp e [a] \<and> evalp e f2))" using hyp by simp
  finally have tmp:"evalp e (map (op @ a) (aa # f2)) = (evalm e (a @ aa) <**> (evalp e [a] \<and> evalp e f2))" by assumption
      
  have tmp2:"evalm e (a @ aa) = (evalm e a \<and> evalm e aa)" by (induction a ; simp)
      
  have "(evalp e [a] \<and> evalp e (aa # f2)) = (evalm e a \<and> evalp e (aa # f2))" by simp
  also have "\<dots> = (evalm e a \<and> (evalm e aa <**> evalp e  f2))" by simp
  also have "\<dots> = ((evalm e a \<and> evalm e aa) <**> (evalm e a  \<and> evalp e  f2))" by auto
  also have "\<dots> = ((evalm e (a@aa)) <**> (evalm e a  \<and> evalp e  f2))" using tmp2 by simp
  also have "\<dots> = ((evalm e (a@aa)) <**> (evalp e [a]  \<and> evalp e  f2))" by simp
  finally  show ?case using tmp by simp
qed
  
lemma helper3: "evalp e (mulpp f1 f2) = (evalp e f1 \<and> evalp e f2)"  
proof (induction f1)
  case Nil
  then show ?case by simp
next
  case (Cons a f1)
  assume hyp:"evalp e (mulpp f1 f2) = (evalp e f1 \<and> evalp e f2)"
    
  have "evalp e (mulpp (a # f1) f2) = evalp e (map (op @ a) f2 @ mulpp f1 f2)" by simp
  also have "\<dots> = (evalp e (map (op @ a) f2) <**> evalp e (mulpp f1 f2))" using helper1 by simp
  also have "\<dots> = (evalp e (map (op @ a) f2) <**> ((evalp e f1 \<and> evalp e f2)))" using hyp by simp
  finally have tmp1:"evalp e (mulpp (a # f1) f2) = (evalp e (map (op @ a) f2) <**> (evalp e f1 \<and> evalp e f2))" by assumption
      
  have "(evalp e (a # f1) \<and> evalp e f2) = ((evalm e a <**> evalp e f1) \<and> evalp e f2)" by simp
  also have "\<dots> = ((evalm e a \<and> evalp e f2 ) <**> (evalp e f1 \<and> evalp e f2))" by auto
  also have "\<dots> = (evalp e (map (op @ a) f2) <**> (evalp e f1 \<and> evalp e f2))" using helper2 by simp
  finally show "evalp e (mulpp (a # f1) f2) = (evalp e (a # f1) \<and> evalp e f2)" using tmp1 by simp
qed
  
  
theorem poly_correct : "evalf e f = evalp e (poly f)" 
proof (induction f)
  case T
  then show ?case by simp
next
  case (Var x)
  then show ?case by simp
next
  case (And f1 f2)
  then show ?case using helper3 by simp
next
  case (Xor f1 f2)
  then show ?case by (simp add: helper1)
qed
  