theory Ex1_1 
  imports ZF 
begin 

consts 
  snoc :: "[i,i] \<Rightarrow> i"

primrec 
"snoc ([] , val)  = [val]"
"snoc (Cons(x , xs) , val) = Cons (x, (snoc (xs , val)))"


lemma snoc_app : "xs \<in> list (A) \<Longrightarrow> ys \<in> list(A) \<Longrightarrow> val \<in> A \<Longrightarrow> snoc (app(xs,ys), val) = app(xs , snoc (ys , val))"  
proof (induct_tac xs)
  assume h1:"ys \<in> list(A)"
     and h2:"val \<in> A"
  show "snoc([] @ ys, val) = [] @ snoc(ys, val)" by auto
next
  fix a l
  assume h1:"ys \<in> list(A)"
     and h2:"val \<in> A"
     and h3:"a \<in> A"
     and h4:"l \<in> list(A)"
     and h5:"snoc(l @ ys, val) = l @ snoc(ys, val)"
  show "snoc(Cons(a, l) @ ys, val) = Cons(a, l) @ snoc(ys, val)" using h5 by simp
qed

notation
  Cons ( infix  "$$" 50)

theorem rev_cons : "xs \<in> list(A) \<Longrightarrow> ys \<in> list(A) \<Longrightarrow> val \<in> A \<Longrightarrow> rev (val $$ xs) = snoc ((rev(xs)) , val)" 
proof (induct_tac xs)
  assume h1:"ys \<in> list(A)"
     and h2:"val \<in> A"
  show "rev( val $$ []) = snoc(rev([]), val)" by simp
next 
  fix a l 
  assume h1:"ys \<in> list(A)"
     and h2:"val \<in> A"
     and h3:"a \<in> A"
     and h4:"l \<in> list(A)"
     and h5:"rev(val $$ l) = snoc(rev(l), val)"

  have "rev(val $$ (a $$ l)) = rev(a $$ l) @ [val]" by simp
  also have "\<dots> = rev (l) @ [a] @ [val]" by (subst rev.simps , subst app_assoc , rule rev_type , rule h4 , rule refl)
  also have "\<dots> = rev (l) @ [a] @ snoc ([],val)" by simp
  also have "\<dots> = rev (l) @ snoc ([a],val)" by simp
  also have "\<dots> = snoc (rev(l) @ [a], val)" using h2 h3 h4 snoc_app by auto
  finally show "rev(val $$ (a $$ l)) = snoc(rev(a $$ l), val)" by simp
qed