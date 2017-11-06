theory Ex5_4 
  imports Main 
begin 

type_synonym intervals = "(nat \<times> nat) list"

type_synonym ntup = "nat \<times> nat"

fun inv2 :: "nat \<Rightarrow> intervals \<Rightarrow> bool" where 
"inv2 _ [] = True"|
"inv2 n ((x,y)#xs) = (n \<le>  x \<and>  x \<le> y \<and> inv2 (y + 2) xs)"


definition inv :: "intervals \<Rightarrow> bool" where 
"inv ls = inv2 0 ls" 


fun set_of :: "intervals \<Rightarrow> nat set" where 
"set_of [] = {}"|
"set_of ((x,y)#xs) = {n. x \<le> n \<and> n  \<le>  y} \<union> set_of xs"


primrec add :: "ntup \<Rightarrow> intervals  \<Rightarrow> intervals" where 
"add val [] = [val]"|
"add nt (x#xs) = (if snd nt < fst x - 1 then nt # x# xs  else (if snd x < fst nt - 1 then x # add nt xs else add (min (fst nt) (fst x), max (snd nt)(snd x)) xs ) ) "
(*
fun rem :: "ntup \<Rightarrow> intervals \<Rightarrow> intervals" where
"rem _ [] = []"|
"rem (s,e) ((x,y)#xs) = (if (s = x) \<and> (e = y) then xs else (x,y) # rem (s,e) xs)"
*)
lemma inv2_monotone : "inv2 m ins \<Longrightarrow> n \<le> m \<Longrightarrow> inv2 n ins"
proof (induction ins arbitrary : m)
  case Nil
  then show ?case by simp
next
  case (Cons a ins)
  have tmp:"inv2 n ins" 
  proof -
    have tmp:"inv2 m (a#ins) = (m \<le> fst a \<and> fst a \<le> snd a \<and> inv2 (snd a + 2) ins)" by (subst prod.collapse[symmetric], subst inv2.simps(2), rule refl) 
    with Cons(2) have tmp1:"inv2 (snd a + 2) ins" by simp
    have "n \<le> snd a + 2" using Cons.prems tmp by linarith
    with Cons(1)[of "snd a + 2"] tmp1 show ?thesis by simp
  qed
  show ?case using  Cons(3) Cons(2) inv2.simps(2) tmp le_trans[of n m "fst a"]  prod.collapse[symmetric, of a]  by metis
qed

declare inv_def[simp]



theorem inv_add : "\<lbrakk> i \<le> j ; inv ins \<rbrakk> \<Longrightarrow> inv (add (i,j) ins)" 
proof (induction ins)
  case Nil
  then show ?case  by simp
next
  case (Cons a ins)
  assume hyp1:"i \<le> j \<Longrightarrow> Ex5_4.inv ins \<Longrightarrow> Ex5_4.inv (add (i, j) ins)"
  and hyp2:"i \<le> j"
  and hyp3:"Ex5_4.inv (a # ins)"
  show ?case 
  proof (cases "j < fst a - 1")
    case True
    have tmp:" (j + 2 \<le> fst a) = (0  \<le> fst a)" using True by simp
    have "inv (add (i, j) (a # ins)) = inv  ((i,j)# a # ins)" using  True add.simps(2)[of "(i,j)" a ins] prod.sel(2)[of i j] by simp 
    also have "\<dots> =  inv2 i  ((i,j)#a#ins)" by simp
    also have "\<dots> = (i \<le> i \<and> i \<le> j \<and>  inv2 (j + 2) (a#ins))" by simp
    also have "\<dots> = inv2 (j + 2) (a#ins)" using hyp2 by simp
    also have "\<dots> = inv2 (j + 2) ((fst a , snd a)#ins)" using prod.collapse[symmetric , of a] by simp
    also have "\<dots> = (0 \<le> fst a \<and> fst a \<le> snd a \<and>  inv2 (snd a + 2) ins)" by (subst inv2.simps(2), subst tmp , rule refl)
    also have "\<dots> = inv (a#ins)" by (subst inv_def , subst (5) prod.collapse[symmetric], subst inv2.simps(2), rule refl)
    finally  show ?thesis using hyp3 by simp
  next
    case False
    assume c1:"\<not> j < fst a - 1"
    then show ?thesis 
    proof (cases "snd a < i - 1")
      case True
      from hyp3 have tmp:"0 \<le> fst a \<and> fst a \<le> snd a \<and> inv2 (snd a + 2) ins" by (subst (asm) inv_def, subst (asm) prod.collapse[symmetric], subst (asm) inv2.simps)

      hence tmp2:"inv2 (snd a + 2) ins" by simp

      with hyp3 have tmp3:"inv ins" using prod.collapse[symmetric, of a] inv2_monotone[of "snd a + 2" ins 0] by simp

      with hyp1 hyp2 have tmp4:"inv (add (i, j) ins)" by simp

      from tmp3 have "inv (add (i, j) (a # ins)) = inv (a # add (i,j) ins)" using True c1 by simp
      also have "\<dots> = inv2 (snd a + 2) (add (i,j) ins)" using tmp prod.collapse[symmetric , of a] by (metis inv_def inv2.simps(2))
      also have "\<dots> = inv (add (i,j) ins)" sorry
      show ?thesis 
    next
      case False
      then show ?thesis 
    qed

  qed
qed

lemma "inv2 a ins \<Longrightarrow> i \<le> j \<Longrightarrow> a \<le> i  \<Longrightarrow> inv2 a (add (i,j) ins)" 
proof (induction ins arbitrary : a i j)
  case Nil
  then show ?case by simp
next
  case (Cons aa ins)
  assume hyp1:"\<And>a i j. inv2 a ins \<Longrightarrow> i \<le> j \<Longrightarrow> a \<le> i  \<Longrightarrow> inv2 a (add (i, j) ins)"
  and hyp2:"inv2 a (aa # ins)"
  and hyp3:"i \<le> j"
  and hyp4:"a \<le> i"

  let ?faa = "fst aa"
  and ?saa = "snd aa"


  show ?case 
  proof (cases "j < snd aa - 1")
    case True
    from 
    then show ?thesis using hyp3 hyp2 hyp4 inv2_monotone by ()
  next
    case False
    then show ?thesis sorry
qed

  
qed
