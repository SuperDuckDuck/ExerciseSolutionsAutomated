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


lemma helper:"inv2 a ins \<Longrightarrow> i \<le> j \<Longrightarrow> a \<le> i  \<Longrightarrow> inv2 a (add (i,j) ins)" 
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
  proof (cases "j < fst aa - 1")
    case True
    hence tmp:"j + 2 \<le> fst aa" by simp
    have "inv2 a (add (i, j) (aa # ins)) = inv2 a ((i,j) # aa # ins)" using True inv2.simps hyp3 prod.collapse[of aa , symmetric]  add.simps(2) prod.sel(2)[of i j] by simp
    also have "\<dots>  = inv2 (j + 2) (aa # ins)" using hyp3 hyp4 by simp
    also have "\<dots> = inv2 a (aa # ins)" using hyp2 tmp inv2.simps(2) prod.collapse[of aa , symmetric]  hyp4 by metis
    finally show ?thesis using hyp2 by simp
  next
    case False
    assume c1:"\<not> j < fst aa - 1"
    then show ?thesis 
    proof (cases "snd aa < i- 1")
      case True
      from hyp2 have "inv2 (snd aa + 2) ins" using inv2.simps(2) prod.collapse[of aa, symmetric] by metis
      with hyp1[of "snd aa + 2" i j] hyp3 True have tmp:"inv2 (snd aa + 2) (add (i, j) ins)" by simp
      have "inv2 a (add (i, j) (aa # ins)) = inv2 a (aa # add (i,j) ins)" using False True prod.collapse[of aa , symmetric] prod.sel add.simps(2) by simp
      also have "\<dots> = inv2 (snd aa + 2) (add (i,j) ins)" using hyp2 inv2.simps(2) prod.collapse[of aa , symmetric]  by metis
      finally show ?thesis using tmp by simp
    next
      case False

      have tmp:"min i (fst aa) \<le> max j (snd aa)" using hyp3 hyp2 by auto

      have tmp2:"a \<le> min i (fst aa)" using hyp2 hyp4 min_def prod.collapse[of aa , symmetric] le_trans inv2.simps by metis

      have "a \<le> snd aa + 2" using hyp2 prod.collapse[symmetric , of aa]  inv2.simps(2) le_trans trans_le_add1 by metis

      hence "inv2 a ins"  using hyp2 inv2_monotone inv2.simps(2) prod.collapse[of aa, symmetric] by metis

      hence tmp3:"inv2 a (add (min i (fst aa), max j (snd aa)) ins)" using hyp1[of a "min i (fst aa)" "max j (snd aa)"] tmp tmp2 by simp

      have "inv2 a (add (i, j) (aa # ins)) = inv2 a (add (min  i (fst aa), max j (snd aa)) ins)" 
        by (subst add.simps , subst prod.sel(2), subst c1, subst if_False, subst prod.sel(1), subst False , subst if_False, simp)
      then show ?thesis using tmp3 by simp
    qed
  qed
qed



theorem inv_add : "\<lbrakk> i \<le> j ; inv ins \<rbrakk> \<Longrightarrow> inv (add (i,j) ins)" using helper[of 0 ins i j] by simp


lemma helper2:"set_of (xs @ ys) = set_of xs \<union> set_of ys"  by (induction xs ;auto)

theorem set_of_add: 
  "\<lbrakk> i \<le> j; inv ins \<rbrakk> \<Longrightarrow> set_of (add (i,j) ins) = set_of [(i,j)] \<union> set_of ins"
proof (induction ins)
  case Nil
  then show ?case by simp
next
  case (Cons aa ins)
  then show ?case 
  proof (cases "j < fst aa - 1")
    case True
    then show ?thesis 
  next
    case False
    then show ?thesis sorry
qed

qed
