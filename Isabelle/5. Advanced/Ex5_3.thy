theory Ex5_3
  imports Main
begin 


datatype ('a , 'v) trie = Trie "'v option" "('a \<times> ('a  , 'v) trie) list"


primrec "value" :: "('a , 'v) trie \<Rightarrow> 'v option" where 
"value (Trie ov al) = ov"

primrec alist ::  "('a , 'v)trie \<Rightarrow> ('a \<times> ('a , 'v)trie) list" where
"alist (Trie v ls) = ls"

primrec assoc :: "('key \<times> 'val)list \<Rightarrow> 'key \<Rightarrow> 'val option" where
"assoc [] x = None"|
"assoc (x#xs) key = (if key=  fst x then Some (snd x) else assoc xs key)"

primrec lookup :: "('a , 'v)trie \<Rightarrow> 'a list \<Rightarrow> 'v option" where 
"lookup t [] = value t"|
"lookup t (x#xs) = (case assoc (alist t) x of
  None \<Rightarrow> None | 
  Some newT \<Rightarrow> lookup newT xs)"

primrec update :: "('a , 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v \<Rightarrow> ('a , 'v)trie" where
"update t [] val =  Trie (Some val) (alist t)"|
"update t (x#xs) val = (case assoc (alist t) x of
  None \<Rightarrow> Trie (value t) ((x , update (Trie None []) xs val) # alist t)|
  Some v \<Rightarrow> Trie  (value t) ((x , update v xs val) # alist t))"

lemma empty_tree_lookup : "lookup (Trie None []) ls = None" by (induction ls ; simp)

theorem "\<forall> t v bs. lookup (update t as v) bs = (if as = bs then Some v else lookup t bs)" 
proof (induction as)
  case Nil
  then show ?case 
  proof - 
    {
      fix t::"('a , 'v)trie"
      fix v bs
      have "lookup (update t [] v) bs = (if [] = bs then Some v else lookup t bs)" 
      proof (cases "bs")
        case Nil
        then show ?thesis by simp
      next
        case (Cons a list)
        then show ?thesis by simp
      qed
    }
    thus ?thesis by blast
  qed
next
  case (Cons a as)
  assume hyp:"\<forall>(t::('a,'v)trie) v bs. lookup (update t as v) bs = (if as = bs then Some v else lookup t bs)"
  then show " \<forall>(t::('a,'v)trie) v bs. lookup (update t (a # as) v) bs = (if a # as = bs then Some v else lookup t bs)"
  proof -
    {
      fix t::"('a , 'v)trie"
      fix bs v
     
      have "lookup (update t (a # as) v) bs = (if a # as = bs then Some v else lookup t bs) " 
      proof (cases "bs")
        case Nil
        then show ?thesis by (cases "assoc (alist t) a" ; simp)
      next
        case (Cons aa list)
        assume c1:"bs = aa # list"
        then show ?thesis 
        proof (cases "assoc (alist t) a")
          case None
          then show ?thesis 
          proof (cases "a = aa")
            case True
            from hyp have tmp:"lookup (update (Trie None []) as v) list = (if as = list then Some v else lookup (Trie None []) list) " by simp

            have "lookup (update t (a # as) v) bs = lookup  (Trie (value t) ((a , update (Trie None []) as v) # alist t)) bs" using None by simp
            also have "\<dots> = lookup (update (Trie None []) as v) list" using c1 True None by simp
            also have "\<dots> = (if as = list then Some v else lookup (Trie None []) list)" using tmp by simp
            also have "\<dots> = (if a # as = bs then Some v else lookup (Trie None []) list)" using True c1 by simp
            also have "\<dots> = (if a # as = bs then Some v else lookup t bs)" using empty_tree_lookup c1 True None by auto
            finally show ?thesis by assumption
          next
            case False
            let ?tmp="update (Trie None []) as v"
            
            have "lookup (update t (a # as) v) bs = lookup (Trie (value t) ((a , ?tmp )  # alist t)) bs" using None by simp
            also have "\<dots> = lookup t bs" using False c1 by simp
            finally show ?thesis using c1 False by simp
          qed
        next
          case (Some aaa)
          then show ?thesis using c1 hyp by (cases "a = aa" ; simp)
        qed
      qed
    }
    then show " \<forall>(t::('a,'v)trie) v bs. lookup (update t (a # as) v) bs = (if a # as = bs then Some v else lookup t bs)"  by simp
  qed
qed

primrec modify :: "('a , 'v)trie \<Rightarrow> 'a list \<Rightarrow> 'v option \<Rightarrow> ('a , 'v)trie" where 
"modify t [] v = Trie v (alist t)"|
"modify t (x#xs) v = (let tr  = (case assoc (alist t) x of
  None \<Rightarrow>  (x ,modify (Trie None []) xs v)   |
  Some t2 \<Rightarrow>  (x , modify t2 xs v)  ) 
  in Trie (value t) (tr # alist t))"

theorem "\<forall> t v bs. lookup (modify t as v) bs = (if as = bs then v else lookup t bs)" 
proof (induction as)
case Nil
  then show ?case  using alist.simps  modify.simps(1) list.exhaust  lookup.simps  value.simps by metis
next
  case (Cons a as)
  assume hyp:"\<forall>(t::('a,'v)trie) (v::'v option) (bs::'a list). lookup (modify t as v) bs = (if as = bs then v else lookup t bs)"
  {
    fix t::"('a , 'v) trie"
    fix v bs
    have "lookup (modify t (a # as) v) bs = (if a # as = bs then v else lookup t bs)" 
    proof (cases bs)
      case Nil
      then show ?thesis by simp
    next
      case (Cons aa list)
      show ?thesis 
      proof (cases "assoc (alist t) a")
        case None
        from hyp have tmp:"lookup (modify (Trie None []) (as::'a list) v) (list :: 'a list) = (if as = list then v else lookup (Trie None []) list)" by simp
        then show ?thesis using Cons hyp None 
        proof (cases "a = aa")
          case True
          have "lookup (modify t (a # as) v) bs = lookup  (modify (Trie None []) as v) list" using None Cons True  by simp
          also have "\<dots> = (if as = list then v else lookup (Trie None []) list)" using tmp by simp
          also have "\<dots> = (if a#as = bs then v else lookup t bs)" using Cons True None empty_tree_lookup by auto
          finally show ?thesis by assumption
        next
          case False
          then show ?thesis using Cons hyp None by simp
        qed
      next
        case (Some aaa)
        then show ?thesis using hyp Cons by (cases "a = aa" ; simp)
      qed
    qed
  }
  then show "\<forall>(t::('a,'v)trie) (v::'v option) bs. lookup (modify t (a # as) v) bs = (if a # as = bs then v else lookup t bs)" by simp
qed

