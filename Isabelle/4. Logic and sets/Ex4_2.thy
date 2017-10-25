theory Ex4_2
  imports Main 
begin
  
  
lemma I: "A \<longrightarrow> A" 
proof (rule impI)
  assume A
  thus A by assumption
qed
  
lemma I_2 : "A \<longrightarrow> A"
proof -
  {
    assume A 
  }
  thus ?thesis by (rule impI)
qed
  
lemma "A \<and> B \<longrightarrow> B \<and> A" 
proof (rule impI)
  assume "A \<and> B"
  thus "B \<and> A"
  proof (rule conjE)
    assume A and B
    thus "B \<and> A" by (rule conjI[rotated 1])
  qed
qed
  
lemma "A \<and> B \<longrightarrow> B \<and> A"
proof - 
  {
    assume a:"A \<and> B"
    hence b:A by (rule conjE)
    from a have B by (rule conjE)
    with b have "B \<and> A" by (rule conjI[rotated 1])
  }
  thus ?thesis by (rule impI)
qed
  
lemma "(A \<and> B) \<longrightarrow> (A \<or> B)" 
proof (rule impI)
  assume "A \<and> B"
  then show "A \<or> B"
  proof (rule conjE)
    assume A 
    thus "A \<or> B" by (rule disjI1)
  qed
qed
  
lemma "(A \<and> B) \<longrightarrow> (A \<or> B)" 
proof -
  {
    assume "A \<and> B"
    hence A by (rule conjE)
    hence "A \<or> B" by (rule disjI1)
  }
  thus ?thesis by (rule impI)
qed
  
  
lemma "((A \<or> B) \<or> C) \<longrightarrow> A \<or> (B \<or> C)"
proof (rule impI)
  assume a:"(A \<or> B) \<or> C"
  show "A \<or> (B \<or> C)"
  proof (rule disjE[where ?P = "A \<or> B" and ?Q = "C"])
    show "(A \<or> B) \<or> C" by (fact a)
    show "A \<or> B \<Longrightarrow> A \<or> B \<or> C"
    proof (rule  disjE[where ?P = A and ?Q = B])
      assume "A \<or> B"
      thus "A \<or> B" by assumption
      assume "A"
      thus "A \<or> B \<or> C" by (rule disjI1)
    next
      assume b:B
      hence c:"B \<or> C" by (rule disjI1)
      thus "A \<or> B \<or> C" by (rule disjI2)
    qed
    assume C
    show "A \<or> B \<or> C"
    proof (rule disjI2)
      from \<open>C\<close> show "B \<or> C" by (rule disjI2)
    qed
  qed
qed
    
lemma "((A \<or> B) \<or> C) \<longrightarrow> A \<or> (B \<or> C)"
proof - 
  {
    assume a:"(A \<or> B) \<or> C"
    {
      assume b:"A \<or> B"
      {
        assume A
        hence "A \<or> (B \<or> C)" by (rule disjI1)
      }
      note tmp=this
      {
        assume B
        hence "B \<or> C" by (rule disjI1)
        hence "A \<or> (B \<or> C)" by (rule disjI2)
      }
        
      with b and tmp have "A \<or> (B \<or> C)" by (rule disjE)
    }
    note tmp=this
    {
      assume b:C
      hence "B \<or> C" by (rule disjI2)
      hence "A \<or> (B \<or> C)" by (rule disjI2)
    }
    with a and tmp have "A \<or> (B \<or> C)" by (rule disjE)
  }
  thus ?thesis by (rule impI)
qed
  
lemma K : "A \<longrightarrow> B \<longrightarrow> A"
proof (rule impI)
  assume A
  show "B \<longrightarrow> A"
  proof (rule impI)
    show A by (fact)
  qed
qed
  
  
lemma "A \<longrightarrow> B \<longrightarrow> A"
proof -
  {
    assume A 
    {
      assume B
      have A by fact
    }
    hence "B \<longrightarrow> A" by (rule impI)
  }
  thus "A \<longrightarrow> B \<longrightarrow> A" by (rule impI)
qed
  
lemma "(A \<or> A) = (A \<and> A)"
  using [[simp_trace_new mode=full]]
proof (rule iffI)
  assume "A \<or> A"
  then show "A \<and> A"
  proof (rule  disjE)
    assume A
    show "A \<and> A" 
    proof (rule conjI)
      show A by (rule \<open>A\<close>)
      show A by fact
    qed
    assume A 
    show "A \<and> A"
    proof (rule conjI)
      show A by fact
      show A by fact
    qed
  qed
next
  show "A \<and> A \<Longrightarrow> A \<or> A"
  proof (rule disjI1)
    show "A \<and> A \<Longrightarrow> A"
    proof (rule conjE[where ?P = A and ?Q = A])
      show "A \<and> A \<Longrightarrow> A \<and> A" by assumption
    next
      show "A \<and> A \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> A " by assumption
    qed
  qed
qed
  
lemma "(A \<or> A) = (A \<and> A)"
proof - 
  {
    assume a:"A \<or> A"
    {
      assume A 
      from this and this have "A \<and> A" by (rule conjI)
    }
    note tmp=this
    {
      assume A
      from this and this have "A \<and> A" by (rule conjI)
    }
    with a and tmp have "A \<and> A" by (rule disjE)
  }
  note tmp=this
  {
    assume "A \<and> A"
    hence A by (rule conjE)
    hence "A \<or> A" by (rule disjI1)
  }
  with tmp show ?thesis by (rule iffI)
qed
  
lemma S: "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
proof (rule impI)+
  assume a:"A \<longrightarrow> B \<longrightarrow> C"
     and b:"A \<longrightarrow> B"
     and c:A
  from b and c have B by (rule mp)
  from a and c have "B \<longrightarrow> C" by (rule mp) 
  with \<open>B\<close> show C by (rule mp[rotated 1])
qed
  
lemma "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
proof - 
  {
    assume a:"A \<longrightarrow> B \<longrightarrow> C"
    {
      assume b:"A \<longrightarrow> B"
      {
        assume A
        with b have B by (rule mp)
        from a and \<open>A\<close> have "B \<longrightarrow> C" by (rule mp) 
        with \<open>B\<close> have C by (rule mp[rotated 1])
      }
      hence "A \<longrightarrow> C" by (rule impI)
    }
    hence "(A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
  
lemma "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C"
proof (rule impI)+
  assume a:"A \<longrightarrow> B"
     and b:"B \<longrightarrow> C"
     and c:A
  from a and c have B by (rule mp)
  with b show C by (rule mp)
qed
  
lemma "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C"
proof - 
  {
    assume a:"A \<longrightarrow> B"
    {
      assume b:"B \<longrightarrow> C"
      {
        assume A 
        with a have B by (rule mp)
        with b have C by (rule mp)
      }
      hence "A \<longrightarrow> C" by (rule impI)
    }
    hence "(B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
  
lemma "\<not>\<not>A \<longrightarrow> A" 
proof (rule impI)
  assume "\<not>\<not>A"
  show A 
  proof (rule classical)
    assume "\<not>A"
    with \<open>\<not>\<not>A\<close> show A by (rule notE)
  qed
qed
  
    
lemma "\<not>\<not>A \<longrightarrow> A"
proof - 
  {
    assume a:"\<not>\<not>A"
    {
      assume "\<not>A"
      with a have A by (rule notE)
    }
    hence A by (rule classical)
  }
  thus ?thesis by (rule impI)
qed
  
lemma "A \<longrightarrow> \<not>\<not>A"
proof - 
  {
    assume a:A
    {
      assume "\<not>A"
      from this a have False by (rule notE)
    }
    hence "\<not>\<not>A" by (rule notI)
  }
  thus ?thesis by (rule impI)
qed

lemma "(\<not>A \<longrightarrow> B) \<longrightarrow> (\<not>B \<longrightarrow> A)"
proof (rule impI)+
  assume "\<not>A \<longrightarrow> B"
     and "\<not>B"
  show A 
  proof (rule FalseE)
    
lemma "(\<not>A \<longrightarrow> B) \<longrightarrow> (\<not>B \<longrightarrow> A)"
proof - 
  {
    assume a:"\<not>A \<longrightarrow> B"
    {
      assume b:"\<not>B"
      {
        assume "\<not>A"
        with a have B by (rule mp)
        with b have False ..
      }
        hence A by (rule not)
    
    
  
    
  
  
        

      