theory Ex4_1
  imports Main 
begin 
  
lemma helper1[simp] : "op = a b = ((a \<longrightarrow> b) \<and> (b \<longrightarrow> a))" by blast
    
lemma helper2[simp] : "op \<or> a b = ((a \<longrightarrow> False) \<longrightarrow> b)" by blast
    
lemma helper3[simp] : "(\<not>a) = (a \<longrightarrow> False)" by blast
    
lemma "(A \<or> (B \<and> C) = A) = ((A \<longrightarrow> False) \<longrightarrow> (B \<and> C \<longrightarrow> A) \<and> (A \<longrightarrow> B \<and> C))" by blast