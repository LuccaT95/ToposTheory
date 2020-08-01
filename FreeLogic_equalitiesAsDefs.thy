theory FreeLogic imports Main

begin 
 consts fExistence:: "'a\<Rightarrow>bool" ("E") (*Existence/definedness predicate in free logic*)
 consts fstar::'a ("\<^bold>*")

 abbreviation fNot ("\<^bold>\<not>") (*Free negation*)                          
   where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
 abbreviation fImplies (infixr "\<^bold>\<rightarrow>" 13) (*Free implication*)        
   where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"
 abbreviation fIdentity (infixr "\<^bold>=" 13) (*Free identity*)        
   where "l \<^bold>= r \<equiv> l = r"
 abbreviation fForall ("\<^bold>\<forall>") (*Free universal quantification*)                  
   where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. E x \<longrightarrow> \<Phi> x"   
 abbreviation fForallBinder (binder "\<^bold>\<forall>" [8] 9) (*Binder notation*)
   where "\<^bold>\<forall>x. \<phi> x \<equiv> \<^bold>\<forall>\<phi>"

 abbreviation fOr (infixr "\<^bold>\<or>" 11)                                 
   where "\<phi> \<^bold>\<or> \<psi> \<equiv> (\<^bold>\<not>\<phi>) \<^bold>\<rightarrow> \<psi>" 
 abbreviation fAnd (infixr "\<^bold>\<and>" 12)                                
   where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>)"    
 abbreviation fImplied (infixr "\<^bold>\<leftarrow>" 13)       
   where "\<phi> \<^bold>\<leftarrow> \<psi> \<equiv> \<psi> \<^bold>\<rightarrow> \<phi>" 
 abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 15)                             
   where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<and> (\<psi> \<^bold>\<rightarrow> \<phi>)"  
 abbreviation fExists ("\<^bold>\<exists>")                                       
   where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y. \<^bold>\<not>(\<Phi> y)))"
 abbreviation fExistsBinder (binder "\<^bold>\<exists>" [8]9)                     
   where "\<^bold>\<exists>x. \<phi> x \<equiv> \<^bold>\<exists>\<phi>"
 abbreviation fExistsUnique ("\<^bold>\<exists>!")
  where "\<^bold>\<exists>!\<phi> \<equiv> \<^bold>\<exists>x. (\<phi> x \<and> (\<^bold>\<forall>y. \<phi> y \<longrightarrow> y = x))"
 abbreviation fExistsUniqueBinder (binder "\<^bold>\<exists>!" [8]9)
  where "\<^bold>\<exists>!x. \<phi> x \<equiv> \<^bold>\<exists>!\<phi>"

definition KlEq (infixr "\<cong>" 56) (* Kleene equality *) 
   where "x \<cong> y \<equiv> (E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<^bold>= y"  
definition ExId (infixr "\<simeq>" 56) (* Existing identity *)   
   where "x \<simeq> y \<equiv> E x \<^bold>\<and> E y \<^bold>\<and> x \<^bold>= y"

lemma fallI [intro]: "\<^bold>\<forall>x. \<phi> x" if "\<And>x. E x \<longrightarrow> \<phi> x" using that by simp
lemma fexI [intro]: "\<^bold>\<exists>x. \<phi> x" if "E x \<and> \<phi> x" using that by auto
lemma fexE [elim]: "(\<And>x. (E x \<and> \<phi> x) \<Longrightarrow> C) \<Longrightarrow> C" if "\<^bold>\<exists>x. \<phi> x" using that by auto

lemma KlEq_sym [simp]: "x \<cong> y \<Longrightarrow> y \<cong> x" unfolding KlEq_def by blast
lemma KlEq_refl [simp]: "x \<cong> x" unfolding KlEq_def by blast
lemma KlEq_trans: "x \<cong> y \<and> y \<cong> z \<Longrightarrow> x \<cong> z" unfolding KlEq_def by blast

lemma ExId_sym [simp]: "x \<simeq> y \<Longrightarrow> y \<simeq> x" unfolding ExId_def by blast
lemma ExId_trans: "x \<simeq> y \<and> y \<simeq> z \<Longrightarrow> x \<simeq> z" unfolding ExId_def by blast

lemma ExIdToKlEq: "x \<simeq> y \<Longrightarrow> x \<cong> y" unfolding KlEq_def ExId_def by blast
lemma KlEqToExId: "E x \<and> x \<cong> y \<Longrightarrow> x \<simeq> y" unfolding KlEq_def ExId_def by blast
lemma KlEqToExId2: "E y \<and> x \<cong> y \<Longrightarrow> x \<simeq> y" unfolding KlEq_def ExId_def by blast

end


