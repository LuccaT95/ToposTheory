theory FreeLogic imports Main

begin 
 consts fExistence:: "'a\<Rightarrow>bool" ("E") (*Existence/definedness predicate in free logic*)

 abbreviation fForall ("\<^bold>\<forall>") (*Free universal quantification*)                  
   where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. E x \<longrightarrow> \<Phi> x"   
 abbreviation fForallBinder (binder "\<^bold>\<forall>" [8] 9) (*Binder notation*)
   where "\<^bold>\<forall>x. \<phi> x \<equiv> \<^bold>\<forall>\<phi>"
  
 abbreviation fExists ("\<^bold>\<exists>")                                       
   where "\<^bold>\<exists>\<Phi> \<equiv> \<not>(\<^bold>\<forall>(\<lambda>y. \<not>(\<Phi> y)))"
 abbreviation fExistsBinder (binder "\<^bold>\<exists>" [8]9)                     
   where "\<^bold>\<exists>x. \<phi> x \<equiv> \<^bold>\<exists>\<phi>"
 abbreviation fExistsUnique ("\<^bold>\<exists>!")
  where "\<^bold>\<exists>!\<phi> \<equiv> \<^bold>\<exists>x. (\<phi> x \<and> (\<^bold>\<forall>y. \<phi> y \<longrightarrow> y = x))"
 abbreviation fExistsUniqueBinder (binder "\<^bold>\<exists>!" [8]9)
  where "\<^bold>\<exists>!x. \<phi> x \<equiv> \<^bold>\<exists>!\<phi>"

abbreviation KlEq (infixr "\<cong>" 56) (* Kleene equality *) 
   where "x \<cong> y \<equiv> (E x \<or> E y) \<longrightarrow> x = y"  
abbreviation ExId (infixr "\<simeq>" 56) (* Existing identity *)   
   where "x \<simeq> y \<equiv> E x \<and> E y \<and> x = y"

lemma fallI [intro]: "\<^bold>\<forall>x. \<phi> x" if "\<And>x. E x \<longrightarrow> \<phi> x" using that by simp
lemma fexI [intro]: "E x \<and> \<phi> x \<Longrightarrow> \<^bold>\<exists>x::'a. \<phi> x" by auto
lemma fexE [elim]: "(\<And>x. (E x \<and> \<phi> x) \<Longrightarrow> C) \<Longrightarrow> C" if "\<^bold>\<exists>x. \<phi> x" using that by auto

lemma fall3I: "(\<And>x y z. E x \<and> E y \<and> E z \<Longrightarrow> \<phi> x y z) \<Longrightarrow> (\<^bold>\<forall>x y z. \<phi> x y z)" for \<phi>::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  by simp

lemma equE: assumes "A \<Longrightarrow> B" and "B \<Longrightarrow> A" shows "A \<longleftrightarrow> B"
  using assms(1) assms(2) by blast
lemma contraposition: assumes "\<not>B \<longrightarrow> \<not>A" shows "A \<longrightarrow> B" 
  using assms by blast


end


