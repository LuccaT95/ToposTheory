theory internalLanguage imports sledgeCategoryV3

begin

context topos begin
lemmas axiomSetTopos = S1 S2 S3 S4 S5 S6 catProd1 catProd2 catProd3 catProd4 catProd5 catProd6 
                          cartesian1 cartesian2 cartesian3 G1 G2 G3 G4 T1 T2 T3 T4 T5
\<comment> \<open>variable of type X: dom x\<close>
\<comment> \<open>product of two maps \<sigma> and \<tau>: \<sigma>\<^bold>\<times>\<tau>\<close>

abbreviation equality::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<^bold>=" 100)
   where "\<sigma> \<^bold>= \<tau> \<equiv> (\<delta> (cod \<sigma>)) \<cdot> (\<sigma>\<^bold>\<times>\<tau>)"  

lemma "cod (\<sigma> \<^bold>= \<tau>) \<cong> \<Omega>" sledgehammer(axiomSetTopos)
 

end

end