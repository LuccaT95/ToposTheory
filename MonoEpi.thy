theory MonoEpi imports FreeLogic 
begin

 (*Begin: some useful parameter settings*)
declare [[ smt_solver = cvc4, smt_oracle = true, smt_timeout = 120]] declare [[ show_types ]] 
sledgehammer_params [provers = cvc4 z3 e spass]
  nitpick_params [user_axioms, show_all, format = 2]
  (*nitpick_params[user_axioms, show_all, format = 2, expect = genuine]*)
 (*End: some useful parameter settings*)

typedecl \<alpha> \<comment>\<open>This type can be thought of representing the morphisms of a category.\<close>

locale category = 
           \<comment>\<open>We need three functions and constant to define a category.\<close>
  fixes domain:: "\<alpha> \<Rightarrow> \<alpha>" ("dom _" [108] 109) and
        codomain:: "\<alpha> \<Rightarrow> \<alpha>" ("cod _" [110] 111) and
        composition:: "\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" (infix "\<cdot>" 110) and
        star::\<alpha> ("\<^bold>*") \<comment>\<open>Symbol for non-existing elements in terms of free logic\<close>

  assumes   
\<comment>\<open>Here we define the axioms that the morphisms 
    in interaction with the functions have to obey.\<close>

\<comment>\<open>The existence of the domain of a morphism implies the existence of the morphism.\<close>
        S1: "E(dom x) \<^bold>\<rightarrow> E x" and         
        S2: "E(cod y) \<^bold>\<rightarrow> E y" and         \<comment>\<open>The same goes for the codomain.\<close>


\<comment>\<open>As we have seen, the composition only exists if the two morphisms are composable.\<close>
\<comment>\<open>We use \<simeq> to denote the existing equality which requires that both sides 
    of the equation exist.\<close>
        S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and


        S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and     \<comment>\<open>Composition of morphisms is associative.\<close>
\<comment>\<open>We use \<cong> to denote the Kleene equality which only implies equality 
    if at least one side of the equation exists\<close>


\<comment>\<open>The domain of a morphisms serves as the right identity for composition.\<close>
        S5: "x\<cdot>(dom x) \<cong> x" and           
        S6: "(cod y)\<cdot>y \<cong> y" and   \<comment>\<open>So does the codomain as a left identity.\<close>


\<comment>\<open>Finally we make sure that there is only one non-existing morphism.\<close>
        L1: "\<^bold>\<not>(E m) \<^bold>\<rightarrow> (m = \<^bold>*)"


begin
\<comment>\<open>We show consistency.\<close>
lemma "True" nitpick[satisfy] oops

definition monic::"\<alpha> \<Rightarrow> bool" where
  "monic m \<equiv> \<forall>f g. m\<cdot>f \<simeq> m\<cdot>g \<longrightarrow> f \<simeq> g"

definition epi::"\<alpha> \<Rightarrow> bool" where
  "epi m \<equiv> \<forall>f g. f\<cdot>m \<simeq> g\<cdot>m \<longrightarrow> f \<simeq> g"

definition iso::"\<alpha> \<Rightarrow> bool" where
  "iso f \<equiv> \<exists>g. f\<cdot>g \<cong> (dom g) \<and> g\<cdot>f \<cong> (dom f)"

lemma "iso f \<longrightarrow> monic f" 
  by (smt S2 S3 S4 S6 local.iso_def monic_def)

lemma "iso f \<longrightarrow> epi f"
  by (smt S2 S3 S4 S5 category.iso_def category_axioms epi_def)

lemma "\<forall>f. ((monic f) \<and> (epi f) \<longrightarrow> iso f)" nitpick[card = 4] oops

end





