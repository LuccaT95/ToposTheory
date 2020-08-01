theory Category imports FreeLogic

abbrevs "modphism" = ":\<rightarrow>" and
        "wedge" = "\<leftarrow>-()-\<rightarrow>"

begin

 (*Begin: some useful parameter settings*)
declare [[ smt_solver = cvc4, smt_oracle = true, smt_timeout = 120]] declare [[ show_types ]] 
sledgehammer_params [provers = cvc4 z3 spass e vampire remote_leo3]
nitpick_params [user_axioms, show_all, format = 2]
(*nitpick_params[user_axioms, show_all, format = 2, expect = genuine]*)
 (*End: some useful parameter settings*)

section \<open>The basis of category theory\<close>

class category =     
  fixes domain:: "'a \<Rightarrow> 'a" ("dom _" [108] 109) and
        codomain:: "'a\<Rightarrow> 'a" ("cod _" [110] 111) and
        composition:: "'a \<Rightarrow> 'a  \<Rightarrow> 'a" (infix "\<cdot>" 110)
        
  assumes   
        S1: "E(dom x) \<^bold>\<rightarrow> E x" and         
        S2: "E(cod y) \<^bold>\<rightarrow> E y" and
        S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
        S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and    
        S5: "x\<cdot>(dom x) \<cong> x" and           
        S6: "(cod y)\<cdot>y \<cong> y"
begin

definition arrow ("(_):(_)\<rightarrow>(_)" [120,120,120] 119) where
  "x:a\<rightarrow>b \<equiv> dom x \<simeq> a \<and> cod x \<simeq> b"

definition wedge ("_\<leftarrow>_- (_) -_\<rightarrow>_" [120,0,0,0,120] 119) where
  "a \<leftarrow>f- (x) -g\<rightarrow> b \<equiv> dom f \<simeq> x \<and> cod f \<simeq> a \<and> dom g \<simeq> x \<and> cod g \<simeq> b"

definition monic::"'a \<Rightarrow> bool" where
  "monic m \<equiv> \<forall>f g. m\<cdot>f \<simeq> m\<cdot>g \<longrightarrow> f \<simeq> g"

definition epi::"'a \<Rightarrow> bool" where
  "epi m \<equiv> \<forall>f g. f\<cdot>m \<simeq> g\<cdot>m \<longrightarrow> f \<simeq> g"

definition isomorphism::"'a \<Rightarrow> bool" where
  "isomorphism f \<equiv> \<exists>g. f\<cdot>g \<cong> (dom g) \<and> g\<cdot>f \<cong> (dom f)"

definition isomorphic::"'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "isomorphic z y \<equiv> \<exists>f. dom f \<cong> z \<and> cod f \<cong> y \<and> isomorphism f"

definition initial::"'a \<Rightarrow> bool" where
  "initial z \<equiv> \<^bold>\<forall>t. (\<exists>!f. dom f \<simeq> z \<and> cod f \<simeq> t)"

definition final::"'a \<Rightarrow> bool" where
  "final z \<equiv> \<^bold>\<forall>t. (\<exists>!f. dom f \<simeq> t \<and> cod f \<simeq> z)"

  
\<comment>\<open>Checking equivalences of definitions\<close>
lemma StrongerInitial1: "(initial z) \<longrightarrow>  (\<^bold>\<forall>t. (\<^bold>\<exists>!f. dom f \<simeq> z \<and> cod f \<simeq> t))" 
  by (metis (no_types) S1 initial_def)

lemma StrongerInitial2: "(\<^bold>\<forall>t. (\<^bold>\<exists>!f. dom f \<simeq> z \<and> cod f \<simeq> t)) \<longrightarrow> initial z"
  by (smt S2 initial_def)


lemma WeakerInitial1: "(\<^bold>\<forall>t. (\<exists>!f. dom f \<cong> z \<and> cod f \<cong> t)) \<longrightarrow> initial z"
  by (smt S5 category.S2 category.S3 category_axioms initial_def)
lemma WeakerInitial2: "initial z \<longrightarrow> (\<^bold>\<forall>t. (\<exists>!f. dom f \<cong> z \<and> cod f \<cong> t))"
  by (smt initial_def)
(*The same as above would do for final*)

end

lemma (in category) InitialsAreIsomorphic: "initial z \<and> initial y \<longrightarrow> isomorphic z y" (*sledgehammer sledgehammer [remote_leo3]*)
  by (smt S1 S3 S5 S6 category_axioms epi_def initial_def isomorphic_def isomorphism_def)

lemma (in category) InitialIsUnique: "\<forall>z. \<forall>f. initial z \<and> (dom f \<cong> z \<and> cod f \<cong> z) \<longrightarrow> z \<cong> f" (*sledgehammer sledgehammer [remote_leo3]*)
  by (metis(no_types) S3 S5 S6 initial_def)

lemma (in category) FinalsAreIsomorphic: "final z \<and> final y \<longrightarrow> isomorphic z y" (*sledgehammer sledgehammer [remote_leo3]*)
  by (smt S2 S3 S5 final_def isomorphic_def isomorphism_def)

lemma (in category) FinalIsUnique: "\<forall>z. \<forall>f. final z \<and> ( dom f \<cong> z \<and> cod f \<cong> z) \<longrightarrow> z \<cong> f" (*sledgehammer sledgehammer [remote_leo3]*)
  by (metis(no_types) S3 S5 S6 final_def)

lemma (in category) TwoMonicsBetweenTypes: "(\<^bold>\<forall>(m::'a) (n::'a). monic m \<and> monic n \<and> dom m \<simeq> dom n \<and> cod m \<simeq> cod n \<longrightarrow> (m\<simeq>n))" nitpick oops 

(*Relationship between isomorphisms and epic and monic maps*)
proposition (in category) "isomorphism m \<longrightarrow> monic m \<and> epi m"  \<comment>\<open>cvc4 and Leo-III proves this\<close>
  (*sledgehammer sledgehammer [remote_leo3]*)
  by (smt S1 S3 S4 S5 S6 epi_def isomorphism_def monic_def) 

proposition (in category) "monic m \<and> epi m \<longrightarrow> isomorphism m" nitpick oops


section \<open>Product\<close>

definition (in category) product::"'a \<Rightarrow> 'a \<Rightarrow> 'a  \<Rightarrow> bool" where
"product a b c \<equiv> \<^bold>\<exists>p1 p2. p1:c\<rightarrow>a \<and> p2:c\<rightarrow>b \<and>
                  (\<^bold>\<forall>x f g. (a\<leftarrow>f-(x)-g\<rightarrow>b) \<longrightarrow> (\<^bold>\<exists>!h. h:x\<rightarrow>c \<and> f \<simeq> p1\<cdot>h \<and> g \<simeq> p2\<cdot>h))"

lemma (in category) "((product a b c) \<and> (product a b d)) \<longrightarrow> isomorphic c d"   
  unfolding isomorphic_def  isomorphism_def  product_def arrow_def wedge_def 
  (* sledgehammer sledgehammer [remote_leo3] *)
  by (smt S3 S4 S5)

lemma (in category) "(product b a c) \<longrightarrow> (product a b c)"   
  unfolding product_def arrow_def wedge_def 
   (* sledgehammer sledgehammer [remote_leo3] *)  
  by smt 


end