theory sledgeDuality imports sledgeCategory

begin

 (*Begin: some useful parameter settings*)
declare [[ smt_solver = cvc4, smt_oracle = true, smt_timeout = 180]] declare [[ show_types ]] 
sledgehammer_params [provers = cvc4 z3 spass e vampire remote_leo3]
nitpick_params [user_axioms, show_all, format = 2]
(*nitpick_params[user_axioms, show_all, format = 2, expect = genuine]*)
 (*End: some useful parameter settings*)

text\<open>Theory about the dual of a category. Can we prove something about the final/initial?\<close>

class categoryOp = 
  fixes domainOp:: "'a \<Rightarrow> 'a" ("domOp _" [108] 109) and
        codomainOp:: "'a\<Rightarrow> 'a" ("codOp _" [110] 111) and
        compositionOp:: "'a \<Rightarrow> 'a  \<Rightarrow> 'a" (infix "\<cdot>\<^sub>o\<^sub>p" 110)
        
  assumes   
        opS1: "E(domOp x) \<^bold>\<rightarrow> E x" and         
        opS2: "E(codOp y) \<^bold>\<rightarrow> E y" and
        opS3: "E(x\<cdot>\<^sub>o\<^sub>py) \<^bold>\<leftrightarrow> domOp x \<simeq> codOp y" and
        opS4: "x\<cdot>\<^sub>o\<^sub>p(y\<cdot>\<^sub>o\<^sub>pz) \<cong> (x\<cdot>\<^sub>o\<^sub>py)\<cdot>\<^sub>o\<^sub>pz" and    
        opS5: "x\<cdot>\<^sub>o\<^sub>p(domOp x) \<cong> x" and           
        opS6: "(codOp y)\<cdot>\<^sub>o\<^sub>py \<cong> y" 
begin

abbreviation typeOp where "typeOp x \<equiv> x \<cong> domOp x"

abbreviation isomorphismOp::"'a::type \<Rightarrow> bool" where
  "isomorphismOp (f::'a) \<equiv> \<exists>g::'a. (f \<cdot>\<^sub>o\<^sub>p g) \<cong> (domOp g) \<and> g\<cdot>\<^sub>o\<^sub>pf \<cong> (domOp f)"

abbreviation isomorphicOp::"'a \<Rightarrow> 'a \<Rightarrow> bool"  where
  "isomorphicOp z y \<equiv> \<exists>f::'a. domOp f \<cong> z \<and> codOp f \<cong> y \<and> isomorphismOp f"

abbreviation initialOp::"'a \<Rightarrow> bool" where
  "initialOp z \<equiv> \<^bold>\<forall>t::'a. (typeOp t) \<longrightarrow> (\<exists>!f::'a. domOp f \<simeq> z \<and> codOp f \<simeq> t)"

abbreviation finalOp::"'a \<Rightarrow> bool" where
  "finalOp z \<equiv> \<^bold>\<forall>t. (typeOp t) \<longrightarrow> (\<exists>!f. domOp f \<simeq> t \<and> codOp f \<simeq> z)"

end

sublocale category \<subseteq> categoryOp codomain domain "\<lambda>x y. y \<cdot> x" 
proof
  show "\<And>x::'a. E x \<^bold>\<leftarrow> E (cod x)" 
    using S2 by blast

  show "\<And>y::'a. E y \<^bold>\<leftarrow> E (dom y)" 
    using S1 by blast

  show "\<And>(x::'a) y::'a. E(y\<cdot>x) \<^bold>\<leftrightarrow> cod x \<simeq> dom y" 
    by (metis S3)

  show "\<And>(x::'a) (y::'a) z::'a. (z \<cdot> y) \<cdot> x \<cong> z \<cdot> (y \<cdot> x)" 
    using S4 by fastforce

  show "\<And>x::'a. (cod x) \<cdot> x \<cong> x" 
    using S6 by blast

  show "\<And>y::'a. y \<cdot> (dom y) \<cong> y"
    using S5 by blast
qed

sublocale categoryOp \<subseteq> category codomainOp domainOp "\<lambda>x y. y \<cdot>\<^sub>o\<^sub>p x"
proof
  show "\<And>x::'a. E x \<^bold>\<leftarrow> E (codOp x)" 
    using opS2 by blast

  show "\<And>y::'a. E y \<^bold>\<leftarrow> E (domOp y)" 
    using opS1 by blast

  show "\<And>(x::'a) y::'a. E(y\<cdot>\<^sub>o\<^sub>px) \<^bold>\<leftrightarrow> codOp x \<simeq> domOp y" 
    by (metis opS3)

  show "\<And>(x::'a) (y::'a) z::'a. (z \<cdot>\<^sub>o\<^sub>p y) \<cdot>\<^sub>o\<^sub>p x \<cong> z \<cdot>\<^sub>o\<^sub>p (y \<cdot>\<^sub>o\<^sub>p x)" 
    using opS4 by fastforce

  show "\<And>x::'a. (codOp x) \<cdot>\<^sub>o\<^sub>p x \<cong> x" 
    using opS6 by blast

  show "\<And>y::'a. y \<cdot>\<^sub>o\<^sub>p (domOp y) \<cong> y"
    using opS5 by blast
qed


context categoryOp begin

print_facts

end

lemma "categoryOp_class.initialOp z \<longrightarrow> categoryOp_class.final z"
  by (metis categoryOp_class.S3 categoryOp_class.S5)

lemma Hello: assumes "category_class.finalOp z" shows "category_class.initial z" 
  by (smt assms category_class.opS3 category_class.opS5 category_class.opS6)

lemma isoeq: "category_class.isomorphic z f \<longrightarrow> category_class.isomorphicOp z f" 
  by (metis category_class.opS1 category_class.opS3 category_class.opS6)

\<comment> \<open>Duality proof that final obj in op are isomorphic.\<close>
lemma assumes 1:"category_class.finalOp z" and  2:"category_class.finalOp f" shows "category_class.isomorphicOp z f"
proof -
  from 1 have 3:"category_class.initial z" by (rule Hello)
  from 2 have 4:"category_class.initial f" by (rule Hello)

  have 5:"category_class.initial z \<and> category_class.initial f" using 3 4 by simp

  have "category_class.isomorphic z f" using 5 by (simp add: category_class.InitialsAreIsomorphic)
  thus "category_class.isomorphicOp z f" by (simp add: isoeq)
qed




end