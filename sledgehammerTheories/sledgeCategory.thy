theory sledgeCategory imports FreeLogic

abbrevs "modphism" = ":\<rightarrow>" and
        "wedge" = "\<leftarrow>-()-\<rightarrow>"

begin

 (*Begin: some useful parameter settings*)
declare [[ smt_solver = cvc4, smt_oracle = true, smt_timeout = 180]] declare [[ show_types ]] 
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


context category begin

abbreviation type ("type") where "type x \<equiv> x \<cong> dom x"

abbreviation arrow ("(_):(_)\<rightarrow>(_)" [120,120,120] 119) where
  "x:a\<rightarrow>b \<equiv> dom x \<simeq> a \<and> cod x \<simeq> b"

abbreviation wedge ("_\<leftarrow>_- (_) -_\<rightarrow>_" [120,0,0,0,120] 119) where
  "a \<leftarrow>f- (x) -g\<rightarrow> b \<equiv> dom f \<simeq> x \<and> cod f \<simeq> a \<and> dom g \<simeq> x \<and> cod g \<simeq> b"

abbreviation monic::"'a \<Rightarrow> bool" ("monic") where
  "(monic m) \<equiv> \<forall>f g. m\<cdot>f \<simeq> m\<cdot>g \<longrightarrow> f \<simeq> g"

abbreviation epi::"'a \<Rightarrow> bool" ("epi") where
  "(epi m) \<equiv> \<forall>f g. f\<cdot>m \<simeq> g\<cdot>m \<longrightarrow> f \<simeq> g"

abbreviation isomorphism::"'a \<Rightarrow> bool" ("isomorphism") where
  "(isomorphism f) \<equiv> \<exists>g. f\<cdot>g \<cong> (dom g) \<and> g\<cdot>f \<cong> (dom f)"

abbreviation isomorphic::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<cong>" 120) where
  "isomorphic z y \<equiv> \<exists>f. dom f \<cong> z \<and> cod f \<cong> y \<and> isomorphism f"

abbreviation initial::"'a \<Rightarrow> bool" ("initial") where
  "(initial z) \<equiv> \<^bold>\<forall>t. (type t) \<longrightarrow> (\<exists>!f. ((dom f) \<simeq> z \<and> (cod f) \<simeq> t))"

abbreviation final::"'a \<Rightarrow> bool" ("final") where
  "(final z) \<equiv> \<^bold>\<forall>t. (type t) \<longrightarrow> (\<exists>!f. ((dom f) \<simeq> t \<and> (cod f) \<simeq> z))"

  
\<comment>\<open>Checking equivalences of abbreviations\<close>
lemma StrongerInitial1: "(initial z) \<longrightarrow>  (\<^bold>\<forall>t.(type t)\<longrightarrow> (\<^bold>\<exists>!f. dom f \<simeq> z \<and> cod f \<simeq> t))" (* sledgehammer sledgehammer [remote_leo3] *)
  by (metis S1)

lemma StrongerInitial2: "(\<^bold>\<forall>t. (type t)\<longrightarrow>(\<^bold>\<exists>!f. dom f \<simeq> z \<and> cod f \<simeq> t)) \<longrightarrow> initial z"  (*sledgehammer sledgehammer [remote_leo3]*) 
  by (metis local.S1)

lemma WeakerInitial1: "(\<^bold>\<forall>t. (type t) \<longrightarrow> (\<exists>!f. dom f \<cong> z \<and> cod f \<cong> t)) \<longrightarrow> initial z" (* sledgehammer sledgehammer [remote_leo3] *)
  by (smt S5 S2 S3 category_axioms)

lemma WeakerInitial2: "(initial z) \<longrightarrow> (\<^bold>\<forall>t. (type t) \<longrightarrow> (\<exists>!f. dom f \<cong> z \<and> cod f \<cong> t))" (* sledgehammer sledgehammer [remote_leo3] *)
  by smt
(*The same as above would do for final*)


end



lemma (in category) InitialsAreIsomorphic: "initial z \<and> initial y \<longrightarrow> z \<^bold>\<cong> y"  (*sledgehammer(S1 S2 S3 S4 S5 S6) sledgehammer [remote_leo3](S1 S2 S3 S4 S5 S6)*)
  by (smt S1 S2 S3 S4 S5 S6)

lemma (in category) InitialIsUnique: "\<forall>z. \<forall>f. initial z \<and> (dom f \<cong> z \<and> cod f \<cong> z) \<longrightarrow> z \<cong> f" (*sledgehammer(S1 S2 S3 S4 S5 S6) sledgehammer [remote_leo3](S1 S2 S3 S4 S5 S6)*)
  by (smt S3 S5 S6)

lemma (in category) FinalsAreIsomorphic: "final z \<and> final y \<longrightarrow> z \<^bold>\<cong> y" (*sledgehammer(S1 S2 S3 S4 S5 S6) sledgehammer [remote_leo3](S1 S2 S3 S4 S5 S6)*)
  by (smt S1 S2 S3 S4 S5 S6)

lemma (in category) FinalIsUnique: "\<forall>z. \<forall>f. final z \<and> ( dom f \<cong> z \<and> cod f \<cong> z) \<longrightarrow> z \<cong> f" (* sledgehammer sledgehammer [remote_leo3] *)
  by (metis S2 S3 S5 S6)

lemma (in category) TwoMonicsBetweenTypes: "(\<^bold>\<forall>(m::'a) (n::'a). monic m \<and> monic n \<and> dom m \<simeq> dom n \<and> cod m \<simeq> cod n \<longrightarrow> (m\<simeq>n))" nitpick oops 

(*Relationship between isomorphisms and epic and monic maps*)
proposition (in category) "isomorphism m \<longrightarrow> monic m \<and> epi m"  \<comment>\<open>cvc4 and Leo-III proves this\<close>
  (* sledgehammer sledgehammer [remote_leo3] *)
  by (smt S1 S3 S4 S5 S6) 

proposition (in category) "monic m \<and> epi m \<longrightarrow> isomorphism m" nitpick oops


section \<open>Product\<close>

abbreviation (in category) product::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("product") where
"product a b c p1 p2 \<equiv> dom p1 \<simeq> c \<and> cod p1 \<simeq> a \<and> dom p2 \<simeq> c \<and> cod p2 \<simeq> b \<and>
                  (\<^bold>\<forall>x f g. dom f \<simeq> x \<and> cod f \<simeq> a \<and> dom g \<simeq> x \<and> cod g \<simeq> b \<longrightarrow> (\<^bold>\<exists>!h. dom h \<simeq> x \<and> cod h \<simeq> c \<and> f \<simeq> p1\<cdot>h \<and> g \<simeq> p2\<cdot>h))"

lemma (in category) productIso: "((product a b c p1 p2) \<and> (product a b d q1 q2)) \<longrightarrow> c \<^bold>\<cong> d"   
   by (smt S1 S2 S4 S3 S5 S6)                     

lemma (in category) productAssoc: "((product b a c p1 p2) \<longrightarrow>  (product a b c p2 p1))"   
   (*sledgehammer  sledgehammer [remote_leo3]()*) 
  by smt

context categoryOp begin

abbreviation coproduct::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" 
  where "coproduct \<equiv> categoryOp.type"

end




lemma (in category) coproductIso: "((coproduct a b c p1 p2) \<and> (coproduct a b d q1 q2)) \<longrightarrow> c \<^bold>\<cong> d" sledgehammer(S1 S2 S4 S3 S5 S6)  sledgehammer [remote_leo3](S1 S2 S4 S3 S5 S6)






end