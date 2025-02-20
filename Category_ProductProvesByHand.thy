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

definition object where "object x \<equiv> dom x \<simeq> x"

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
  by (metis (no_types) S1 initial_def ExId_def)

lemma StrongerInitial2: "(\<^bold>\<forall>t. (\<^bold>\<exists>!f. dom f \<simeq> z \<and> cod f \<simeq> t)) \<longrightarrow> initial z"
  by (smt S2 initial_def ExId_def)


lemma WeakerInitial1: "(\<^bold>\<forall>t. (\<exists>!f. dom f \<cong> z \<and> cod f \<cong> t)) \<longrightarrow> initial z"
  by (smt S5 category.S2 category.S3 category_axioms initial_def KlEq_def ExId_def)
lemma WeakerInitial2: "initial z \<longrightarrow> (\<^bold>\<forall>t. (\<exists>!f. dom f \<cong> z \<and> cod f \<cong> t))"
  by (smt initial_def KlEq_def ExId_def)
(*The same as above would do for final*)

end

lemma (in category) InitialsAreIsomorphic: "initial z \<and> initial y \<longrightarrow> isomorphic z y"
  by (metis ExId_def KlEq_def local.S1 local.S3 local.S5 local.S6 local.initial_def local.isomorphic_def local.isomorphism_def)

lemma (in category) InitialIsUnique: "\<forall>z. \<forall>f. initial z \<and> (dom f \<cong> z \<and> cod f \<cong> z) \<longrightarrow> z \<cong> f"
  by (metis ExId_def KlEq_def initial_def local.S2 local.S3 local.S6)


lemma (in category) FinalsAreIsomorphic: "final z \<and> final y \<longrightarrow> isomorphic z y"
  unfolding final_def isomorphic_def isomorphism_def
  apply(auto)
  by (metis ExId_def KlEq_def local.S2 local.S3 local.S5)

lemma (in category) FinalIsUnique: "\<forall>z. \<forall>f. final z \<and> ( dom f \<cong> z \<and> cod f \<cong> z) \<longrightarrow> z \<cong> f" unfolding final_def
  apply(auto)
  by (metis ExId_def KlEq_def local.S2 local.S3 local.S5)

lemma (in category) TwoMonicsBetweenTypes: "(\<^bold>\<forall>(m::'a) (n::'a). monic m \<and> monic n \<and> dom m \<simeq> dom n \<and> cod m \<simeq> cod n \<longrightarrow> (m\<simeq>n))" nitpick oops

(*Relationship between isomorphisms and epic and monic maps*)
proposition (in category) "isomorphism m \<longrightarrow> monic m \<and> epi m" \<comment>\<open>cvc4 proves this\<close>
  by (smt ExId_def KlEq_def epi_def isomorphism_def local.S2 local.S3 local.S4 local.S5 local.S6 monic_def)

proposition (in category) "monic m \<and> epi m \<longrightarrow> isomorphism m" nitpick oops


section \<open>Product\<close>

definition (in category) product::"'a \<Rightarrow> 'a \<Rightarrow> 'a  \<Rightarrow> bool" where
"product a b c \<equiv> \<^bold>\<exists>p1 p2. p1:c\<rightarrow>a \<and> p2:c\<rightarrow>b \<and>
                  (\<^bold>\<forall>x f g. (a\<leftarrow>f-(x)-g\<rightarrow>b) \<longrightarrow> (\<^bold>\<exists>!h. h:x\<rightarrow>c \<and> f \<simeq> p1\<cdot>h \<and> g \<simeq> p2\<cdot>h))"

lemma (in category) "((product a b c) \<and> (product a b d)) \<longrightarrow> isomorphic c d" for a::"'a" and b::"'a" and c::'a and d::"'a"                 
  unfolding isomorphic_def  isomorphism_def product_def arrow_def wedge_def ExId_def KlEq_def
  by (smt S3 S4 S5)

lemma (in category) "isomorphic c d" if 1: "product a b c" and 2: "product a b d" for a::"'a" and b::"'a" and c::'a and d::"'a"
proof -
  from 1 obtain p1 p2 where "E p1" and "E p2" and 
    projMap1: "dom p1 \<simeq> c \<and> cod p1 \<simeq> a \<and> dom p2 \<simeq> c \<and> cod p2 \<simeq> b" and
    uniqueMap1: "\<^bold>\<forall>x f g. ((dom f \<simeq> x \<and> cod f \<simeq> a \<and> dom g \<simeq> x \<and> cod g \<simeq> b) \<longrightarrow> 
                   (\<^bold>\<exists>!h. dom h \<simeq> x \<and> cod h \<simeq> c \<and> f \<simeq> p1\<cdot>h \<and> g \<simeq> p2\<cdot>h))" unfolding product_def arrow_def wedge_def ExId_def KlEq_def by auto

  from 2 obtain i j where "E i" and "E j" and 
    projMap2: "dom i \<simeq> d \<and> cod i \<simeq> a \<and> dom j \<simeq> d \<and> cod j \<simeq> b" and
    uniqueMap2: "(\<^bold>\<forall>x f g. (dom f \<simeq> x \<and> cod f \<simeq> a \<and> dom g \<simeq> x \<and> cod g \<simeq> b) \<longrightarrow> 
                  (\<^bold>\<exists>!h. dom h \<simeq> x \<and> cod h \<simeq> d \<and> f \<simeq> i\<cdot>h \<and> g \<simeq> j\<cdot>h))" unfolding product_def arrow_def wedge_def ExId_def KlEq_def by auto

  let ?universalMap1 = "\<lambda>h::'a. dom h \<simeq> d \<and> cod h \<simeq> c \<and> i \<simeq> p1\<cdot>h \<and> j \<simeq> p2\<cdot>h"

  from uniqueMap1 projMap2 have mapDC: "(\<^bold>\<exists>!h. ?universalMap1 h)" unfolding ExId_def KlEq_def
     by (smt S1) (*also: by (simp add: S1) works but takes longer*)
  then obtain h where uniMap_h: "?universalMap1 h" and h_unique: "(\<^bold>\<forall>x. ?universalMap1 x \<longrightarrow> x = h)" by fast

  let ?universalMap2 = "\<lambda>h. dom h \<simeq> c \<and> cod h \<simeq> d \<and> p1 \<simeq> i\<cdot>h \<and> p2 \<simeq> j\<cdot>h"

  from uniqueMap2 projMap1 have mapCD: "\<^bold>\<exists>!h. ?universalMap2 h" unfolding ExId_def KlEq_def
    by (smt S1) (*also: by (simp add: S1) works but takes longer*)
  then obtain g where uniMap_g: "?universalMap2 g" and g_unique: "(\<^bold>\<forall>x. ?universalMap2 x \<longrightarrow> x = g)" by fast

  have "p1 \<simeq> p1 \<cdot> (h \<cdot> g)" and "i \<simeq> i\<cdot>(g\<cdot>h)"
    apply (metis ExId_def KlEq_def S4 uniMap_g uniMap_h)
    by (metis ExId_def KlEq_def S4 uniMap_g uniMap_h)

  have "p2 \<simeq> p2 \<cdot> (h \<cdot> g)" and "j \<simeq> j \<cdot> (g \<cdot> h)"
    apply (metis ExId_def KlEq_def S4 uniMap_g uniMap_h)
    by (metis ExId_def KlEq_def S4 uniMap_g uniMap_h)

  hence "dom (h \<cdot> g) \<simeq> c" and "dom (g \<cdot> h) \<simeq> d" 
    apply (metis ExId_def KlEq_def S3 S4 uniMap_g uniMap_h)
    by (metis ExId_def KlEq_def S3 S4 uniMap_g uniMap_h)
 
  from uniqueMap1 have "\<^bold>\<exists>!h. dom h \<simeq> c \<and> cod h \<simeq> c \<and> p1 \<simeq> p1\<cdot>h \<and> p2 \<simeq> p2\<cdot>h" 
    by (smt ExId_def \<open>E (p1::'a)\<close> \<open>E (p2::'a)\<close> projMap1)

  hence id_hg: "h\<cdot>g \<simeq> c"
    by (metis ExId_def KlEq_def S3 S5 S6 \<open>dom h \<cdot> g \<simeq> c\<close> \<open>p1 \<simeq> p1 \<cdot> (h \<cdot> g)\<close> \<open>p2 \<simeq> p2 \<cdot> (h \<cdot> g)\<close>)

  from uniqueMap2 have "\<^bold>\<exists>!h. dom h \<simeq> d \<and> cod h \<simeq> d \<and> i \<simeq> i\<cdot>h \<and> j \<simeq> j\<cdot>h"
    by (smt ExId_def \<open>E (i::'a)\<close> \<open>E (j::'a)\<close> projMap2)
  hence id_gh: "g\<cdot>h \<simeq> d"
    by (metis ExId_def KlEq_def S3 S5 S6 \<open>dom g \<cdot> h \<simeq> d\<close> \<open>i \<simeq> i \<cdot> (g \<cdot> h)\<close> \<open>j \<simeq> j \<cdot> (g \<cdot> h)\<close>)

  show ?thesis unfolding isomorphism_def isomorphic_def KlEq_def ExId_def
    using uniMap_g id_gh id_hg uniMap_h unfolding isomorphism_def isomorphic_def KlEq_def ExId_def
      by blast
  qed                    

(*Even when defining all definitions used as abbreviations sledgehammer doesn't find a proof*)
lemma (in category) "product a b c \<longrightarrow> product b a c" unfolding product_def arrow_def wedge_def ExId_def KlEq_def
  by smt 
  
lemma (in category) "product b a c" if "product a b c"
proof -
  from that obtain \<pi>\<^sub>1 \<pi>\<^sub>2 where 1: "E \<pi>\<^sub>1" and 2: "E \<pi>\<^sub>2" and 3: "\<pi>\<^sub>1:c\<rightarrow>a" and 4: "\<pi>\<^sub>2:c\<rightarrow>b" 
                              and "\<^bold>\<forall>x f g. (a\<leftarrow>f-(x)-g\<rightarrow>b) \<longrightarrow> (\<^bold>\<exists>!h. h:x\<rightarrow>c \<and> f \<simeq> \<pi>\<^sub>1\<cdot>h \<and> g \<simeq> \<pi>\<^sub>2\<cdot>h)" unfolding product_def by blast

  then have "\<^bold>\<forall>x f g. (b\<leftarrow>f-(x)-g\<rightarrow>a) \<longrightarrow> (\<^bold>\<exists>!h. h:x\<rightarrow>c \<and> f \<simeq> \<pi>\<^sub>2\<cdot>h \<and> g \<simeq> \<pi>\<^sub>1\<cdot>h)" unfolding wedge_def arrow_def
    by smt

  thus ?thesis unfolding product_def using 1 2 3 4 by blast                        
qed


end