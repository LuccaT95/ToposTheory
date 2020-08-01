theory Category imports FreeLogic

abbrevs "morphism" = ":\<rightarrow>" and
        "wedge" = "\<leftarrow>-()-\<rightarrow>" and
        "ptimes" = "\<^bold>\<times>"

begin

 (*Begin: some useful parameter settings*)
declare [[ smt_solver = cvc4, smt_oracle = true, smt_timeout = 120]] declare [[ show_types ]] 
sledgehammer_params [provers = cvc4 z3 spass e vampire]
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

context category
begin

subsection\<open>Basic definitions\<close>

definition type where "type x \<equiv> x \<cong> dom x"

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

subsection\<open>Initial and Final Types | Mono and Epi Maps\<close>

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
proposition (in category) "isomorphism m \<longrightarrow> monic m \<and> epi m"  \<comment>\<open>cvc4 and Leo-III prove this\<close>
  (*sledgehammer sledgehammer [remote_leo3]*)
  by (smt S1 S3 S4 S5 S6 epi_def isomorphism_def monic_def) 

proposition (in category) "monic m \<and> epi m \<longrightarrow> isomorphism m" nitpick oops


subsection \<open>Products\<close>

definition (in category) product::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"product a b c p1 p2 \<equiv> p1:c\<rightarrow>a \<and> p2:c\<rightarrow>b \<and>
                  (\<^bold>\<forall>x f g. (a\<leftarrow>f-(x)-g\<rightarrow>b) \<longrightarrow> (\<^bold>\<exists>!h. h:x\<rightarrow>c \<and> f \<simeq> p1\<cdot>h \<and> g \<simeq> p2\<cdot>h))"

lemma (in category) prodIso: "(\<^bold>\<exists>p1 p2. (product a b c p1 p2) \<and> (\<^bold>\<exists>p1 p2. product a b d p1 p2)) \<longrightarrow> isomorphic c d"   
  unfolding isomorphic_def isomorphism_def  product_def arrow_def wedge_def 
  (* sledgehammer sledgehammer [remote_leo3] *)
  by (smt S3 S4 S5)

lemma (in category) sym_prod: "(\<^bold>\<exists>p1 p2. product b a c p1 p2) \<longrightarrow> (\<^bold>\<exists>p1 p2. product a b c p1 p2)"   
  unfolding product_def arrow_def wedge_def 
   (* sledgehammer sledgehammer [remote_leo3] *)  
  by smt 

\<comment> \<open>Solved the exercise but writing down proof will take time.\<close>
(*lemma (in category) "((product a b u) \<and> (product u c v) \<and> (product a s t) \<and> (product b c s)) \<longrightarrow> isomorphic v t" using prodIso
  unfolding isomorphic_def isomorphism_def  product_def arrow_def wedge_def sorry*)

lemma (in category) zero_prod: "\<^bold>\<forall>x a. initial (x) \<longrightarrow> (\<^bold>\<exists>p1 p2. product x a x p1 p2)" 
  unfolding initial_def product_def arrow_def wedge_def
  by (smt local.S3 local.S5 local.S6)

lemma (in category) unit_prod: "\<^bold>\<forall>u a. final (u) \<longrightarrow> (\<^bold>\<exists>p1 p2. product u a a p1 p2)"
  unfolding final_def product_def arrow_def wedge_def
  by (smt local.S3 local.S5 local.S6)


section \<open>Functor\<close>

definition isFunctor::"('c::category \<Rightarrow> 'd::category) \<Rightarrow> bool" where
  "isFunctor F \<equiv> (\<forall>x. E x \<longleftrightarrow> E (F x)) \<and>
                  (\<forall>x. type x \<longrightarrow> type (F x)) \<and> 
                   (\<forall>x. F (dom x) \<cong> dom (F x)) \<and>                    
                  (\<^bold>\<forall>x y. E(x\<cdot>y) \<longrightarrow> (F (x\<cdot>y) \<cong> (F x) \<cdot> (F y)))"


lemma isFunc_codOnCod: "isFunctor F \<longrightarrow> (\<forall>x. F (cod x) \<cong> cod (F x))" unfolding isFunctor_def type_def 
  by (metis (full_types) S2 S3 S6)


class categoryObj = category +
  fixes  fstar1::'a ("\<^bold>*\<^sub>1") and
         fstar2::'a ("\<^bold>*\<^sub>2")
  assumes O1: "E \<^bold>*\<^sub>1" and
          O2: "\<not>(E \<^bold>*\<^sub>2)" and
          O3: "type \<^bold>*\<^sub>1" and
          O4: "type \<^bold>*\<^sub>2"


typedef (overloaded) ('c::category, 'd::categoryObj) Functor = "{F::('c \<Rightarrow>'d). isFunctor F}"
morphisms "getFunctor" "setFunctor"
proof
  show "(\<lambda>m. if E m then \<^bold>*\<^sub>1 else \<^bold>*\<^sub>2) \<in> {F::'c \<Rightarrow> 'd. isFunctor F}" unfolding isFunctor_def
    apply standard
    by (smt O1 O2 O3 S1 S3 S5 type_def)
qed
 

section \<open>Natural Transformations\<close>
(*This should be a type in order to build the functor category*)

definition isNaturalTransformation::"('c, 'd) Functor \<Rightarrow> ('c, 'd) Functor \<Rightarrow> ('c::category \<Rightarrow> 'd::categoryObj) \<Rightarrow> bool" ("natTrans")
  where "natTrans F G \<upsilon> \<equiv> \<^bold>\<forall>f::'c. (\<upsilon> (cod f))\<cdot>(getFunctor F f) \<simeq> (getFunctor G f)\<cdot>(\<upsilon> (dom f))"

\<comment> \<open>Checking the domain of \<upsilon>\<close>
lemma assumes "natTrans F G \<upsilon>" shows "\<^bold>\<forall>f. (getFunctor F) (dom f) \<simeq> dom (\<upsilon> (dom f))"
  by (smt S3 S5 assms getFunctor isFunc_codOnCod isNaturalTransformation_def mem_Collect_eq) 

\<comment> \<open>It is perhaps better to not introduce the type Functor\<close>
definition isNaturalTransformation2::"('c \<Rightarrow> 'd) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('c::category \<Rightarrow> 'd::category) \<Rightarrow> bool" ("natTrans2")
  where "natTrans2 F G \<upsilon> \<equiv> isFunctor F \<and> isFunctor G \<and> 
                              (\<^bold>\<forall>f::'c. (\<upsilon> (cod f))\<cdot>(F f) \<simeq> (G f)\<cdot>(\<upsilon> (dom f)))"

lemma assumes "natTrans2 F G \<upsilon>" shows "\<^bold>\<forall>f. (F) (dom f) \<simeq> dom (\<upsilon> (dom f))" unfolding isNaturalTransformation2_def
  by (smt S3 S5 assms isFunc_codOnCod isNaturalTransformation2_def)

(*
instantiation prod :: (category, category) category
begin

instance  sorry

end


definition productFunctor::"('c::category, 'c::category) prod \<Rightarrow> 'c::category" where
  "productFunctor \<equiv> \<lambda>(a,b). (SOME f. product (fst (a,b)) (snd (a,b)) f)"


lemma "isFunctor productFunctor" oops

*)

section \<open>Cartesian category\<close>

class categoryProduct = category +
  fixes product_func::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<^bold>\<times>" 105)
  assumes catProd1: "E (a \<^bold>\<times> b) \<longrightarrow> (E a \<and> E b)" and 
          catProd2: "\<^bold>\<forall>a b. \<^bold>\<exists>p1 p2. product a b (a \<^bold>\<times> b) p1 p2"

\<comment> \<open>e is the equalizer for f and g.\<close>
definition (in category) isEqualizer::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "isEqualizer f g e \<equiv> f \<cdot> e \<simeq> g \<cdot> e \<and>
          (\<^bold>\<forall>z. f \<cdot> z \<simeq> g \<cdot> z \<longrightarrow> (\<^bold>\<exists>!u. u:(dom z)\<rightarrow>(dom g) \<and> e \<cdot> u \<simeq> z))"

class cartesianCategory = categoryProduct +
  fixes finalObject::"'a" ("\<^bold>1")

assumes
        cartesian1: "\<forall>f g. (f:(dom g)\<rightarrow>(cod g)) \<longrightarrow> (\<exists>e. isEqualizer f g e)" and
        cartesian2: "final \<^bold>1"
begin

lemma "True" nitpick[satisfy] oops

lemma "isomorphic (\<^bold>1 \<^bold>\<times> A) A"
  by (metis local.S1 local.S2 local.S3 catProd1 catProd2 local.cartesian2 local.final_def local.isomorphic_def local.isomorphism_def local.prodIso local.unit_prod)

lemma "\<forall> f g e. isEqualizer f g e \<longrightarrow> E e" unfolding isEqualizer_def
  using local.S2 local.S3 by blast

end
end











