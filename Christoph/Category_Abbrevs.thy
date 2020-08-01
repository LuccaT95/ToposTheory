theory Category_Abbrevs imports FreeLogic

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
begin

abbreviation type where "type x \<equiv> x \<cong> dom x"

abbreviation arrow ("(_):(_)\<rightarrow>(_)" [120,120,120] 119) where
  "x:a\<rightarrow>b \<equiv> dom x \<simeq> a \<and> cod x \<simeq> b"

abbreviation wedge ("_\<leftarrow>_- (_) -_\<rightarrow>_" [120,0,0,0,120] 119) where
  "a \<leftarrow>f- (x) -g\<rightarrow> b \<equiv> dom f \<simeq> x \<and> cod f \<simeq> a \<and> dom g \<simeq> x \<and> cod g \<simeq> b"

abbreviation monic::"'a \<Rightarrow> bool" where
  "monic m \<equiv> \<forall>f g. m\<cdot>f \<simeq> m\<cdot>g \<longrightarrow> f \<simeq> g"

abbreviation epi::"'a \<Rightarrow> bool" where
  "epi m \<equiv> \<forall>f g. f\<cdot>m \<simeq> g\<cdot>m \<longrightarrow> f \<simeq> g"

abbreviation isomorphism::"'a \<Rightarrow> bool" where
  "isomorphism f \<equiv> \<exists>g. f\<cdot>g \<cong> (dom g) \<and> g\<cdot>f \<cong> (dom f)"

abbreviation isomorphic::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<cong>" 120) where
  "isomorphic z y \<equiv> \<exists>f. dom f \<cong> z \<and> cod f \<cong> y \<and> isomorphism f"

abbreviation initial::"'a \<Rightarrow> bool" where
  "initial z \<equiv> \<^bold>\<forall>t. (\<exists>!f. dom f \<simeq> z \<and> cod f \<simeq> t)"

abbreviation final::"'a \<Rightarrow> bool" where
  "final z \<equiv> \<^bold>\<forall>t. (\<exists>!f. dom f \<simeq> t \<and> cod f \<simeq> z)"

  
\<comment>\<open>Checking equivalences of abbreviations\<close>
lemma StrongerInitial1: "(initial z) \<longrightarrow>  (\<^bold>\<forall>t. (\<^bold>\<exists>!f. dom f \<simeq> z \<and> cod f \<simeq> t))" (* sledgehammer sledgehammer [remote_leo3] *)
  by (metis S1)

lemma StrongerInitial2: "(\<^bold>\<forall>t. (\<^bold>\<exists>!f. dom f \<simeq> z \<and> cod f \<simeq> t)) \<longrightarrow> initial z"  (*sledgehammer sledgehammer [remote_leo3]*) 
  by (metis local.S1)

lemma WeakerInitial1: "(\<^bold>\<forall>t. (\<exists>!f. dom f \<cong> z \<and> cod f \<cong> t)) \<longrightarrow> initial z" (* sledgehammer sledgehammer [remote_leo3] *)
  by (smt S5 S2 S3 category_axioms)

lemma WeakerInitial2: "initial z \<longrightarrow> (\<^bold>\<forall>t. (\<exists>!f. dom f \<cong> z \<and> cod f \<cong> t))" (* sledgehammer sledgehammer [remote_leo3] *)
  by smt
(*The same as above would do for final*)

end

lemma (in category) InitialsAreIsomorphic: "initial z \<and> initial y \<longrightarrow> isomorphic z y" (* sledgehammer sledgehammer [remote_leo3] *)
  by (smt S1 S3 S5 S6)

lemma (in category) InitialIsUnique: "\<forall>z. \<forall>f. initial z \<and> (dom f \<cong> z \<and> cod f \<cong> z) \<longrightarrow> z \<cong> f" (* sledgehammer sledgehammer [remote_leo3] *)
  by (metis S3 S5 S6)

lemma (in category) FinalsAreIsomorphic: "final z \<and> final y \<longrightarrow> isomorphic z y" (* sledgehammer sledgehammer [remote_leo3] *)
  by (smt S2 S3 S5)

lemma (in category) FinalIsUnique: "\<forall>z. \<forall>f. final z \<and> ( dom f \<cong> z \<and> cod f \<cong> z) \<longrightarrow> z \<cong> f" (* sledgehammer sledgehammer [remote_leo3] *)
  by (metis S3 S5 S6)

lemma (in category) TwoMonicsBetweenTypes: "(\<^bold>\<forall>(m::'a) (n::'a). monic m \<and> monic n \<and> dom m \<simeq> dom n \<and> cod m \<simeq> cod n \<longrightarrow> (m\<simeq>n))" nitpick oops 

(*Relationship between isomorphisms and epic and monic maps*)
proposition (in category) "isomorphism m \<longrightarrow> monic m \<and> epi m"  \<comment>\<open>cvc4 and Leo-III proves this\<close>
  (* sledgehammer sledgehammer [remote_leo3] *)
  by (smt S1 S3 S4 S5 S6) 

proposition (in category) "monic m \<and> epi m \<longrightarrow> isomorphism m" nitpick oops


section \<open>Product\<close>

abbreviation (in category) product::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"product a b c p1 p2 \<equiv> p1:c\<rightarrow>a \<and> p2:c\<rightarrow>b \<and>
                  (\<^bold>\<forall>x f g. (a\<leftarrow>f-(x)-g\<rightarrow>b) \<longrightarrow> (\<^bold>\<exists>!h. h:x\<rightarrow>c \<and> f \<simeq> p1\<cdot>h \<and> g \<simeq> p2\<cdot>h))"

lemma (in category) productIso: "((product a b c p1 p2) \<and> (product a b d q1 q2)) \<longrightarrow> isomorphic c d"   
   by (smt S1 S2 S4 S3 S5 S6)                     

lemma (in category) productAssoc: "((product b a c p1 p2) \<longrightarrow>  (product a b c p2 p1))"   
   (*sledgehammer  sledgehammer [remote_leo3]()*) 
  by smt


abbreviation isFunctor::"('a::category \<Rightarrow> 'b::category) \<Rightarrow> bool" where
  "isFunctor F \<equiv> (\<forall>x. E x \<longleftrightarrow> E (F x)) \<and>
                  (\<forall>x. type x \<longrightarrow> type (F x)) \<and> 
                   (\<forall>x. F (dom x) \<cong> dom (F x)) \<and>                    
                  (\<^bold>\<forall>x y. E(x\<cdot>y) \<longrightarrow> (F (x\<cdot>y) \<cong> (F x) \<cdot> (F y)))"


class categoryProduct = category +
  fixes product_func::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<^bold>\<times>" 115)
  assumes catProd1: "E (a \<^bold>\<times> b) \<longrightarrow> (E a \<and> E b)" and 
          catProd2: "\<^bold>\<forall>a b. \<^bold>\<exists>p1 p2. product a b (a \<^bold>\<times> b) p1 p2"

abbreviation (in categoryProduct) isExponential:: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("isExp")
  where "isExp a b c \<epsilon> \<equiv> \<^bold>\<exists>p1 p2. product a c (dom \<epsilon>) p1 p2 \<and> \<epsilon>:(a\<^bold>\<times>c)\<rightarrow>b \<and>
                        (\<^bold>\<forall>z f. \<^bold>\<exists>q1 q2. product z a (dom f) q1 q2 \<and> f:(z\<^bold>\<times>a)\<rightarrow>b \<and>
                          (\<^bold>\<exists>!\<ff>. \<ff>:z\<rightarrow>c \<and> (\<^bold>\<exists>!\<jj>. \<jj>:(dom f)\<rightarrow>(dom \<epsilon>) \<and> 
                            p2 \<cdot> \<jj> \<simeq> \<ff> \<cdot> q1 \<and> p1 \<cdot> \<jj> \<simeq> q2 \<and> \<epsilon> \<cdot> \<jj> \<simeq> f)))"


class exponentialCategory2 = categoryProduct +
fixes  exp2::"'a \<Rightarrow> 'a \<Rightarrow> 'a"

  assumes G1: "\<^bold>\<forall>a b. \<^bold>\<exists>\<epsilon>. isExp a b (exp2 a b) \<epsilon>" and
          G2: "E (exp2 a b) \<longrightarrow> (E a \<and> E b)" 
begin
lemmas axiomSet2 = S1 S2 S3 S4 S5 S6 catProd1 catProd2 G1 G2 productAssoc

\<comment> \<open>leo3 finds proof but timeout using metis\<close>
(*lemma "\<exists>x. final x" (*sledgehammer[remote_leo3](S1 S2 S3 S4 S5 S6 catProd1 catProd2 G1 G2 productAssoc)*)
 by (metis G1 G2 S1 S2 S3 S4 S5 S6 catProd1 catProd2)*)


end

class exponentialCategory = categoryProduct +
  fixes  exp::"'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<^sup>_") and
         finalObject::"'a" ("\<^bold>1")

  assumes E1: "\<^bold>\<forall>a b. \<^bold>\<exists>\<epsilon>. isExp a b (exp a b) \<epsilon>" and
          E2: "E (a\<^sup>b) \<longrightarrow> (E a \<and> E b)" and
          E4: "final \<^bold>1"
begin

\<comment> \<open>Feeding this set to sledgehammer will avoid including facts from Isabelle Main\<close>
lemmas axiomSet = S1 S2 S3 S4 S5 S6 catProd1 catProd2 E1 E2 E4 productAssoc

lemma "((A \<^bold>\<times> B)\<^sup>C) \<cong> ((A\<^sup>C) \<^bold>\<times> (B\<^sup>C))" (*sledgehammer sledgehammer [remote_leo3]*)
  by (metis (no_types, hide_lams) E2 S2 S3 S5 S6 E4 catProd1) 

lemma "\<^bold>\<forall>A. (\<^bold>1\<^sup>A) \<simeq> \<^bold>1"  (*sledgehammer(axiomSet) sledgehammer [remote_leo3](axiomSet)*)
  by (smt axiomSet(11) axiomSet(9))  
 
lemma "((B\<^sup>A)\<^sup>C) \<cong> exp B (A \<^bold>\<times> C)" (* sledgehammer(axiomSet) sledgehammer [remote_leo3](axiomSet)*)
  by (smt axiomSet(10) axiomSet(7) axiomSet(8) axiomSet(9))

lemma "\<^bold>\<forall>A. (exp A \<^bold>1) \<simeq> \<^bold>1" (* sledgehammer(axiomSet) sledgehammer [remote_leo3](axiomSet) *)
  by (smt axiomSet(11) axiomSet(9))

(*lemma expIsFunc1: "E (A) \<longrightarrow> isFunctor (\<lambda>(x). (x\<^sup>A))" (*sledgehammer(axiomSet) sledgehammer [remote_leo3](axiomSet)*)
  apply(simp add: imp_conjR)
  apply(rule conjI) 
   apply (smt axiomSet(10) axiomSet(9))
  apply(rule conjI) 
   apply (metis axiomSet(1) axiomSet(11) axiomSet(3) axiomSet(5))
  apply(rule conjI) 
  apply (metis axiomSet(1) axiomSet(10) axiomSet(11) axiomSet(3) axiomSet(5))
  by (metis axiomSet(1) axiomSet(11) axiomSet(3) axiomSet(5))
*)

end

lemma expIsFunc1: "E A \<longrightarrow> isFunctor (\<lambda>(x). (x\<^sup>A))"
apply(simp add: imp_conjR)
  apply(rule conjI) 
   apply (smt axiomSet(10) axiomSet(9))
  apply(rule conjI) 
   apply (metis axiomSet(1) axiomSet(11) axiomSet(3) axiomSet(5))
  apply(rule conjI) 
  apply (metis axiomSet(1) axiomSet(10) axiomSet(11) axiomSet(3) axiomSet(5))
  by (metis axiomSet(1) axiomSet(11) axiomSet(3) axiomSet(5))

proposition "\<^bold>\<forall>A. isFunctor (\<lambda>x. (x\<^sup>A))"
  using expIsFunc1 by blast


axiomatization where productExistence: "E (m:: 'a::category \<times> 'b::category ) \<longleftrightarrow> E (fst m) \<and> E (snd m)"

lemma "True" nitpick[satisfy] oops

instantiation prod :: (category, category) category
begin

lift_definition domain_prod::"'a \<times> 'b \<Rightarrow> 'a \<times> 'b" is "\<lambda>m. ((dom fst m), (dom snd m))" done
lift_definition codomain_prod::"'a \<times> 'b \<Rightarrow> 'a \<times> 'b" is "\<lambda>m. ((cod fst m), (cod snd m))" done
lift_definition composition_prod::"'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" is 
    "\<lambda>g f. (((fst g) \<cdot> (fst f)), ((snd g) \<cdot> (snd f)))" done

instance
proof 
  show "\<And>x::'a \<times> 'b. E x \<^bold>\<leftarrow> E (dom x)"
    apply(transfer)
    apply(simp add: productExistence)
    by (simp add: S1)

  show "\<And>y::'a \<times> 'b. E y \<^bold>\<leftarrow> E (cod y)"
    apply(transfer)
    apply(simp add: productExistence)
    by (simp add: S2)

  show "\<And>(x::'a \<times> 'b) y::'a \<times> 'b. E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y"
    apply(transfer)
    apply(simp add: productExistence)
    by (metis S3)

  show "\<And>(x::'a \<times> 'b) (y::'a \<times> 'b) z::'a \<times> 'b. x \<cdot> (y \<cdot> z) \<cong> (x \<cdot> y) \<cdot> z"
    apply(transfer)
    apply(simp add: productExistence)
    by (meson S4)

  show "\<And>x::'a \<times> 'b. x \<cdot> (dom x) \<cong> x"
    apply(transfer)
    apply(simp add: productExistence)
    by (metis S5 prod.collapse)

  show "\<And>y::'a \<times> 'b. (cod y) \<cdot> y \<cong> y"
    apply(transfer)
    apply(simp add: productExistence)
    by (metis S6 prod.collapse)
qed
end

lemma simpProdDom: "fst (dom (a, b)) = dom a" 
  by (simp add: domain_prod.abs_eq)

lemma simpProdComp: "(fst ((a, b) \<cdot> (aa, ba))) = a \<cdot> aa"
  by (simp add: composition_prod.abs_eq)

proposition "isFunctor (\<lambda>(m::'a::categoryProduct\<times>'a). ((fst m) \<^bold>\<times> (snd m)))"
apply(simp add: imp_conjR)
  apply(rule conjI) 
   apply (smt catProd1 catProd2 fst_conv productExistence snd_conv)
  apply(rule conjI) 
   apply (smt S3 S5 S6 catProd2)
  apply(rule conjI)  
   apply (smt S1 S3 S6 catProd1 catProd2 domain_prod.abs_eq simpProdDom snd_conv)
  by (smt S3 S5 S6 catProd2 composition_prod.abs_eq fst_conv productExistence snd_conv)


end



