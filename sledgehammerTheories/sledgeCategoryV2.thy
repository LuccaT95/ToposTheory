theory sledgeCategoryV2 imports FreeLogic

abbrevs "morphismE" = ":\<rightarrow>" and
        "morphism" = ":\<Rightarrow>" and
        "wedgeE" = "\<leftarrow>-()-\<rightarrow>" and
        "wedge" = "\<Leftarrow>-()-\<Rightarrow>" and
        "cowedgeE" = "-\<rightarrow>()\<leftarrow>-" and
        "ptimes" = "\<^bold>\<times>"

begin

(*Begin: some useful parameter settings*)
declare [[ smt_solver = cvc4, smt_oracle = true, smt_timeout = 180]] declare [[ show_types ]] 
sledgehammer_params [provers = cvc4 z3 spass e vampire remote_leo3]
nitpick_params [user_axioms, show_all, format = 2]
(*nitpick_params[user_axioms, show_all, format = 2, expect = genuine]*)
 (*End: some useful parameter settings*)

section \<open>The Basics of Category Theory\<close>

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

subsection\<open>Basic Definitions\<close>

abbreviation type ("type") where "type x \<equiv> x \<cong> dom x"

abbreviation typeE ("typeE") where "typeE x \<equiv> x \<simeq> dom x"

abbreviation arrow ("(_):(_)\<Rightarrow>(_)" [120,120,120] 119) where
  "x:a\<Rightarrow>b \<equiv> dom x \<cong> a \<and> cod x \<cong> b"

abbreviation arrowE ("(_):(_)\<rightarrow>(_)" [120,120,120] 119) where
  "x:a\<rightarrow>b \<equiv> dom x \<simeq> a \<and> cod x \<simeq> b"

abbreviation wedge ("_\<Leftarrow>_- (_) -_\<Rightarrow>_" [120,0,0,0,120] 119) where
  "a \<Leftarrow>f- (x) -g\<Rightarrow> b \<equiv> f:x\<Rightarrow>a \<and> g:x\<Rightarrow>b"

abbreviation wedgeE ("_\<leftarrow>_- (_) -_\<rightarrow>_" [120,0,0,0,120] 119) where
  "a \<leftarrow>f- (x) -g\<rightarrow> b \<equiv> f:x\<rightarrow>a \<and> g:x\<rightarrow>b"

abbreviation cowedgeE ("_-_\<rightarrow> (_) \<leftarrow>_-_" [120,0,0,120] 119) where
  "a -f\<rightarrow> (x) \<leftarrow>g- b \<equiv> f:a\<rightarrow>x \<and> g:b\<rightarrow>x"

\<comment> \<open>arrows appear in counterclockwise order starting at lower right corner\<close>
abbreviation commutativeSquare ("commSquare") where
  "commSquare g p q f \<equiv> ((dom f)\<Leftarrow>q-(dom p)-p\<Rightarrow>(dom g)) \<and> cod f \<cong> cod g \<and> g\<cdot>p \<cong> f\<cdot>q"

abbreviation commutativeSquareE ("commSquareE") where
  "commSquareE g p q f \<equiv> ((dom f)\<leftarrow>q-(dom p)-p\<rightarrow>(dom g)) \<and> cod f \<simeq> cod g \<and> g\<cdot>p \<simeq> f\<cdot>q"

abbreviation monic::"'a \<Rightarrow> bool" ("monic") where
  "(monic m) \<equiv> \<forall>f g. m\<cdot>f \<simeq> m\<cdot>g \<longrightarrow> f \<simeq> g"

abbreviation epi::"'a \<Rightarrow> bool" ("epi") where
  "(epi m) \<equiv> \<forall>f g. f\<cdot>m \<simeq> g\<cdot>m \<longrightarrow> f \<simeq> g"

abbreviation initial::"'a \<Rightarrow> bool" ("initial") where
  "(initial z) \<equiv> \<^bold>\<forall>t. (type t) \<longrightarrow> (\<^bold>\<exists>!f. f:z\<rightarrow>t)"

abbreviation final::"'a \<Rightarrow> bool" ("final") where
  "final z \<equiv> \<^bold>\<forall>t. (type t) \<longrightarrow> (\<^bold>\<exists>!f. f:t\<rightarrow>z)"

abbreviation isomorphism::"'a \<Rightarrow> bool" ("isomorphism") where
  "(isomorphism f) \<equiv> \<exists>g. f\<cdot>g \<cong> (dom g) \<and> g\<cdot>f \<cong> (dom f)"

abbreviation isomorphic::"'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<cong>" 120) where
  "isomorphic z y \<equiv> \<exists>f. dom f \<cong> z \<and> cod f \<cong> y \<and> isomorphism f"


subsection\<open>More Advanced Definitions\<close>
(*ToDo*)

\<comment> \<open>e is the equalizer for f and g\<close>
abbreviation isEqualizer::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("Equalizer")
  where "isEqualizer f g e \<equiv> f \<cdot> e \<cong> g \<cdot> e \<and>
          (\<^bold>\<forall>z. f \<cdot> z \<simeq> g \<cdot> z \<longrightarrow> (\<^bold>\<exists>!u. u:(dom z)\<rightarrow>(dom e) \<and> e \<cdot> u \<simeq> z))"

(*abbreviation coequalizer*)

abbreviation product::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("product") where
"product a b c p1 p2 \<equiv> p1:c\<Rightarrow>a \<and> p2:c\<Rightarrow>b \<and>
                        (\<^bold>\<forall>x f g. (a\<leftarrow>f-(x)-g\<rightarrow>b) \<longrightarrow> 
                          (\<^bold>\<exists>!h. h:x\<rightarrow>c \<and> f \<simeq> p1\<cdot>h \<and> g \<simeq> p2\<cdot>h))"

abbreviation coproduct::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("coproduct") where
"coproduct a b c p1 p2 \<equiv> p1:a\<Rightarrow>c \<and> p2:b\<Rightarrow>c \<and>
                        (\<^bold>\<forall>x f g. (a-f\<rightarrow>(x)\<leftarrow>g-b) \<longrightarrow> 
                          (\<^bold>\<exists>!h. h:c\<rightarrow>x \<and> f \<simeq> h\<cdot>p1 \<and> g \<simeq> h\<cdot>p2))"

abbreviation isPullback ("pullback") where
  "pullback g p q f \<equiv> commSquare g p q f \<and> 
                        (\<^bold>\<forall>\<beta> \<gamma>. (dom f)\<leftarrow>\<beta>-(dom \<beta>)-\<gamma>\<rightarrow>(dom g) \<and> f\<cdot>\<beta> \<simeq> g\<cdot>\<gamma> \<longrightarrow>
                          (\<^bold>\<exists>!\<delta>. \<delta>:(dom \<beta>)\<rightarrow>(dom p) \<and> q\<cdot>\<delta> \<simeq> \<beta> \<and> p\<cdot>\<delta> \<simeq> \<gamma>))"

abbreviation isPushout ("pushout") where
  "pushout p f g q \<equiv> commSquare g p q f \<and> 
                        (\<^bold>\<forall>\<beta> \<gamma>. ((cod g)-\<gamma>\<rightarrow>(cod \<gamma>)\<leftarrow>\<beta>-(cod f)) \<and> \<beta>\<cdot>f \<simeq> \<gamma>\<cdot>g \<longrightarrow>
                          (\<^bold>\<exists>!\<delta>. \<delta>:(cod p)\<rightarrow>(cod \<gamma>) \<and> \<delta>\<cdot>q \<simeq> \<beta> \<and> \<delta>\<cdot>p \<simeq> \<gamma>))"

end

subsection\<open>Functors\<close>

abbreviation isFunctor::"('a::category \<Rightarrow> 'b::category) \<Rightarrow> bool" ("Functor") where
  "isFunctor F \<equiv> (\<forall>x. E x \<longleftrightarrow> E (F x)) \<and>
                  (\<forall>x. type x \<longrightarrow> type (F x)) \<and> 
                   (\<forall>x. F (dom x) \<cong> dom (F x)) \<and>                    
                  (\<^bold>\<forall>x y. E(x\<cdot>y) \<longrightarrow> (F (x\<cdot>y) \<simeq> (F x) \<cdot> (F y)))"

abbreviation isNaturalTransformation::"('c \<Rightarrow> 'd) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('c::category \<Rightarrow> 'd::category) \<Rightarrow> bool" ("natTrans")
  where "natTrans F G \<upsilon> \<equiv> isFunctor F \<and> isFunctor G \<and> 
                              (\<^bold>\<forall>f::'c. (\<upsilon> (cod f))\<cdot>(F f) \<simeq> (G f)\<cdot>(\<upsilon> (dom f)))"

section\<open>Category with Binary Products\<close>

class productCategory = category +
  fixes product_func::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<^bold>\<times>" 115) and
        p1::"'a \<Rightarrow> 'a" and
        p2::"'a \<Rightarrow> 'a"
  assumes 
          catProd1: "E (a \<^bold>\<times> b) \<longrightarrow> (E a \<and> E b)" and
          catProd3: "E (p1 (a \<^bold>\<times> b)) \<longrightarrow> (E (a \<^bold>\<times> b))" and
          catProd4: "E (p2 (a \<^bold>\<times> b)) \<longrightarrow> (E (a \<^bold>\<times> b))" and
          catProd2: "\<^bold>\<forall>a b. (product  (dom a) (dom b) ((dom a) \<^bold>\<times> (dom b)) (p1 ((dom a) \<^bold>\<times> (dom b))) (p2 ((dom a) \<^bold>\<times> (dom b))))" and
          catProd5: "\<^bold>\<forall>a b. (commSquareE a (p1 ((dom a) \<^bold>\<times> (dom b))) (a \<^bold>\<times> b) (p1 ((cod a) \<^bold>\<times> (cod b))))" and
          catProd6: "\<^bold>\<forall>a b. commSquareE b (p2 ((dom a) \<^bold>\<times> (dom b))) (a \<^bold>\<times> b) (p2 ((cod a) \<^bold>\<times> (cod b)))"

begin

lemma "type A" oops (*sledgehammer(S1 S2 S3 S4 S5 S6 catProd1 catProd2 catProd3 catProd4 catProd5 catProd6)*)

lemma "(typeE a \<and> typeE b) \<longrightarrow> typeE (a \<^bold>\<times> b)" 
  by (metis S2 S3 S5 S6 catProd2)

\<comment> \<open>Surprisingly the next lemma cannot be proven though z3 finds a proof..\<close>
lemma "\<^bold>\<forall>a b. \<^bold>\<exists>p1 p2. product (dom a) (dom b) ((dom a) \<^bold>\<times> (dom b)) p1 p2" oops (*sledgehammer (S2 S3 S5 catProd2 catProd1 catProd4 catProd3)*)
  (*by (smt S2 S3 S5 catProd2) fails*)

end

section\<open>Cartesian Category\<close>

class cartesianCategory = productCategory +
  fixes finalObject::"'a" ("\<^bold>1") and
        finalMap::"'a \<Rightarrow> 'a" ("\<^bold>!")
  assumes
        cartesian1: "\<^bold>\<forall>f g. (f:(dom g)\<rightarrow>(cod g)) \<longrightarrow> (\<^bold>\<exists>e. isEqualizer f g e)" and
        cartesian2: "final \<^bold>1" and
        cartesian3: "\<^bold>\<forall>t. (\<^bold>! t):(dom t)\<rightarrow>\<^bold>1"
begin
lemma "True" nitpick[satisfy] oops
end

section\<open>Cartesian Closed Category\<close>

abbreviation (in productCategory) isExponential:: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("Exp")
  where "Exp a b c \<epsilon> \<equiv> \<^bold>\<exists>p1 p2. product a c (dom \<epsilon>) p1 p2 \<and> \<epsilon>:(a\<^bold>\<times>c)\<rightarrow>b \<and>
                        (\<^bold>\<forall>z f q1 q2. (product z a (dom f) q1 q2 \<and> f:(z\<^bold>\<times>a)\<rightarrow>b) \<longrightarrow>
                          (\<^bold>\<exists>!\<ff>. \<ff>:z\<rightarrow>c \<and> (\<^bold>\<exists>!\<jj>. \<jj>:(dom f)\<rightarrow>(dom \<epsilon>) \<and> 
                            p2 \<cdot> \<jj> \<simeq> \<ff> \<cdot> q1 \<and> p1 \<cdot> \<jj> \<simeq> q2 \<and> \<epsilon> \<cdot> \<jj> \<simeq> f)))"

class exponentialCategory = productCategory +
  fixes  exp::"'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<^sup>_") and
         finalObject::"'a" ("\<^bold>1\<^sub>c")

  assumes E1: "\<^bold>\<forall>a b. (\<^bold>\<exists>\<epsilon>. Exp (dom a) (dom b) (exp a b) \<epsilon>)" and
          E2: "E (a\<^sup>b) \<longrightarrow> (E a \<and> E b)" and
          E3: "final \<^bold>1\<^sub>c"
begin
lemma "E (a\<^sup>b) \<longrightarrow> typeE (a\<^sup>b)"
  by (smt E1 E2 S3 S6)
end


class exponentialCategory2 = productCategory +
  fixes  exp2::"'a \<Rightarrow> 'a \<Rightarrow> 'a" and
         evaluation::"'a" ("\<epsilon>")

  assumes G1: "\<^bold>\<forall>a b. (typeE a \<and> typeE b) \<longrightarrow> (Exp a b (exp2 a b) \<epsilon>)" and
          G2: "E (exp2 a b) \<longrightarrow> (E a \<and> E b)"
begin
lemma "True" nitpick[satisfy] oops
end

section\<open>Topos\<close>

(*abbreviation (in cartesianCategory) subobjectClassifier::"'a \<Rightarrow> 'a \<Rightarrow> bool" ("subC") where
    "subC \<Omega> t \<equiv> t:(\<^bold>1\<^sub>c)\<Rightarrow>\<Omega> \<and> (\<^bold>\<forall>m s. (monic m \<and> s:(dom m)\<rightarrow>(\<^bold>1\<^sub>c)) \<longrightarrow> (\<^bold>\<exists>!\<Phi>. (\<Phi>:(cod m)\<rightarrow>\<Omega>) \<and>
                                                pullback t s m \<Phi>))"*)

class topos = cartesianCategory + exponentialCategory2 +
  fixes classifier::'a ("\<Omega>") and
        true::'a ("true") and
        characteristicMap::"'a \<Rightarrow> 'a" ("char") and
        diagnalMap::"'a \<Rightarrow> 'a" ("\<Delta>")
      assumes T1: "(E m \<and> monic m)  \<longrightarrow> 
                            (((char m):(cod m)\<rightarrow>\<Omega>) \<and> pullback true (\<^bold>! (dom m)) m (char m) \<and> 
                                (\<^bold>\<forall>\<Phi>. ((\<Phi>:(cod m)\<rightarrow>\<Omega>) \<and> pullback true (\<^bold>! (dom m)) m \<Phi>) \<longrightarrow> \<Phi> \<simeq> (char m)))" and
              T2: "\<^bold>\<forall>B. (p1((dom B)\<^bold>\<times>(dom B)))\<cdot>(\<Delta> B) \<simeq> (dom B)" and
              T3: "\<^bold>\<forall>B. (p2((dom B)\<^bold>\<times>(dom B)))\<cdot>(\<Delta> B) \<simeq> (dom B)" and
              T4: "E (char m) \<longrightarrow> E m" and
              T5: "E (\<Delta> B) \<longrightarrow> E B"
begin
lemma "True" nitpick[satisfy] oops

\<comment> \<open>We do not axiomatize the existence of \<Omega> because one existing morphism leads to the desired behaviour. This way the empty topos is possible.\<close>
lemma "(\<exists>x::'a. E x) \<longrightarrow> E \<Omega>" (*sledgehammer (S1 S2 S3 S4 S5 S6 catProd1 catProd2 cartesian1 cartesian2 G1 G2 T1)*)
  by (smt S1 S2 S3 S5 S6 T1 cartesian2)

\<comment> \<open>vampire finds by (metis S1 S2 S3 S5 S6 T1 cartesian2) but timeout --> splitting proof works\<close>
lemma "true:\<^bold>1\<Rightarrow>\<Omega>"
proof -
  consider (a) "E true" | (b) "\<not> (E true)" by auto
  then show ?thesis
  proof cases
case a
  then show ?thesis 
    by (smt S1 S2 S3 S5 S6 T1 cartesian2 cartesian3)
next
  case b
  then show ?thesis
    by (smt S1 S2 S3 S5 S6 T1 cartesian2)
qed 
qed

\<comment> \<open>This justifies our skolemization of \<Delta>\<close>
lemma "typeE B \<longrightarrow>  (\<^bold>\<exists>!f. ((p1(B\<^bold>\<times>B))\<cdot>f \<simeq>  B \<and> (p2(B\<^bold>\<times>B))\<cdot>f \<simeq> B))" (*sledgehammer (S1 S2 S3 S4 S5 S6 catProd1 catProd2 catProd3 catProd4 catProd5 catProd6 cartesian1 cartesian2 G1 G2 T1 T2 T3 T4 T5)*)
  by (smt S2 S3 S4 S5 catProd2)


end

end