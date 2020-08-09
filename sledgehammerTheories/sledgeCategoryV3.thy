theory sledgeCategoryV3 imports FreeLogic
                                     
abbrevs "morphismE" = ":\<rightarrow>" and
        "morphism" = ":\<Rightarrow>" and
        "wedgeE" = "\<leftarrow>-()-\<rightarrow>" and
        "wedge" = "\<Leftarrow>-()-\<Rightarrow>" and
        "cowedgeE" = "-\<rightarrow>()\<leftarrow>-" and
        "ptimes" = "\<^bold>\<times>"

begin

(*Begin: some useful parameter settings*)
declare [[ smt_solver = cvc4, smt_oracle = true, smt_timeout = 300]] declare [[ show_types ]] 
sledgehammer_params [provers = cvc4 z3 e vampire remote_leo3, timeout = 120, isar_proofs = false]
nitpick_params [user_axioms, show_all, format = 2]
(*nitpick_params[user_axioms, show_all, format = 2, expect = genuine]*)
 (*End: some useful parameter settings*)

section \<open>The Basics of Category Theory\<close>

class category =     
  fixes domain:: "'a \<Rightarrow> 'a" ("dom _" [108] 109) and
        codomain:: "'a \<Rightarrow> 'a" ("cod _" [110] 111) and
        composition:: "'a \<Rightarrow> 'a  \<Rightarrow> 'a" (infix "\<cdot>" 110)
        
  assumes   
        S1: "E(dom x) \<longrightarrow> E x" and         
        S2: "E(cod y) \<longrightarrow> E y" and
        S3: "E(x\<cdot>y) \<longleftrightarrow> dom x \<simeq> cod y" and
        S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and    
        S5: "x\<cdot>(dom x) \<cong> x" and           
        S6: "(cod y)\<cdot>y \<cong> y"
begin

lemmas catAx = S1 S2 S3 S4 S5 S6

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
  "commSquare g p q f \<equiv> g\<cdot>p \<cong> f\<cdot>q"

abbreviation commutativeSquareE ("commSquareE") where
  "commSquareE g p q f \<equiv> g\<cdot>p \<simeq> f\<cdot>q"

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

abbreviation iso2::"'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "iso2 x y \<equiv> \<^bold>\<exists>f g. f\<cdot>g \<simeq> x \<and> g\<cdot>f \<simeq> y"

subsection\<open>More Advanced Definitions\<close>
(*ToDo*)

\<comment> \<open>e is the equalizer for f and g\<close>
abbreviation isEqualizer::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("Equalizer")
  where "isEqualizer f g e \<equiv> f \<cdot> e \<simeq> g \<cdot> e \<and>
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
          prodCat1: "E (a \<^bold>\<times> b) \<longrightarrow> (E a \<and> E b)" and
          prodCat2: "E (p1 a) \<longrightarrow> (E a)" and
          prodCat3: "E (p2 b) \<longrightarrow> (E b)" and
          prodCat4: "typeE a \<and> typeE b \<longrightarrow> product a b (a \<^bold>\<times> b) (p1 (a \<^bold>\<times> b)) (p2 (a \<^bold>\<times> b))" and
          prodCat5: "commSquare a (p1 ((dom a) \<^bold>\<times> (dom b))) (a \<^bold>\<times> b) (p1 ((cod a) \<^bold>\<times> (cod b)))" and
          prodCat6: "commSquare b (p2 ((dom a) \<^bold>\<times> (dom b))) (a \<^bold>\<times> b) (p2 ((cod a) \<^bold>\<times> (cod b)))"

begin
lemma "True" nitpick[satisfy] oops
lemma "\<exists>x::'a. E x" nitpick[satisfy] oops

lemmas prodCatAx = catAx prodCat1 prodCat2 prodCat3 prodCat4 prodCat5 prodCat6
lemmas prodCatAxPure = prodCat1 prodCat2 prodCat3 prodCat4 prodCat5 prodCat6

\<comment> \<open>We can decide about the domain of p1 in any case\<close>
lemma "((dom a) \<^bold>\<times> (dom b)) \<cong> dom (p1 ((dom a) \<^bold>\<times> (dom b)))" 
  by (metis S1 S3 S5 S6 prodCat1 prodCat4 prodCat2)

\<comment> \<open>This is not true for the codomain: The reason is that (dom a) might exist even though (dom a \<times> dom b) does not.\<close>
lemma "(dom a) \<cong> cod (p1 ((dom a) \<^bold>\<times> (dom b)))" oops

lemma "type A" oops

lemma "(typeE a \<and> typeE b) \<longrightarrow> typeE (a \<^bold>\<times> b)" 
  by (metis local.S3 local.S5 local.S6 local.prodCat4)

lemma "\<^bold>\<forall>a b. typeE a \<and> typeE b \<longrightarrow> (\<^bold>\<exists>p1 p2. product a b (a \<^bold>\<times> b) p1 p2)" (*sledgehammer (S2 S3 S5 catProd2 catProd1 catProd4 catProd3)*)
  by (smt S2 prodCat4)

end

section\<open>Cartesian Category\<close>

class cartesianCategory = productCategory +
  fixes equalizer::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<doteq>" 120) and
        finalObject::"'a" ("\<^bold>1") and
        finalMap::"'a \<Rightarrow> 'a" ("!\<^sub>1")
  assumes
        cartesian1: "f:(dom g)\<rightarrow>(cod g) \<longrightarrow> isEqualizer f g (f \<doteq> g)" and
        cartesian2: "final \<^bold>1" and
        cartesian3: "typeE t \<longrightarrow> (!\<^sub>1 t):t\<Rightarrow>\<^bold>1" and
        cartesian4: "E (!\<^sub>1 t) \<longrightarrow> typeE t" and
        cartesian5: "E (f \<doteq> g) \<longrightarrow> f:(dom g)\<rightarrow>(cod g)"
begin
lemma "True" nitpick[satisfy] oops

lemmas cartesianAx = prodCatAx cartesian1 cartesian2 cartesian3 cartesian4 cartesian5
lemmas cartesianAxPure = cartesian1 cartesian2 cartesian3 cartesian4 cartesian5

lemma "(f:(dom g) \<rightarrow> (cod g) \<and> isEqualizer f g e) \<longrightarrow> E e" 
  using S2 S3 by blast  

lemma "\<not> (E (f \<doteq> g)) \<longrightarrow> \<not> (f:(dom g) \<rightarrow> (cod g))" 
  using S2 S3 cartesian1 by blast

lemma "typeE t \<longrightarrow> (!\<^sub>1 t):t\<rightarrow>\<^bold>1" 
  using local.cartesian2 local.cartesian3 by auto

(*lemma "type t" sledgehammer (S1 S2 S3 S4 S5 S6 catProd1 catProd2 catProd3 catProd4 catProd5 catProd6 cartesian1 cartesian2 cartesian3 cartesian4 cartesian5)*)

end

section\<open>Cartesian Closed Category\<close>

abbreviation (in productCategory) isExponential:: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" ("Exp")
  where "Exp a b c \<epsilon> tp \<equiv> \<epsilon>:(c\<^bold>\<times>a)\<Rightarrow>b \<and> (\<^bold>\<forall>z f. f:(z \<^bold>\<times> a)\<rightarrow>b \<longrightarrow>
                            ((tp f):z\<rightarrow>c) \<and> \<epsilon> \<cdot> ((tp f) \<^bold>\<times> a) \<simeq> f \<and>
                              (\<^bold>\<forall>\<ff>. \<ff>:z\<rightarrow>c \<and> \<epsilon> \<cdot> (\<ff> \<^bold>\<times> a) \<simeq> f \<longrightarrow> \<ff> \<simeq> (tp f)))"

class exponentialCategory = cartesianCategory +
  fixes  exp::"'a \<Rightarrow> 'a \<Rightarrow> 'a" and
         evaluation::"'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<epsilon>") and
         tp::"'a \<Rightarrow> 'a" 

  assumes G1: "(typeE a \<and> typeE b) \<longrightarrow> (Exp a b (exp b a) (\<epsilon> a b) tp)" and
          G2: "commSquare f (\<epsilon> (dom f) a) ((exp f a) \<^bold>\<times> a) (\<epsilon> (cod f) a)" and
          G3: "E (exp b a) \<longrightarrow> E b \<and> typeE a" and
          G4: "E (\<epsilon> a b) \<longrightarrow> typeE a \<and> E b" and
          G5: "E (tp a) \<longrightarrow> E a"
begin
lemma "True" nitpick[satisfy] oops

lemmas expCatAx = cartesianAx G1 G2 G3 G4 G5
lemmas expCatAxPure = G1 G2 G3 G4 G5

(*This helps justifing G2*)
lemma expArrow: "(commSquare f (\<epsilon> (dom f) a) ((tp (f\<cdot>(\<epsilon> (dom f) a))) \<^bold>\<times> a) (\<epsilon> (cod f) a))"
  by (smt expCatAx(1) expCatAx(18) expCatAx(19) expCatAx(2) expCatAx(20) expCatAx(22) expCatAx(3) expCatAx(4) expCatAx(6) expCatAx(7))

lemma expArrow2: "\<exists>e. (commSquare f (\<epsilon> (dom f) a) (e \<^bold>\<times> a) (\<epsilon> (cod f) a))" using expArrow by auto

(*proposition "E f \<and> typeE a \<and> E (\<epsilon> a (dom f)) \<and> E (\<epsilon> a (cod f)) \<longrightarrow> (\<^bold>\<exists>!e. (commSquare f (\<epsilon> a (dom f)) (a \<^bold>\<times> e) (\<epsilon> a (cod f))))" sledgehammer(expCatAx expArrow2)

proposition "E f \<and> typeE a \<and> E (\<epsilon> a (dom f)) \<longrightarrow> exp f a \<simeq> (tp (f\<cdot>(\<epsilon> a (dom f))))" *)

end

class topos = exponentialCategory +
  fixes classifier::'a ("\<Omega>") and
        true::'a ("true") and
        characteristicMap::"'a \<Rightarrow> 'a" ("char") and
        diagnalMap::"'a \<Rightarrow> 'a" ("\<Delta>")

  assumes T1: "(E m \<and> monic m) \<longrightarrow> 
                (((char m):(cod m)\<rightarrow>\<Omega>) \<and> pullback true (!\<^sub>1 (dom m)) m (char m) \<and> 
                  (\<^bold>\<forall>\<Phi>. ((\<Phi>:(cod m)\<rightarrow>\<Omega>) \<and> pullback true (!\<^sub>1 (dom m)) m \<Phi>) \<longrightarrow> \<Phi> \<simeq> (char m)))" and
          T2: "(p1((dom B)\<^bold>\<times>(dom B)))\<cdot>(\<Delta> B) \<cong> (dom B)" and
          T3: "(p2((dom B)\<^bold>\<times>(dom B)))\<cdot>(\<Delta> B) \<cong> (dom B)" and
          T4: "E (char m) \<longrightarrow> E m" and
          T5: "E (\<Delta> B) \<longrightarrow> E B"
begin

lemmas toposAx = expCatAx T1 T2 T3 T4 T5
lemmas toposAxPure = T1 T2 T3 T4 T5

\<comment> \<open>We do not axiomatize the existence of \<Omega> because one existing morphism leads to the desired behaviour. This way the empty topos is possible.\<close>
lemma "(\<exists>x::'a. E x) \<longrightarrow> E \<Omega>" (*sledgehammer (S1 S2 S3 S4 S5 S6 catProd1 catProd2 cartesian1 cartesian2 G1 G2 T1)*)
  by (smt S1 S2 S3 S5 S6 T1 cartesian2)

lemma "true:\<^bold>1\<Rightarrow>\<Omega>" (*sledgehammer(S1 S2 S3 S5 S6 T1 cartesian2 cartesian3)*)
  by (smt S1 S2 S3 S5 S6 T1 cartesian2 cartesian3)

\<comment> \<open>This justifies our skolemization of \<Delta>\<close>
lemma "typeE B \<longrightarrow>  (\<^bold>\<exists>!f. ((p1(B\<^bold>\<times>B))\<cdot>f \<simeq>  B \<and> (p2(B\<^bold>\<times>B))\<cdot>f \<simeq> B))" (*sledgehammer (S1 S2 S3 S4 S5 S6 catProd1 catProd2 catProd3 catProd4 catProd5 catProd6 cartesian1 cartesian2 G1 G2 T1 T2 T3 T4 T5)*)
  by (smt S2 S3 S4 S5 prodCat4)

abbreviation PredicateOfEquality::"'a \<Rightarrow> 'a" ("\<delta>") where
  "\<delta> \<equiv> \<lambda>B. char (\<Delta> B)"

end

end
















