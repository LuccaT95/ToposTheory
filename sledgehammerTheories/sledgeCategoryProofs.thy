theory sledgeCategoryProofs imports sledgeCategoryV3

begin

(*Begin: some useful parameter settings*)
declare [[ smt_solver = cvc4, smt_oracle = true, smt_timeout = 300]] declare [[ show_types ]] 
sledgehammer_params [provers = cvc4 z3 e vampire remote_leo3, timeout = 120, isar_proofs = false]
nitpick_params [user_axioms, show_all, format = 2]
(*nitpick_params[user_axioms, show_all, format = 2, expect = genuine]*)
 (*End: some useful parameter settings*)

section\<open>Proofs in Categories\<close>

context category begin
(*sledgehammer(S1 S2 S3 S4 S5 S6) sledgehammer [remote_leo3](S1 S2 S3 S4 S5 S6)*)

  subsection\<open>About initial and final\<close>

\<comment>\<open>Checking equivalences of initial - the same would do for final\<close>
lemma StrongerInitial1: "(initial z) \<longrightarrow>  (\<^bold>\<forall>t.(type t)\<longrightarrow> (\<^bold>\<exists>!f. dom f \<simeq> z \<and> cod f \<simeq> t))" (*  sledgehammer(S1 S2 S3 S4 S5 S6) sledgehammer [remote_leo3](S1 S2 S3 S4 S5 S6)]*) 
  by (metis S2 S3 S5) 

lemma StrongerInitial2: "(\<^bold>\<forall>t. (type t)\<longrightarrow>(\<^bold>\<exists>!f. dom f \<simeq> z \<and> cod f \<simeq> t)) \<longrightarrow> initial z"  (*sledgehammer sledgehammer [remote_leo3]*) 
  by (metis local.S1)

lemma WeakerInitial1: "(\<^bold>\<forall>t. (type t) \<longrightarrow> (\<exists>!f. dom f \<cong> z \<and> cod f \<cong> t)) \<longrightarrow> initial z" (* sledgehammer sledgehammer [remote_leo3] *)
  by (smt S5 S2 S3 category_axioms)

lemma WeakerInitial2: "(initial z) \<longrightarrow> (\<^bold>\<forall>t. (type t) \<longrightarrow> (\<exists>!f. dom f \<cong> z \<and> cod f \<cong> t))"
  by (metis S1) 

lemma InitialsAreIsomorphic: "initial z \<and> initial y \<longrightarrow> z \<^bold>\<cong> y"
  by (smt catAx(1) catAx(2) catAx(3) catAx(4) catAx(5) catAx(6))

lemma InitialIsUnique: "\<forall>z. \<forall>f. initial z \<and> (dom f \<cong> z \<and> cod f \<cong> z) \<longrightarrow> z \<cong> f" (*sledgehammer(S1 S2 S3 S4 S5 S6) sledgehammer [remote_leo3](S1 S2 S3 S4 S5 S6)*)
  by (smt S3 S5 S6)

lemma FinalsAreIsomorphic: "final z \<and> final y \<longrightarrow> z \<^bold>\<cong> y" (*sledgehammer(S1 S2 S3 S4 S5 S6) sledgehammer [remote_leo3](S1 S2 S3 S4 S5 S6)*)
  by (smt S3 S4 S5 S6)

lemma FinalIsUnique: "\<forall>z. \<forall>f. final z \<and> ( dom f \<cong> z \<and> cod f \<cong> z) \<longrightarrow> z \<cong> f" (* sledgehammer sledgehammer [remote_leo3] *)
  by (metis S2 S3 S5 S6)

lemma TwoMonicsBetweenTypes: "(\<^bold>\<forall>(m::'a) (n::'a). monic m \<and> monic n \<and> dom m \<simeq> dom n \<and> cod m \<simeq> cod n \<longrightarrow> (m\<simeq>n))" nitpick oops

  subsection\<open>About epi and mono\<close>

proposition "isomorphism m \<longrightarrow> monic m \<and> epi m"  \<comment>\<open>cvc4 and Leo-III find proof\<close>
  (*sledgehammer(S1 S2 S3 S4 S5 S6) sledgehammer [remote_leo3](S1 S2 S3 S4 S5 S6)*)
  by (smt S1 S3 S4 S5 S6) 

lemma "monic m \<and> epi m \<longrightarrow> isomorphism m" nitpick oops

  subsection\<open>About products\<close>

lemma productIso: "product a b c t1 t2 \<and> product a b d q1 q2 \<longrightarrow> c \<^bold>\<cong> d"   
   by (smt S1 S2 S4 S3 S5 S6)                     

lemma productSym: "((product b a c q1 q2) \<longrightarrow>  (product a b c q2 q1))"  
  by smt

lemma productUnit: "final (u) \<and> typeE a \<longrightarrow> (\<^bold>\<exists>p1 p2. product u a a p1 p2)"
  by (smt S3 S4 S5 S6)

\<comment> \<open>This enables us to generally define the product for all morphisms\<close>
lemma "\<^bold>\<forall>a b c p1 p2 q1 q2. (product  (dom a) (dom b) c p1 p2) \<and> (product (cod a) (cod b) c q1 q2) \<longrightarrow>
                      (\<^bold>\<exists>!f. (commSquareE a p1 f q1 \<and> commSquareE b p2 f q2))" 
  by (smt S3 S4 S5 S6)

(*nitpick finds counterexample*)
lemma mapToInitial: "(initial z \<and> (\<^bold>\<exists>f. f:A\<rightarrow>z)) \<longrightarrow> initial A" nitpick oops

end

section\<open>Category with binary products\<close>
context productCategory begin

proposition prodWithFinal: "final (u) \<and> typeE A \<longrightarrow> (u \<^bold>\<times> A) \<^bold>\<cong> A"
proof
  assume assm: "final (u) \<and> typeE A" 
  then have "\<^bold>\<exists>p1 p2. product u A A p1 p2" using productUnit by auto
  then obtain q1::'a and q2::'a  where prodAssm: "product u A A q1 q2" using assm by smt

  have "typeE u \<and> typeE A" using assm
    by (metis catAx(3) catAx(6))
  then have "product u A (u \<^bold>\<times> A) (p1 (u \<^bold>\<times> A)) (p2 (u \<^bold>\<times> A)) \<and> product u A A q1 q2" using prodCat4 prodAssm by auto
  thus "(u \<^bold>\<times> A) \<^bold>\<cong> A" using productIso[of "(p1 (u \<^bold>\<times> A))" "(u \<^bold>\<times> A)" u "(p2 (u \<^bold>\<times> A))" A q1 A q2 ] by (rule rev_mp)
qed

(* z3 finds proof but timeout*)
proposition SymOfProduct: "typeE A \<and> typeE B \<longrightarrow> (A \<^bold>\<times> B) \<^bold>\<cong> (B \<^bold>\<times> A)"
proof (rule impI)
  assume assm: "typeE A \<and> typeE B"
  have "product A B (A \<^bold>\<times> B) (p1 (A \<^bold>\<times> B)) (p2 (A \<^bold>\<times> B))" using prodCat4 assm by auto
  then have 1:"product B A (A \<^bold>\<times> B) (p2 (A \<^bold>\<times> B)) (p1 (A \<^bold>\<times> B))" by (rule productSym[THEN impE])
  have "product B A (B \<^bold>\<times> A) (p1 (B \<^bold>\<times> A)) (p2 (B \<^bold>\<times> A))" using prodCat4 assm by auto
  thus "(A \<^bold>\<times> B) \<^bold>\<cong> (B \<^bold>\<times> A)" 
    using 1 productIso[where ?a = B and ?b = A and ?c = "(A \<^bold>\<times> B)" and ?d = "(B \<^bold>\<times> A)" and 
                            ?t1.0 = "(p2 (A \<^bold>\<times> B))" and ?t2.0 = "(p1 (A \<^bold>\<times> B))" and ?q1.0 = "(p1 (B \<^bold>\<times> A))"
                            and ?q2.0 = "(p2 (B \<^bold>\<times> A))"] by auto
qed

proposition AssocOfProduct: "typeE A \<and> typeE B \<and> typeE C \<longrightarrow> ((A \<^bold>\<times> B) \<^bold>\<times> C) \<^bold>\<cong> (A \<^bold>\<times> (B \<^bold>\<times> C))" oops

(*Rule which is used in prodWithInitial*)
lemma domP1: "E (f \<cdot> (p1 (a \<^bold>\<times> b))) \<and> type a \<and> type b \<Longrightarrow> dom (f\<cdot>(p1 (a \<^bold>\<times> b))) \<simeq> (a \<^bold>\<times> b)"
  by (smt prodCatAx(10) prodCatAx(2) prodCatAx(3) prodCatAx(4) prodCatAx(5) prodCatAx(7) prodCatAx(8))
end



section\<open>Proofs in Cartesian Categories\<close>

context cartesianCategory begin

subsection\<open>Pullbacks\<close>

\<comment> \<open>z3 finds proof\<close>
proposition pastingLemma: "pullback g p t f \<and> pullback t q s h \<and> commSquare g (p\<cdot>q) s (f\<cdot>h) \<longrightarrow> pullback g (p\<cdot>q) s (f\<cdot>h)" (*sledgehammer(S1 S2 S3 S4 S5 S6) sledgehammer[remote_leo3] (S1 S2 S3 S4 S5 S6)*)
  by (smt cartesianAx(1) cartesianAx(2) cartesianAx(3) cartesianAx(4) cartesianAx(5) cartesianAx(6)) 

lemma "typeE A \<and> initial z \<longrightarrow> ((z \<^bold>\<times> A) \<^bold>\<cong> A)" 
proof 
  assume assm: "typeE A \<and> initial z"
  then obtain f::'a where 1:"f:z\<rightarrow>A \<and> (\<^bold>\<forall>g. g:z\<rightarrow>A \<longrightarrow> g \<simeq> f)" by force
  have "product z A z z f"
    apply(rule conjI)
     apply (metis 1 local.S2 local.S3 local.S5 local.S6)
    apply(rule conjI)
     apply (metis 1)
  proof (rule fall3I, rule impI)
    fix x::'a and v::'a and w::'a
    assume "E x \<and> E v \<and> E w" and "z\<leftarrow>v- x -w\<rightarrow>A"
    show "\<^bold>\<exists>!h. h:x\<rightarrow>z \<and> v \<simeq> z\<cdot>h \<and> w \<simeq> f\<cdot>h" oops
    
end

section\<open>Proofs in Cartesian Closed Categories\<close>

context exponentialCategory begin

lemma prodWithInitial: "initial z \<and> typeE A \<longrightarrow> initial (z \<^bold>\<times> A)"
proof
  assume assm: "initial z \<and> typeE A"
  show "initial (z \<^bold>\<times> A)"
    apply(rule fallI, intro impI)
  proof -
    fix x assume 1: "E x" and 2: "type x"
    then have "\<exists>!f. E f \<and> f:z\<rightarrow>x" using assm by blast
    then obtain f where 3: "E f \<and> f:z\<rightarrow>x \<and> (\<forall>g. E g \<and> g:z\<rightarrow>x \<longrightarrow> g = f)" by auto
    show "(\<^bold>\<exists>!f. f:(z \<^bold>\<times> A)\<rightarrow>x)"
      apply(rule fexI[of "f\<cdot>(p1(z \<^bold>\<times> A))"], rule conjI)
      apply (metis "3" assm prodCatAx(10) prodCatAx(3) prodCatAx(5) prodCatAx(6), rule conjI, rule conjI, rule domP1)
        apply (metis "3" assm prodCatAx(10) prodCatAx(3) prodCatAx(5) prodCatAx(6))
       apply (metis "3" assm prodCatAx(10) prodCatAx(3) prodCatAx(4) prodCatAx(5) prodCatAx(6))
    proof (rule fallI, rule impI, rule impI)
      fix g assume 6:"E g" and 7:"g:(z \<^bold>\<times> A)\<rightarrow>x"
      then have 4:"(tp g):z\<rightarrow>(exp x A)"
        by (metis "2" assm expCatAx(18))
      have 5: "(f \<cdot> p1 (z \<^bold>\<times> A)):(z \<^bold>\<times> A)\<rightarrow>x"
        apply(rule conjI, rule domP1)
        apply (metis "3" assm prodCatAx(10) prodCatAx(3) prodCatAx(5) prodCatAx(6))
        by (metis "3" assm prodCatAx(10) prodCatAx(3) prodCatAx(4) prodCatAx(5) prodCatAx(6)) 
      moreover have "(tp (f\<cdot>(p1 (z \<^bold>\<times> A)))):z\<rightarrow>(exp x A)"
        by (metis "5" assm expCatAx(18) expCatAx(2) expCatAx(3) expCatAx(6))
      then have 8:"(tp (f\<cdot>(p1 (z \<^bold>\<times> A)))) = (tp g)" using 4
        by (metis assm catAx(1) catAx(3) catAx(6))
      have 9:"(\<epsilon> A x) \<cdot> ((tp g) \<^bold>\<times> A) \<simeq> g"
        by (metis "2" "6" "7" assm expCatAxPure(1))
      have 10:"(\<epsilon> A x) \<cdot> ((tp (f\<cdot>(p1 (z \<^bold>\<times> A)))) \<^bold>\<times> A) \<simeq> f\<cdot>(p1 (z \<^bold>\<times> A))"
        by (metis "2" "5" assm catAx(1) expCatAxPure(1))
      have "(\<epsilon> A x) \<cdot> ((tp (f\<cdot>(p1 (z \<^bold>\<times> A)))) \<^bold>\<times> A) \<simeq> g" using 8 9 by auto
      thus "g = f\<cdot>(p1 (z \<^bold>\<times> A))" using 10
        by blast
    qed
  qed
qed

lemma "initial z \<and> typeE A \<longrightarrow> ((z \<^bold>\<times> A) \<^bold>\<cong> z)"
proof (rule impI)
  assume assm: "initial z \<and> typeE A"
  then have 1: "initial (z \<^bold>\<times> A)" using prodWithInitial by auto
  from assm have "initial z" by simp
  thus "(z \<^bold>\<times> A) \<^bold>\<cong> z" using InitialsAreIsomorphic 1 by auto 
qed


(*lemma "(type A \<and> type B \<and> type C) \<longrightarrow> ((A \<^bold>\<times> B)\<^sup>C) \<cong> ((A\<^sup>C) \<^bold>\<times> (B\<^sup>C))" sledgehammer(axiomSet)
 

lemma "\<^bold>\<forall>A. type A \<longrightarrow> (\<^bold>1\<^sub>c\<^sup>A) \<simeq> \<^bold>1\<^sub>c"  (*sledgehammer(axiomSet) sledgehammer [remote_leo3](axiomSet)*)
  by (smt axiomSet(12) axiomSet(13) axiomSet(15))
 
lemma "(type A \<and> type B \<and> type C) \<longrightarrow> ((B\<^sup>A)\<^sup>C) \<cong> exp B (A \<^bold>\<times> C)"  (*sledgehammer(axiomSet) sledgehammer [remote_leo3](axiomSet)*)
  by (smt axiomSet(11) axiomSet(13) axiomSet(14) axiomSet(15) axiomSet(2) axiomSet(7) axiomSet(8)) 

lemma "\<^bold>\<forall>A. type A \<longrightarrow> (exp A \<^bold>1\<^sub>c) \<simeq> \<^bold>1\<^sub>c"  (*sledgehammer(axiomSet) sledgehammer [remote_leo3](axiomSet)*)
  by (smt axiomSet(12) axiomSet(13) axiomSet(15)) *)

end

section\<open>Proofs about Functors\<close>
(*
\<comment> \<open>None of the proofs work with metis here even though they do in Category_Abbrevs.thy\<close>
lemma ExpIsFunc: "typeE A \<longrightarrow> isFunctor (\<lambda>(x). (x\<^sup>A))"
apply(simp add: imp_conjR)
  apply(rule conjI) 
   apply (smt axiomSet(10) axiomSet(7) axiomSet(9))
  apply(rule conjI) 
  apply (smt axiomSet(1) axiomSet(10) axiomSet(3) axiomSet(6) axiomSet(9)) 
  apply(rule conjI) sledgehammer(axiomSet) sledgehammer [remote_leo3](axiomSet)
  apply (smt axiomSet(1) axiomSet(10) axiomSet(10) axiomSet(3) axiomSet(6) axiomSet(9)) 
  by (smt axiomSet(9))

proposition "\<^bold>\<forall>A. isFunctor (\<lambda>x. (x\<^sup>A))"
  using ExpIsFunc by blast*)

section\<open>Topos\<close>

context topos begin

proposition DiagonalMapIsMonic: "monic (\<Delta> B)" (*sledgehammer(axiomSetTopos)*)
  by (smt axiomSetTopos(1) axiomSetTopos(19) axiomSetTopos(22) axiomSetTopos(3) axiomSetTopos(4) axiomSetTopos(5) axiomSetTopos(6)) 
  
abbreviation PredicateOfEquality::"'a \<Rightarrow> 'a" ("\<delta>") where
  "\<delta> \<equiv> \<lambda>B. char (\<Delta> B)"

proposition MonoIsEqualizer: "(E m \<and> monic m) \<longrightarrow> (\<exists>s. (isEqualizer (char m) (true\<cdot>s) m))"
  apply(rule impI)
proof -
  assume 1: "E m \<and> monic m"
  have "isEqualizer (char m) (true\<cdot>(\<^bold>! (dom m))) m"
  proof -
    have 4:"monic (cod m)" 
      by (metis S1 S2 S3 S6)
    then have "pullback true (\<^bold>! (dom(cod m))) (cod m) (char (cod m))" using 1 T1
      by (smt S2) \<comment> \<open>Takes some time\<close>
    hence "(char (cod m))\<cdot>m \<cong> (true\<cdot>(\<^bold>! (dom m)))\<cdot>m" sledgehammer(axiomSetTopos 1)
      by (smt "1" axiomSetTopos(16) axiomSetTopos(3) axiomSetTopos(5) axiomSetTopos(6))
    thus ?thesis  sledgehammer(axiomSetTopos 1)
      by (smt "1" axiomSetTopos(1) axiomSetTopos(12) axiomSetTopos(14) axiomSetTopos(15) axiomSetTopos(16) axiomSetTopos(2) axiomSetTopos(20) axiomSetTopos(3) axiomSetTopos(4) axiomSetTopos(5) axiomSetTopos(6))
      by (smt "1" axiomSetTopos(15) axiomSetTopos(3) axiomSetTopos(5) axiomSetTopos(6))
  qed
  then show "\<exists>s. isEqualizer (char m) (true\<cdot>s) m" by (intro exI)
qed

lemma "type A" sledgehammer(axiomSetTopos)

proposition MonoEpiIso: "\<^bold>\<forall>m. monic m \<and> epi m \<longrightarrow> isomorphism m" sledgehammer(axiomSetTopos MonoIsEqualizer) sledgehammer[remote_leo3](axiomSetTopos)*)
  by (metis axiomSetTopos(1) axiomSetTopos(15) axiomSetTopos(3) axiomSetTopos(5)) 
  apply(rule fallI, rule impI, rule impI)
proof -
  fix m
  assume 1: "E m" and 2: "monic m \<and> epi m"

  from 2 have "\<exists>f g. isEqualizer f g m" using MonoIsEqualizer by blast  
  then obtain f g where 3: "isEqualizer f g m" by auto
  hence 4:"f\<cdot>m \<cong> g\<cdot>m" by blast
  then have "f\<cdot>m \<simeq> g\<cdot>m" using 1 S1 S2 S3 S4 S5 S6 by blast
  show "isomorphism m"
qed

end










end