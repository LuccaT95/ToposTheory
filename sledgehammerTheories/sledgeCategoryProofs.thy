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
  by (smt S3 S4 S5 S6)

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

lemma productIso: "((product a b c q1 q2) \<and> (product a b d q1 q2)) \<longrightarrow> c \<^bold>\<cong> d"   
   by (smt S1 S2 S4 S3 S5 S6)                     

lemma productSym: "((product b a c q1 q2) \<longrightarrow>  (product a b c q2 q1))"  
  by smt

lemma productUnit: "\<^bold>\<forall>u a. final (u) \<and> typeE a \<longrightarrow> (\<^bold>\<exists>p1 p2. product u a a p1 p2)"
  by (smt S3 S4 S5 S6)

\<comment> \<open>This enables us to generally define the product for all morphisms\<close>
lemma "\<^bold>\<forall>a b c p1 p2 q1 q2. (product  (dom a) (dom b) c p1 p2) \<and> (product (cod a) (cod b) c q1 q2) \<longrightarrow>
                      (\<^bold>\<exists>!f. (commSquareE a p1 f q1 \<and> commSquareE b p2 f q2))" 
  by (smt S3 S4 S5 S6)

end

section\<open>Category with binary products\<close>
context productCategory begin

(*proposition prodFunc: "isFunctor \<^bold>\<times>"*)

end



section\<open>Proofs in Cartesian Categories\<close>

context cartesianCategory begin

lemmas axiomSetCartesian = S1 S2 S3 S4 S5 S6 catProd1 catProd2 catProd3 catProd4 catProd5 catProd6 
                          cartesian1 cartesian2 cartesian3 cartesian4 cartesian5

subsection\<open>Pullbacks\<close>

\<comment> \<open>z3 finds proof but it cannot be performed\<close>
proposition pastingLemma: "pullback g p t f \<and> pullback t q s h \<and> commSquare g (p\<cdot>q) s (f\<cdot>h) \<longrightarrow> pullback g (p\<cdot>q) s (f\<cdot>h)" oops (*sledgehammer(S1 S2 S3 S4 S5 S6) sledgehammer[remote_leo3] (S1 S2 S3 S4 S5 S6)*)

lemma productUnit2: "\<^bold>\<forall>x a. (initial x \<and> type a) \<longrightarrow> (\<^bold>\<exists>p2. product x a x (dom x) p2)" (*sledgehammer(axiomSetCartesian(11) axiomSetCartesian(12) axiomSetCartesian(13) axiomSetCartesian(14) axiomSetCartesian(3) axiomSetCartesian(5) axiomSetCartesian(6) axiomSetCartesian(8)) sledgehammer[remote_leo3] (axiomSetCartesian)*)
  (*by (smt axiomSetCartesian(11) axiomSetCartesian(12) axiomSetCartesian(13) axiomSetCartesian(14) axiomSetCartesian(3) axiomSetCartesian(5) axiomSetCartesian(6) axiomSetCartesian(8)) *)
  sorry

lemma "typeE A \<longrightarrow> (\<^bold>1 \<^bold>\<times> A) \<^bold>\<cong> A" sledgehammer(axiomSetCartesian)
  by (metis axiomSetCartesian(14) axiomSetCartesian(3) axiomSetCartesian(4) axiomSetCartesian(5) axiomSetCartesian(6) axiomSetCartesian(8))
(*proof 
  consider (a) "E A" | (b) "\<not> (E A)" by auto
  then have "(\<^bold>1\<^sub>c \<^bold>\<times> A) \<^bold>\<cong> A"
  proof cases
    case a
    then have "E \<^bold>1\<^sub>c \<and> E A" 
      by (metis S1 S3 S6 cartesian2)
    then show "(\<^bold>1\<^sub>c \<^bold>\<times> A) \<^bold>\<cong> A"
      by (metis S1 S2 S3 S4 S5 S6 cartesian1 cartesian2 catProd1 catProd2) \<comment> \<open>Takes a few seconds\<close>
  next
    case b
    then show ?thesis 
      by (metis S1 S2 S3 catProd1) *)
end

section\<open>Proofs in Cartesian Closed Categories\<close>

context exponentialCategory begin

\<comment> \<open>Feeding this set to sledgehammer will avoid including facts from Isabelle Main\<close>
lemmas axiomSet = S1 S2 S3 S4 S5 S6 catProd1 catProd2 catProd3 catProd4 catProd5 catProd6  E1 E2 E3

(*lemma "(type A \<and> type B \<and> type C) \<longrightarrow> ((A \<^bold>\<times> B)\<^sup>C) \<cong> ((A\<^sup>C) \<^bold>\<times> (B\<^sup>C))" sledgehammer(axiomSet)
 

lemma "\<^bold>\<forall>A. type A \<longrightarrow> (\<^bold>1\<^sub>c\<^sup>A) \<simeq> \<^bold>1\<^sub>c"  (*sledgehammer(axiomSet) sledgehammer [remote_leo3](axiomSet)*)
  by (smt axiomSet(12) axiomSet(13) axiomSet(15))
 
lemma "(type A \<and> type B \<and> type C) \<longrightarrow> ((B\<^sup>A)\<^sup>C) \<cong> exp B (A \<^bold>\<times> C)"  (*sledgehammer(axiomSet) sledgehammer [remote_leo3](axiomSet)*)
  by (smt axiomSet(11) axiomSet(13) axiomSet(14) axiomSet(15) axiomSet(2) axiomSet(7) axiomSet(8)) 

lemma "\<^bold>\<forall>A. type A \<longrightarrow> (exp A \<^bold>1\<^sub>c) \<simeq> \<^bold>1\<^sub>c"  (*sledgehammer(axiomSet) sledgehammer [remote_leo3](axiomSet)*)
  by (smt axiomSet(12) axiomSet(13) axiomSet(15)) *)

end

context exponentialCategory2 begin
\<comment> \<open>leo3 finds proof but timeout using metis\<close>
(*lemma "\<exists>x. final x" (*sledgehammer[remote_leo3](S1 S2 S3 S4 S5 S6 catProd1 catProd2 G1 G2 productAssoc)*)
 by (metis G1 G2 S1 S2 S3 S4 S5 S6 catProd1 catProd2)*)
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
lemmas axiomSetTopos = S1 S2 S3 S4 S5 S6 catProd1 catProd2 catProd3 catProd4 catProd5 catProd6 
                          cartesian1 cartesian2 cartesian3 G1 G2 T1 T2 T3 T4 T5

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