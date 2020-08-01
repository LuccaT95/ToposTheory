theory IO_Logic imports Main

abbrevs
 f_top="\<^bold>\<top>"  f_bot="\<^bold>\<bottom>" f_neg="\<^bold>\<not>"  f_or="\<^bold>\<or>" f_and="\<^bold>\<and>" f_impl="\<^bold>\<supset>" f_valid="\<lfloor>\<rfloor>"


begin 
 (*Begin: some useful parameter settings*)
  declare [[ smt_solver = cvc4 ]] declare [[ show_types ]]
  nitpick_params [user_axioms, show_all, format = 2]

 (*IO logic in HOL*)
 typedecl i -- "type for possible worlds"     type_synonym e = "(i\<Rightarrow>bool)"
 abbreviation ktop   :: "e"    ("\<^bold>\<top>")  where "\<^bold>\<top> \<equiv> \<lambda>w. True"  
 abbreviation kbot   :: "e"    ("\<^bold>\<bottom>")  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"  
 abbreviation knot   :: "e\<Rightarrow>e"    ("\<^bold>\<not>_"[52]53)  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)"
 abbreviation kor    :: "e\<Rightarrow>e\<Rightarrow>e" (infixr"\<^bold>\<or>"50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"  
 abbreviation kand   :: "e\<Rightarrow>e\<Rightarrow>e" (infixr"\<^bold>\<and>"51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
 abbreviation kimp   :: "e\<Rightarrow>e\<Rightarrow>e" (infixr"\<^bold>\<supset>"49) where "\<phi>\<^bold>\<supset>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
 abbreviation kvalid :: "e\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
 
 abbreviation "outpre \<equiv> \<lambda>G.\<lambda>a.\<lambda>y::e. \<exists>f. \<lfloor>a \<^bold>\<supset> f\<rfloor> \<and> G (f,y)"  

 abbreviation "out1 \<equiv>  \<lambda>G.\<lambda>a.\<lambda>x. \<lfloor>x\<rfloor> \<or> 
    (\<exists>i j k. outpre G a i \<and> outpre G a j \<and> outpre G a k \<and> \<lfloor>(i \<^bold>\<and> j \<^bold>\<and> k) \<^bold>\<supset> x\<rfloor>)" 


(* Some Tests *)
 consts a::e b::e e::e 
 abbreviation "G1 \<equiv> (\<lambda>X. X=(a,e) \<or> X=(b,e))"  (* G = {(a,e),(b,e)} *) 

 lemma "out1 G1 a e" by blast (*proof*)
 lemma "outpre G1 a e" by blast (*proof*)
 lemma "outpre G1 (a \<^bold>\<or> b) e" nitpick oops (*countermodel*)
 lemma "out1 G1 (a \<^bold>\<or> b) e" nitpick oops (*countermodel*)
 lemma "\<lfloor>x\<rfloor> \<Longrightarrow> outpre G1 (a \<^bold>\<or> b) x" nitpick oops (*countermodel*)
 lemma "\<lfloor>x\<rfloor> \<Longrightarrow> out1 G1 (a \<^bold>\<or> b) x" by blast (*proof*)


(* GDPR Example from before *)
 consts    pr_d_lawf::e     erase_d::e      kill_boss::e

 abbreviation (* G = {(T,pr_d_lawf),(pr_d_lawf,\<^bold>\<not>erase_d),(\<^bold>\<not>pr_d_lawf,erase_d)} *)
 "G \<equiv> (\<lambda>X. X=(\<^bold>\<top>,pr_d_lawf) \<or> X=(pr_d_lawf,\<^bold>\<not>erase_d) \<or> X=(\<^bold>\<not>pr_d_lawf,erase_d) )"

 lemma "out1 G (\<^bold>\<not>pr_d_lawf) erase_d" by smt (*proof*)
 lemma "out1 G (\<^bold>\<not>pr_d_lawf) (\<^bold>\<not>erase_d)" nitpick oops (*countermodel*)
 lemma "out1 G (\<^bold>\<not>pr_d_lawf) kill_boss"  nitpick oops (*countermodel*)
 lemma "out1 G (\<^bold>\<not>pr_d_lawf) \<^bold>\<bottom>"  nitpick oops (*countermodel*)



end

