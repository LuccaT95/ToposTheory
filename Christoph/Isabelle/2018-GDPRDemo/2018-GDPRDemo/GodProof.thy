theory GodProof imports Main 
  
abbrevs  
 mneg="\<^bold>\<not>" mor="( \<^bold>\<or> )" mand="( \<^bold>\<and> )" mimpl="( \<^bold>\<rightarrow> )" mequ="( \<^bold>\<leftrightarrow> )" 
 mor="\<^bold>\<or>" mand="\<^bold>\<and>" mimpl="\<^bold>\<rightarrow>" mequ="\<^bold>\<leftrightarrow>"  
 mequpred="\<^sup>\<not>" mequal="( \<^bold>= )" mequal="\<^bold>=" mequal="( \<^bold>=L )" mequal="\<^bold>=L"   
 malli="(\<^bold>\<forall>\<^sup>ix. )" mallp="(\<^bold>\<forall>\<^sup>p\<Phi>. )" mexii="(\<^bold>\<exists>\<^sup>ix. )" mexip="(\<^bold>\<exists>\<^sup>p\<Phi>. )"  
 malli="\<^bold>\<forall>\<^sup>i" mallp="\<^bold>\<forall>\<^sup>p" maxii="\<^bold>\<exists>\<^sup>i" mexip="\<^bold>\<exists>\<^sup>p"  
 mbox="(\<^bold>\<box> )" mdia="(\<^bold>\<diamond> )"   
 mbox="\<^bold>\<box>" media="\<^bold>\<diamond>"   
 mvalid="\<lfloor>\<rfloor>"  mvalid="\"\<lfloor>\<rfloor>\""   
 P="P()"  G="G()"  ess="( ess )"  NE="NE()" d="\<Phi>" d="\<Psi>"   
  
begin
 declare [[smt_solver = cvc4, smt_timeout = 200]]

 typedecl i -- "type for possible worlds" 
 typedecl \<mu> -- "type for individuals"      
 type_synonym \<sigma> = "(i\<Rightarrow>bool)"

(* Shallow embedding modal logic connectives in HOL *)
 abbreviation mneg ("\<^bold>\<not>_"[52]53)    where "\<^bold>\<not>\<phi>   \<equiv> \<lambda>w. \<not>\<phi>(w)"  
 abbreviation mand (infixr"\<^bold>\<and>"51)   where "\<phi>\<^bold>\<and>\<psi>  \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
 abbreviation mor (infixr"\<^bold>\<or>"50)    where "\<phi>\<^bold>\<or>\<psi>  \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
 abbreviation mimp (infixr"\<^bold>\<rightarrow>"49)   where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
 abbreviation mequ (infixr"\<^bold>\<leftrightarrow>"48)   where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)" 
 abbreviation mnegpred ("\<^sup>\<not>_"[52]53) where "\<^sup>\<not>\<Phi>   \<equiv> \<lambda>x.\<lambda>w. \<not>\<Phi>(x)(w)"  

(* Generic box and diamond operators *)
 abbreviation mboxgen ("\<box>") where "\<box>r \<phi> \<equiv> \<lambda>w. \<forall>v.  r w v \<longrightarrow> \<phi>(v)"
 abbreviation mdiagen ("\<diamond>") where "\<diamond>r \<phi> \<equiv> \<lambda>w. \<exists>v. r w v \<and> \<phi>(v)" 

(* Shallow embedding of constant domain quantifiers in HOL *)
 abbreviation mall_const ("\<^bold>\<forall>c") where "\<^bold>\<forall>c \<Phi> \<equiv> \<lambda>w.\<forall>x. \<Phi>(x)(w)"
 abbreviation mallB_const (binder"\<^bold>\<forall>c"[8]9) where "\<^bold>\<forall>c x. \<phi>(x) \<equiv> \<^bold>\<forall>c \<phi>" 
 abbreviation mexi_const ("\<^bold>\<exists>c") where "\<^bold>\<exists>c \<Phi> \<equiv> \<lambda>w.\<exists>x. \<Phi>(x)(w)"
 abbreviation mexiB_const (binder"\<^bold>\<exists>c"[8]9) where "\<^bold>\<exists>c x. \<phi>(x) \<equiv> \<^bold>\<exists>c \<phi>"   

(* Global validity: truth in all possible worlds *)
 abbreviation mvalid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>"[7]110) where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"

(* Shallow embedding of varying domain quantifiers in HOL *)
 consts eiw :: "'a \<Rightarrow> 'b \<Rightarrow> bool"    
 axiomatization where nonempty: "\<forall>w. \<exists>x. eiw w x"
 abbreviation mall_var ("\<^bold>\<forall>v") 
  where "\<^bold>\<forall>v \<Phi> \<equiv> \<lambda>w.\<forall>x. eiw(w)(x) \<longrightarrow> \<Phi>(x)(w)"
 abbreviation mallB_var (binder"\<^bold>\<forall>v"[8]9) 
  where "\<^bold>\<forall>v x. \<phi>(x) \<equiv> \<^bold>\<forall>v \<phi>"   
 abbreviation mexi_var ("\<^bold>\<exists>v") 
  where "\<^bold>\<exists>v \<Phi> \<equiv> \<lambda>w.\<exists>x. eiw(w)(x) \<and> \<Phi>(x)(w)"
 abbreviation mexiB_var (binder"\<^bold>\<exists>v"[8]9) 
  where "\<^bold>\<exists>v x. \<phi>(x) \<equiv> \<^bold>\<exists>v \<phi>"   



(* Reflexivity, symmetry and transitivity of relations *)
 abbreviation ref 
  where "ref r \<equiv> \<forall>x. r x x"
 abbreviation sym 
  where "sym r \<equiv> \<forall>x y. r x y \<longrightarrow> r y x"
 abbreviation trans 
  where "trans r \<equiv> \<forall>x y z. r x y \<and> r y z \<longrightarrow> r x z" 

(* Different accessibility relations for different modal logics *)
 consts 
   K :: "i\<Rightarrow>i\<Rightarrow>bool" 
   KB :: "i\<Rightarrow>i\<Rightarrow>bool" 
   S4 :: "i\<Rightarrow>i\<Rightarrow>bool" 
   S5 :: "i\<Rightarrow>i\<Rightarrow>bool" 
 axiomatization where 
   KB: "sym KB" and 
   S4: "ref S4 \<and> trans S4" and
   S5: "ref S5 \<and> sym S5 \<and> trans S5"

(* **************************************************************** *)

(* Setting Parameters for Experimentation with Ontological Argument *)
(* Default: Second-Order S5 with constant domain quantifiers *)

 abbreviation mbox  ("\<^bold>\<box>") 
   where "\<^bold>\<box> \<equiv> \<box>S5"
 abbreviation mdia  ("\<^bold>\<diamond>") 
  where "\<^bold>\<diamond> \<equiv> \<diamond>S5" 

 abbreviation mall_ind :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>\<^sup>i"[8]9) 
  where "\<^bold>\<forall>\<^sup>ix. \<phi>(x) \<equiv> \<^bold>\<forall>c \<phi>"   
 abbreviation mexi_ind :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>\<^sup>i"[8]9) 
  where "\<^bold>\<exists>\<^sup>ix. \<phi>(x) \<equiv> \<^bold>\<exists>c \<phi>"   

 abbreviation mall_prop :: "((\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>\<^sup>p"[8]9) 
  where "\<^bold>\<forall>\<^sup>px. \<phi>(x) \<equiv> \<^bold>\<forall>c \<phi>"   
 abbreviation mexi_prop :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>\<^sup>p"[8]9) 
  where "\<^bold>\<exists>\<^sup>px. \<phi>(x) \<equiv> \<^bold>\<exists>c \<phi>"   

(* **************************************************************** *)
(* Analysis of Gödel's Ontological Argument (in Scott's version) *)

(* Positiveness *)
 consts P :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>"  

 axiomatization where
(* A1: Either a property or its negation is positive, but not both *)
   A1a: "\<lfloor>\<^bold>\<forall>\<^sup>p\<Phi>. P(\<^sup>\<not>\<Phi>) \<^bold>\<rightarrow> \<^bold>\<not>P(\<Phi>)\<rfloor>" and 
   A1b: "\<lfloor>\<^bold>\<forall>\<^sup>p\<Phi>. \<^bold>\<not>P(\<Phi>) \<^bold>\<rightarrow> P(\<^sup>\<not>\<Phi>)\<rfloor>" and 
(* A2: A property necessarily implied by a positive property is positive *)
   A2: "\<lfloor>\<^bold>\<forall>\<^sup>p\<Phi> \<Psi>. P(\<Phi>) \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>\<^sup>ix. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> P(\<Psi>)\<rfloor>"

(* T1: Positive properties are possibly exemplified *)
 theorem T1: "\<lfloor>\<^bold>\<forall>\<^sup>p\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>\<^sup>ix. \<Phi>(x))\<rfloor>" 
  using A1a A2 by blast

(* God: A God-like being possesses all positive properties *)
 definition G where "G(x) = (\<^bold>\<forall>\<^sup>p\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<Phi>(x))"   

(* A3: The property of being God-like is positive *)
 axiomatization where A3: "\<lfloor>P(G)\<rfloor>"

(* C: Possibly, God exists *) 
 corollary C: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>ix. G(x))\<rfloor>" by (simp add: A3 T1)

(* A4: Positive properties are necessarily positive *)
 axiomatization where A4: "\<lfloor>\<^bold>\<forall>\<^sup>p\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<box>(P(\<Phi>))\<rfloor>" 

(* Ess: An essence of an individual is a property possessed by 
        it and necessarily implying any of its properties: *)
 definition ess (infixr "ess" 85) where
    "\<Phi> ess x = \<Phi> x \<^bold>\<and> (\<^bold>\<forall>\<^sup>p\<Psi>. \<Psi>(x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>iy. \<Phi>(y) \<^bold>\<rightarrow> \<Psi>(y)))"

(* T2: Being God-like is an essence of any God-like being *)
 theorem T2: "\<lfloor>\<^bold>\<forall>\<^sup>ix. G(x) \<^bold>\<rightarrow> G ess x\<rfloor>" by (metis A1b A4 G_def ess_def)

(* NE: Necessary existence of an individual is the necessary 
       exemplification of all its￼essences *)
 definition NE where "NE(x) = (\<^bold>\<forall>\<^sup>p\<Phi>. \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>\<^sup>iy. \<Phi>(y)))"

(* A5: Necessary existence is a positive property *)
 axiomatization where A5:  "\<lfloor>P(NE)\<rfloor>"

(* T3: Necessarily, God exists *)
 theorem T3: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>\<^sup>ix. G(x))\<rfloor>" 
  sledgehammer
  sledgehammer [remote_leo2 remote_satallax] 
  by (metis A3 A5 G_def NE_def S5 T1 T2)


(* Consistency is confirmed by Nitpick *)
 lemma True nitpick [satisfy,user_axioms,show_all] nunchaku [satisfy]  oops  

 lemma False sledgehammer [remote_leo2,verbose] oops

end
