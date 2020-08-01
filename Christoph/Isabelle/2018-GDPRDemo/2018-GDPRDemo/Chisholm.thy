theory Chisholm imports SDL                             (* Christoph Benzmüller, 2018 *)

begin (* Chisholm Example *) 
 consts go::\<sigma> tell::\<sigma> kill::\<sigma>
 axiomatization where
  D1: "\<lfloor>\<^bold>O\<^bold>\<langle>go\<^bold>\<rangle>\<rfloor>" (*It ought to be that Jones goes to assist his neighbors.*) and
  D2: "\<lfloor>\<^bold>O\<^bold>\<langle>go \<^bold>\<rightarrow> tell\<^bold>\<rangle>\<rfloor>"  (*It ought to be that if Jones goes, then he tells them he is coming.*) and
  D3: "\<lfloor>\<^bold>\<not>go \<^bold>\<rightarrow> \<^bold>O\<^bold>\<langle>\<^bold>\<not>tell\<^bold>\<rangle>\<rfloor>" (*If Jones doesn't go, then he ought not tell them he is coming.*) and
  D4: "\<lfloor>\<^bold>\<not>go\<rfloor>\<^sub>c\<^sub>w" (*Jones doesn't go. (This is encoded as a locally valid statement.)*)

 (*Some Experiments*) 
  sledgehammer_params [max_facts=20] (*Sets default parameters for the theorem provers*)
  nitpick_params [user_axioms,expect=genuine,show_all,format=2] (*... and for the model finder.*)

 lemma True  nitpick [satisfy] oops  (*Consistency-check: Is there a model?*) 
 lemma False sledgehammer      oops  (*Inconsistency-check: Can Falsum be derived?*) 

 lemma "\<lfloor>\<^bold>O\<^bold>\<langle>\<^bold>\<not>tell\<^bold>\<rangle>\<rfloor>" sledgehammer  nitpick oops   (*Should James not tell?*)
 lemma "\<lfloor>\<^bold>O\<^bold>\<langle>tell\<^bold>\<rangle>\<rfloor>"  sledgehammer  nitpick oops   (*Should James tell?*)
 lemma "\<lfloor>\<^bold>O\<^bold>\<langle>kill\<^bold>\<rangle>\<rfloor>"  sledgehammer  nitpick oops   (*Should James kill?*)              
end

