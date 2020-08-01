theory GDPRGlobal imports SDL        (* Christoph Benzmüller & Xavier Parent, 2018 *)

begin (*** GDPR Example ***)
 consts process_data_lawfully::\<sigma> erase_data::\<sigma> kill_boss::\<sigma>

 axiomatization where
  (* It is an obligation to process data lawfully. *)
    A1: "\<lfloor>\<^bold>O\<^bold>\<langle>process_data_lawfully\<^bold>\<rangle>\<rfloor>" 
  (* Given a situation where data is processed unlawfully. *) and
    A3: "\<lfloor>\<^bold>\<not>process_data_lawfully\<rfloor>" 

 (*** Some Experiments ***) 
  lemma True  nitpick [satisfy] nunchaku [satisfy] oops  (* Consistency-check: Is there a model? *) 
  lemma False sledgehammer      oops  (* Inconsistency-check: Can Falsum be derived? *) 

  lemma "\<lfloor>\<^bold>O\<^bold>\<langle>erase_data\<^bold>\<rangle>\<rfloor>"   sledgehammer nitpick oops  (* Should the data be erased? *)
  lemma "\<lfloor>\<^bold>O\<^bold>\<langle>\<^bold>\<not>erase_data\<^bold>\<rangle>\<rfloor>"  sledgehammer nitpick oops  (* Should the data be kept? *)
  lemma "\<lfloor>\<^bold>O\<^bold>\<langle>kill_boss\<^bold>\<rangle>\<rfloor>"    sledgehammer nitpick oops  (* Should the boss be killed? *)            
end




    
 