theory STVO imports DDL

begin

consts w::i (*world in which we create a situation*)

typedecl p (*type for person such as owner*)

consts owner::p
consts driver::p

typedecl m (*type for measures as in things to do in a situation*)

consts preventAccidentCongestion::m

(*---------- Predicates to describe a given situation within the traffic system -------*)
  (* These are basically on/off switches for creating a situation*)

(*Getting in or out of vehicle*)
consts gettingInOrOut_ofVehicle::\<sigma>

(*Who has taken measures?*)
measureTakenBy::"m \<Rightarrow> p \<Rightarrow> \<sigma>"

(*Did we leave the vehicle?*)
consts vehicleIsLeft::\<sigma>

(*Do we participate in traffic?*)
consts participationTraffic::\<sigma>

(*Should we be careful and considerate?*)
consts carefulAndConsiderate::\<sigma>

(*Should we harm others?*)
consts harmfulAction::\<sigma>

(*Should we annoy others?*)
consts annoyingAction::\<sigma>

(*Can we avoid an annoying action?*)
isAvoidable_annoyingAction::"\<sigma> \<Rightarrow> \<sigma>"
(*------------------------------------------------------------------------------------*)


(*------------------------------------- Grundregeln ----------------------------------*)
axiomatization where
  (*Participation in traffic requires caution and consideration*)
  ax1_1: "\<lfloor> \<^bold>O\<^bold>\<langle> carefulAndConsiderate \<^bold>| participationTraffic \<^bold>\<rangle> \<rfloor>" and

  (*Participation in traffic should not lead to harm of others or annoyance more then necessary*)
  ax1_2_1: "\<lfloor> \<^bold>O\<^bold>\<langle> (\<^bold>\<not>harmfulAction) \<^bold>| participationTraffic \<^bold>\<rangle> \<rfloor>" and
  ax1_2_2: "\<lfloor> \<^bold>O\<^bold>\<langle> (isAvoidable_annoyingAction(annoyingAction) \<^bold>\<rightarrow> (\<^bold>\<not>annoyingAction)) \<^bold>| participationTraffic \<^bold>\<rangle> \<rfloor>" (*If I do not split the axiom the provers fail*)
(*------------------------------------------------------------------------------------*)

theorem streetSafty: "(\<lfloor>participationTraffic\<rfloor> \<longrightarrow> \<lfloor> \<^bold>O\<^bold>\<langle>  carefulAndConsiderate  \<^bold>\<rangle>  \<rfloor>)" sledgehammer
  by (metis ax1_1 ax_5a ax_5b ax_5e)

theorem hope: "(\<lfloor>harmfulAction\<rfloor> \<longrightarrow> \<lfloor> \<^bold>O\<^bold>\<langle>  carefulAndConsiderate  \<^bold>\<rangle>  \<rfloor>)" sledgehammer
  using ax1_2_1 ax_5a by fastforce

lemma noAnnoyingActionPossible: "\<lfloor>participationTraffic \<^bold>\<and> isAvoidable_annoyingAction(annoyingAction)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<not>annoyingAction\<rfloor>"  nitpick[card=2] (*card 1 does not exist*) oops

lemma a: "\<lfloor>participationTraffic\<rfloor> \<longrightarrow> \<lfloor> \<^bold>O\<^bold>\<langle>\<^bold>\<not>harmfulAction \<^bold>\<rangle> \<rfloor>" sledgehammer
  by (metis (no_types, lifting) ax1_2_1 ax_5a ax_5b ax_5e)

lemma Ob_toNotBeAnnoying: "\<lfloor>participationTraffic \<^bold>\<and> isAvoidable_annoyingAction(annoyingAction)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>O\<^bold>\<langle>\<^bold>\<not>annoyingAction\<^bold>\<rangle>\<rfloor>" sledgehammer
  by (metis (no_types, lifting) ax1_2_2 ax_5a ax_5b ax_5e)

lemma intuition: "\<lfloor>participationTraffic\<rfloor>\<^sub>c\<^sub>w \<longrightarrow> \<lfloor>\<^bold>\<diamond> participationTraffic \<rfloor>" sledgehammer 
(*How to say: locally valid in world w and locally valid in world v?*)
  by auto


(*------------------------------- Ein- und Aussteigen --------------------------------*)
axiomatization where
  ax14_1: "\<lfloor> \<^bold>O\<^bold>\<langle> (\<^bold>\<not>harmfulAction) \<^bold>| gettingInOrOut_ofVehicle \<^bold>\<rangle> \<rfloor>" and
  ax14_2: "\<lfloor> \<^bold>O\<^bold>\<langle> measureTakenBy preventAccidentCongestion owner \<^bold>| vehicleIsLeft \<^bold>\<rangle> \<rfloor>"

(*------------------------------------------------------------------------------------*)

lemma True nitpick[satisfy] oops

end