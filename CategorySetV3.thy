theory CategorySetV3 imports "ZFC_in_HOL.ZFC_Typeclasses" Category
                                                
begin

 (*Begin: some useful parameter settings*)
declare [[ smt_solver = cvc4, smt_oracle = true, smt_timeout = 120]] declare [[ show_types ]] 
sledgehammer_params [provers = cvc4 z3 spass e vampire]
nitpick_params [user_axioms, show_all, format = 2]
(*nitpick_params[user_axioms, show_all, format = 2, expect = genuine]*)
 (*End: some useful parameter settings*)

\<comment>\<open>The type of set functions\<close>
typedef setCat = "UNIV::(V\<times>V\<times>V) set"
  morphisms getFunc setFunc
  using VPi_I by blast

abbreviation funcP:: "setCat \<Rightarrow> V" where "funcP f \<equiv> fst (getFunc f)"
abbreviation domP :: "setCat \<Rightarrow> V" where "domP f \<equiv> fst (snd (getFunc f))"
abbreviation codP :: "setCat \<Rightarrow> V" where "codP f \<equiv> snd (snd (getFunc f))"

lemma "\<not> (single_valued (pairs (vinsert \<langle>0,0\<rangle> \<langle>0,1\<rangle>)))"
  apply(simp add: pairs_def single_valued_def vinsert_def)
  apply(simp add: vpair_def set_def)
  sorry

abbreviation compositionF :: "setCat \<Rightarrow> setCat \<Rightarrow> setCat" (infixl "\<^bold>\<odot>" 110)
  where "g \<^bold>\<odot> f \<equiv> setFunc (if codP f = domP g then
                  ((THE h. h \<in> elts (VPi (domP f) (\<lambda>x. codP g)) \<and>
                    (\<forall>a\<in>(elts (domP f)). \<langle>a, (app (funcP g) (app (funcP f) a))\<rangle> \<in> elts h)), 
                     domP f, codP g)
                      else (vinsert \<langle>0,0\<rangle> \<langle>0,1\<rangle>, 0, 0))"
    






end