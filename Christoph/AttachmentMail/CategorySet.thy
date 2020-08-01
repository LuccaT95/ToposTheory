theory CategorySet imports "ZFC_in_HOL.ZFC_Typeclasses" Category

begin

 (*Begin: some useful parameter settings*)
declare [[ smt_solver = cvc4, smt_oracle = true, smt_timeout = 120]] declare [[ show_types ]] 
sledgehammer_params [provers = cvc4 z3 spass e vampire]
nitpick_params [user_axioms, show_all, format = 2]
(*nitpick_params[user_axioms, show_all, format = 2, expect = genuine]*)
 (*End: some useful parameter settings*)

text\<open>Lets try to build the category of sets!\<close>

section\<open>Prerequisites\<close>

declare[[coercion_enabled]]

\<comment>\<open>The type of set functions\<close>
typedef setFunc = "{(f, A, B). f \<in> elts (VPi A (\<lambda>x. B))}"
  using VPi_I by blast

type_synonym funcRaw = "setFunc option"
typedef setCat = "UNIV::funcRaw set" by auto

setup_lifting type_definition_setFunc

lift_definition ffst::"setFunc \<Rightarrow> V" is fst
  done

lift_definition Psnd::"setFunc \<Rightarrow> V \<times> V" is snd
  done

definition fdom_r::"setFunc \<Rightarrow> V" 
   where "fdom_r m \<equiv> fst(Psnd(m))"

definition fcod_r::"setFunc \<Rightarrow> V"
  where "fcod_r m \<equiv> snd(Psnd(m))"

declare [[coercion Abs_setFunc]]

\<comment> \<open>Raw definition of composition\<close>
definition PComp::"setFunc \<Rightarrow> setFunc \<Rightarrow> setFunc" (infixl "\<^bold>\<odot>" 75)
  where "g \<^bold>\<odot> f \<equiv> ((THE h. h \<in> elts (VPi (fdom_r f) (\<lambda>x. fcod_r g)) \<and>
                    (\<forall>a\<in>(elts (fdom_r f)). \<langle>a, (app (ffst g) (app (ffst f) a))\<rangle> \<in> elts h)), 
                     fdom_r f, fcod_r g)"

section\<open>Setting up definitions for dom, cod and comp\<close>

declare [[coercion Abs_setCat]]

definition fdom::"setCat \<Rightarrow> setCat"
  where "fdom m \<equiv> case Rep_setCat m of None \<Rightarrow> None | 
          Some y \<Rightarrow> Some (Abs_setFunc ((VLambda (fdom_r y) (\<lambda>x::V. x)) , (fdom_r y), (fdom_r y)))"

definition fcod::"setCat \<Rightarrow> setCat"
  where "fcod m \<equiv> case Rep_setCat m of None \<Rightarrow> None | 
          Some y \<Rightarrow> Some (Abs_setFunc ((VLambda (fcod_r y) (\<lambda>x::V. x)) , (fcod_r y), (fcod_r y)))"

\<comment> \<open>Refined function composition\<close>
definition fComp::"setCat \<Rightarrow> setCat \<Rightarrow> setCat" (infixl "\<odot>" 75)
  where "g \<odot> f \<equiv> case Rep_setCat g of None \<Rightarrow> None
                  | Some y \<Rightarrow> (case Rep_setCat f of None \<Rightarrow> None
                                      | Some z \<Rightarrow> if (fdom_r y = fcod_r z)  then Some (y \<^bold>\<odot> z) else None)"


section\<open>Axiomatization of existence in free logic\<close>

axiomatization where 
SetCatEx: "E (f::setCat) \<longleftrightarrow> \<not>(Rep_setCat f = None)"

lemma NoneNotEx: "\<not>(E ((Abs_setCat None)::setCat))"
  by (simp add: Abs_setCat_inverse SetCatEx)


lemma DomExHelp: assumes "E x" shows "\<exists>y. fdom x = Abs_setCat (Some y)"
proof -
  obtain y where 1:"fdom x = Abs_setCat (Some y)"
    using SetCatEx assms fdom_def by auto
  show ?thesis using 1 by auto
qed

lemma CodExHelp: assumes "E x" shows "\<exists>y. fcod x = Abs_setCat (Some y)"
proof -
  obtain y where 1: "fcod x = Abs_setCat(Some y)"
    using SetCatEx assms fcod_def by auto
  show ?thesis using 1 by auto
qed

section\<open>setCat defines a category - the category of sets\<close>

instantiation setCat :: category
begin

lift_definition domain_setCat::"setCat\<Rightarrow>setCat" is fdom done
lift_definition codomain_setCat::"setCat\<Rightarrow>setCat" is fcod done
lift_definition composition_setCat::"setCat\<Rightarrow>setCat\<Rightarrow>setCat" is fComp done

instance
proof 
  show S1: "\<And>x::setCat. E (dom x) \<longrightarrow> E x"
    apply(rule contraposition)
  proof
    fix x::setCat
    assume "\<not> (E x)"
    then have "Rep_setCat x = None"
      using SetCatEx by blast
    hence "dom x = Abs_setCat None"
    using domain_setCat.transfer fdom_def by auto
    thus "\<not> (E (dom x))"
      by (simp add: NoneNotEx)
  qed

  show S2: "\<And>x::setCat. E (cod x) \<longrightarrow> E x"
  apply(rule contraposition)
  proof
    fix x::setCat
    assume "\<not> (E x)"
    then have "Rep_setCat x = None"
      using SetCatEx by blast
    hence "cod x = Abs_setCat None"
    using codomain_setCat.transfer fcod_def by auto
    thus "\<not> (E (cod x))"
      by (simp add: NoneNotEx)
  qed

  show "\<And>(x::setCat) y::setCat. E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y"
    apply(transfer, rule equE)
  proof -
    fix x y :: setCat
      assume "E (x \<odot> y)"
      thus "fdom x \<simeq> fcod y" 
        by (smt Abs_setCat_inverse CategorySet.fComp_def SetCatEx UNIV_I fcod_def fdom_def option.case_eq_if option.discI)
    next
    fix x y :: setCat
      assume 1:"fdom x \<simeq> fcod y" 
      then have 2:"E x \<and> E y"
        by (metis(mono_tags) codomain_setCat.abs_eq domain_setCat.transfer local.S1 local.S2)
      from 1 show "E (x \<odot> y)" unfolding fComp_def 
        apply (split option.splits)  
        apply (split option.splits)
        apply (auto) 
        using "2" SetCatEx apply blast
        using "2" SetCatEx apply blast
         apply (simp add: Abs_setCat_inverse SetCatEx)
      proof - 
        fix u w :: setFunc
        assume 1: "E (fcod y)" and
         2: "fdom x \<^bold>= fcod y" and 
         3: "fdom_r u \<noteq> fcod_r w" and
         4: "Rep_setCat y \<^bold>= Some w" and
         5: "Rep_setCat x \<^bold>= Some u"

        from 2 4 5 have 8: "fdom (Some u) = fcod (Some w)"
          by (metis Rep_setCat_inverse)

        have 6: "fcod (Some w) = 
                    Some (Abs_setFunc((VLambda (fcod_r w) (\<lambda>x::V. x)) , (fcod_r w), (fcod_r w)))"         
          by (simp add: Abs_setCat_inverse fcod_def)

        have 7: "fdom (Some u) = Some (Abs_setFunc((VLambda (fdom_r u) (\<lambda>x::V. x)) , (fdom_r u), (fdom_r u)))"
          by (simp add: Abs_setCat_inverse fdom_def)

        from 6 7 8 Abs_setFunc_inverse  have "((VLambda (fcod_r w) (\<lambda>x::V. x)) , (fcod_r w), (fcod_r w)) = 
                        ((VLambda (fdom_r u) (\<lambda>x::V. x)) , (fdom_r u), (fdom_r u))"
          by (metis Abs_setCat_inverse UNIV_I VPi_I mem_Collect_eq option.sel prod.simps(2))
        then have "(fcod_r w) = (fdom_r u)" using VLambda_def
          by blast
        with 3 have "False" by auto
        thus "E (Abs_setCat None)" by simp
      qed
  qed



  show "\<And>(x::setCat) (y::setCat) z::setCat. x \<cdot> (y \<cdot> z) \<cong> (x \<cdot> y) \<cdot> z"
    apply(transfer)
    sorry


  show "\<And>x::setCat. x \<cdot> (dom x) \<cong> x"
    apply(transfer) unfolding fdom_def fComp_def
    apply(split option.split, split option.split, split option.split, split option.split)
    apply(auto) 
    using NoneNotEx apply blast 
    using SetCatEx apply blast 
    using NoneNotEx apply blast
    apply (simp add: Abs_setCat_inverse) 
       defer
       defer
    using NoneNotEx apply blast
    sorry

  show "\<And>y::setCat. (cod y) \<cdot> y \<cong> y"
    apply(transfer)
    sorry
qed

end








end