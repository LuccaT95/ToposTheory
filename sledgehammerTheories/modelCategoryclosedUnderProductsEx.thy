theory modelCategoryclosedUnderProductsEx imports sledgeCategoryV3

begin

(*Begin: some useful parameter settings*)
declare [[ smt_solver = cvc4, smt_oracle = true, smt_timeout = 300]] declare [[ show_types ]] 
sledgehammer_params [provers = cvc4 z3 e vampire remote_leo3, timeout = 120, isar_proofs = false]
nitpick_params [user_axioms, show_all, format = 2]
(*nitpick_params[user_axioms, show_all, format = 2, expect = genuine]*)
 (*End: some useful parameter settings*)

typedef ('a) idempotentTheory = "UNIV::('a\<times>'a\<times>'a::productCategory) set" 
  morphisms getTriplet setTriplet
by auto

abbreviation fstT::"'a idempotentTheory \<Rightarrow> 'a::productCategory" where "fstT x \<equiv> fst (getTriplet x)"
abbreviation sndT::"'a idempotentTheory \<Rightarrow> 'a::productCategory" where "sndT x \<equiv> fst (snd (getTriplet x))"
abbreviation trdT::"'a idempotentTheory \<Rightarrow> 'a::productCategory" where "trdT x \<equiv> snd (snd (getTriplet x))"

definition compT::"'a idempotentTheory \<Rightarrow>'a idempotentTheory \<Rightarrow>'a::productCategory idempotentTheory" where
  "compT \<equiv> \<lambda>x y. setTriplet (fstT y, sndT x, (trdT x) \<cdot> (trdT y))"

axiomatization where homomorphismEx: "E (setTriplet (f,g,h)) \<longleftrightarrow> f\<cdot>f \<simeq> f \<and> g\<cdot>g \<simeq> g \<and> h\<cdot>f \<simeq> g\<cdot>h" 
  for f::"'a::productCategory" and g::"'a::productCategory" and h::"'a::productCategory"

(*This is probably provable*)
axiomatization where homoCompEx: "E (compT x y) \<longleftrightarrow> (fstT x) \<simeq> (sndT y)"
  for x::"'a::productCategory idempotentTheory"

instantiation idempotentTheory :: (productCategory) productCategory
begin

lift_definition domain_idempotentTheory::"'a idempotentTheory \<Rightarrow>'a idempotentTheory" is 
  "\<lambda>x. setTriplet (fstT x, fstT x, dom (fstT x))" done

lift_definition codomain_idempotentTheory::"'a idempotentTheory \<Rightarrow>'a idempotentTheory" is 
  "\<lambda>x. setTriplet (sndT x, sndT x, dom (sndT x))" done

lift_definition composition_idempotentTheory::"'a idempotentTheory \<Rightarrow>'a idempotentTheory \<Rightarrow>'a idempotentTheory" is 
  compT done

instance
proof
  show "\<And>x::'a idempotentTheory. E (dom x) \<longrightarrow> E x" apply(transfer)
    by (smt S3 S5 UNIV_I compT_def fst_conv getTriplet_inject homoCompEx homomorphismEx prod.sel(2) prod_eq_iff setTriplet_inverse)

  show "\<And>y::'a idempotentTheory. E (cod y) \<longrightarrow> E y" apply(transfer)
    by (smt S3 S6 UNIV_I compT_def fst_conv getTriplet_inject homoCompEx homomorphismEx prod.sel(2) prod_eq_iff setTriplet_inverse)

  show "\<And>(x::'a idempotentTheory) y::'a idempotentTheory. E (x \<cdot> y) = dom x \<simeq> cod y" apply(transfer)
    by (smt UNIV_I catAx(4) catAx(5) compT_def fst_conv homoCompEx homomorphismEx setTriplet_inverse snd_conv)

  show "\<And>(x::'a idempotentTheory) (y::'a idempotentTheory) z::'a idempotentTheory. x \<cdot> (y \<cdot> z) \<cong> (x \<cdot> y) \<cdot> z" apply(transfer)
    by (smt S2 S3 S4 UNIV_I compT_def fst_conv homomorphismEx setTriplet_inverse snd_conv)

  show "\<And>x::'a idempotentTheory. x \<cdot> (dom x) \<cong> x" apply(transfer)
    by (smt S3 S5 UNIV_I compT_def fst_conv getTriplet_inverse homomorphismEx setTriplet_inverse snd_conv surjective_pairing)

  show "\<And>y::'a idempotentTheory. (cod y) \<cdot> y \<cong> y" apply(transfer)
    by (smt S3 S6 UNIV_I compT_def fst_conv getTriplet_inverse homomorphismEx setTriplet_inverse snd_conv surjective_pairing)

qed
end
                
end                                         