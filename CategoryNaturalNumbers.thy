theory CategoryNaturalNumbers imports Category
begin

typedef natCat = "UNIV::(nat\<times>nat) set" by auto

(*(Abs_natCat ((snd (Rep_natCat b)), (fst (Rep_natCat a))))"*)

axiomatization where 
natCatEx1: "E (a::natCat) \<longleftrightarrow> fst (Rep_natCat a) \<ge> snd (Rep_natCat a)" and
natCatEx2: "\<not>(E (Abs_natCat (0::nat,1::nat)))"

lemma "True" nitpick[satisfy, card natCat = 4] oops

instantiation natCat :: category
begin

lift_definition domain_natCat::"natCat\<Rightarrow>natCat" is 
"\<lambda>x::natCat. if E x then Abs_natCat((snd (Rep_natCat x), snd (Rep_natCat x))) 
                      else (Abs_natCat (0::nat,1::nat))"
  done

lift_definition codomain_natCat::"natCat\<Rightarrow>natCat" is 
"\<lambda>x::natCat. if E x then Abs_natCat((fst (Rep_natCat x), fst (Rep_natCat x)))
                      else(Abs_natCat (0::nat,1::nat))"
  done

lift_definition composition_natCat::"natCat\<Rightarrow>natCat\<Rightarrow>natCat" is 
"\<lambda>y x. if E x \<and> E y \<and> snd (Rep_natCat y) = fst (Rep_natCat x) 
    then (Abs_natCat ((snd (Rep_natCat y)), (fst (Rep_natCat x))))
      else Abs_natCat (0,1)" 
  done

instance
proof 
  fix x y z :: natCat

  show "E x \<^bold>\<leftarrow> E (dom x)"
    apply(transfer) 
    using natCatEx2 by auto

  show "E x \<^bold>\<leftarrow> E (cod x)"
    apply(transfer)
    using natCatEx2 by auto

  show "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y"
    apply(transfer)
    by (smt Abs_natCat_inverse UNIV_I natCatEx2 prod.inject)

  show "x \<cdot> (y \<cdot> z) \<cong> (x \<cdot> y) \<cdot> z"
    apply(transfer)
    sorry


  show "x \<cdot> (dom x) \<cong> x" 
    apply(transfer)
    sorry

  show "(cod y) \<cdot> y \<cong> y"
    apply(transfer)
    sorry
qed

end
end