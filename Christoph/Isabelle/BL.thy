theory BL imports Main

begin

typedecl a

type_synonym i = "(a\<Rightarrow>bool)"

consts impl:: "i \<Rightarrow> i => i" (infixr "\<^bold>\<rightarrow>" 49)
consts con:: "i \<Rightarrow> i \<Rightarrow> i" (infixr "\<^bold>&" 50)

axiomatization where
  A1: "((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> ((\<psi> \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>)))(x)" and
  A2: "((\<phi> \<^bold>& \<psi>) \<^bold>\<rightarrow> \<phi>)(x)" and
  A3: "((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>))(x)" and
  A4: "((\<phi> \<^bold>& (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<psi> \<^bold>& (\<psi> \<^bold>\<rightarrow> \<phi>))))(x)" and
  A5a: "((\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>& \<psi>) \<^bold>\<rightarrow> \<chi>))(x)" and
  A5b: "(((\<phi> \<^bold>& \<psi>) \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)))(x)" and
  A6: "(((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> (((\<psi> \<^bold>\<rightarrow> \<phi>) \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> \<chi>))(x)" and
  A7: "False \<Longrightarrow> \<phi>(x::a)"

 axiomatization where
  ModusPonens: "(\<phi> \<^bold>\<rightarrow> \<psi>)(x) \<Longrightarrow> \<phi>(x) \<Longrightarrow>  \<psi>(x)"

lemma True nitpick[satisfy, user_axioms] oops

lemma "(\<phi> \<^bold>\<rightarrow> \<phi>)(x)" sledgehammer
  by (meson A2 A3 A5b ModusPonens)

lemma "(\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>))(x)" sledgehammer
  using A2 A5b ModusPonens by blast

end