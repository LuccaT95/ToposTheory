theory ExponentialCategory imports Category

begin

definition (in categoryProduct) isExponential:: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("isExp")
  where "isExp a b c \<epsilon> \<equiv> \<^bold>\<exists>p1 p2. product a c (dom \<epsilon>) p1 p2 \<and> \<epsilon>:(a\<^bold>\<times>c)\<rightarrow>b \<and>
                        (\<^bold>\<forall>z f. \<^bold>\<exists>q1 q2. product z a (dom f) q1 q2 \<and> f:(z\<^bold>\<times>a)\<rightarrow>b \<and>
                          (\<^bold>\<exists>!\<ff>. \<ff>:z\<rightarrow>c \<and> (\<^bold>\<exists>!\<jj>. \<jj>:(dom f)\<rightarrow>(dom \<epsilon>) \<and> 
                            p2 \<cdot> \<jj> \<simeq> \<ff> \<cdot> q1 \<and> p1 \<cdot> \<jj> \<simeq> q2 \<and> \<epsilon> \<cdot> \<jj> \<simeq> f)))"

class exponentialCategory = categoryProduct +
  fixes  exp::"'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<^sup>_")

  assumes E1: "\<^bold>\<forall>a b. \<^bold>\<exists>\<epsilon>. isExp a b (exp a b) \<epsilon>" and
          E2: "E (a\<^sup>b) \<longrightarrow> (E a \<and> E b)"
begin

\<comment> \<open>Checking notation\<close>
lemma "\<^bold>\<forall>a b. \<^bold>\<exists>\<epsilon>. (isExp a b (a\<^sup>b) \<epsilon>)"
  using local.E1 by blast

lemma "True" nitpick[satisfy] oops

lemma "\<exists>x. final x" oops

abbreviation finalObj::'a where "finalObj \<equiv> SOME x. final x"

end

sublocale exponentialCategory \<subseteq> cartesianCategory domain codomain composition product_func finalObj sorry


proposition "E A \<and> type (A::'a::exponentialCategory) \<longrightarrow> isFunctor (\<lambda>x. (x\<^sup>A))" oops





end