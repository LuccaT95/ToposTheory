theory CategorySetV2 imports Main
                                                
begin

typedecl V

abbreviation subset_eq :: "(V \<Rightarrow> bool) \<Rightarrow> (V \<Rightarrow> bool) \<Rightarrow> bool" ("(_/ \<^bold>\<subseteq> _)" [51, 51] 50) 
  where "A \<^bold>\<subseteq> B \<equiv> \<forall>x. A x \<longrightarrow> B x"

abbreviation range :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b  \<Rightarrow> bool)"
  where "range f \<equiv> \<lambda>y. \<exists>x. f x = y"

abbreviation Union :: "((V \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> (V \<Rightarrow> bool)"
  where "Union M \<equiv> \<lambda>x::V. \<exists>s. M s \<and> s x"

abbreviation image :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)"
  where "image f M \<equiv> \<lambda>y. \<exists>x. M x \<and> f x = y"

abbreviation Pow :: "(V \<Rightarrow> bool) \<Rightarrow> ((V \<Rightarrow> bool) \<Rightarrow> bool)"
  where "Pow M \<equiv> \<lambda>B. B \<^bold>\<subseteq> M"

abbreviation wf :: "(V \<Rightarrow> V \<Rightarrow> bool) \<Rightarrow> bool"
  where "wf r \<equiv> (\<forall>P. (\<forall>x. (\<forall>y. r y x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x. P x))"

axiomatization elts :: "V \<Rightarrow> (V \<Rightarrow> bool)" and getSet :: "(V \<Rightarrow> bool) \<Rightarrow> V"
  where invRel1:        "elts (getSet X) = X"  
    and invRel2:        "getSet (elts x) = x"
    and ext:            "elts x = elts y \<Longrightarrow> x=y"
    and down_raw:       "Y \<^bold>\<subseteq> elts x \<Longrightarrow> range elts Y" 
    and Union_raw:      "range elts X \<Longrightarrow> range elts (Union (image elts X))"
    and Pow_raw:        "range elts X \<Longrightarrow> range elts (image getSet (Pow X))"
    and replacement_raw:"range elts X \<Longrightarrow> range elts (image f X)"
    and inf_raw:        "range elts (range (g::nat \<Rightarrow> V))"
    and foundation:     "wf (\<lambda>x y. (elts y) x)"


end