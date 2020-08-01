(*<*)
theory definitionCategory imports FreeLogic LaTeXsugar InverseSemigroup

begin
(*>*)

(*<*)
 (*Begin: some useful parameter settings*)
declare [[ smt_solver = cvc4, smt_oracle = true, smt_timeout = 120]] declare [[ show_types ]] 
sledgehammer_params [provers = cvc4 z3 e spass]
  nitpick_params [user_axioms, show_all, format = 2]
  (*nitpick_params[user_axioms, show_all, format = 2, expect = genuine]*)
 (*End: some useful parameter settings*) 
(*>*)
(*<*)



typedecl \<alpha> \<comment>\<open>This type can be thought of representing the morphisms of a category.\<close>

locale category = 
           \<comment>\<open>We need three functions and constant to define a category.\<close>
  fixes domain:: "\<alpha> \<Rightarrow> \<alpha>" ("dom _" [108] 109) and
        codomain:: "\<alpha> \<Rightarrow> \<alpha>" ("cod _" [110] 111) and
        composition:: "\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" (infix "\<cdot>" 110) and
        star::\<alpha> ("\<^bold>*") \<comment>\<open>Symbol for non-existing elements in terms of free logic\<close>

  assumes   
\<comment>\<open>Here we define the axioms that the morphisms 
    in interaction with the functions have to obey.\<close>

\<comment>\<open>The existence of the domain of a morphism implies the existence of the morphism.\<close>
        S1: "E(dom x) \<^bold>\<rightarrow> E x" and         
        S2: "E(cod y) \<^bold>\<rightarrow> E y" and         \<comment>\<open>The same goes for the codomain.\<close>


\<comment>\<open>As we have seen, the composition only exists if the two morphisms are composable.\<close>
\<comment>\<open>We use \<simeq> to denote the existing equality which requires that both sides 
    of the equation exist.\<close>
        S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and


        S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and     \<comment>\<open>Composition of morphisms is associative.\<close>
\<comment>\<open>We use \<cong> to denote the Kleene equality which only implies equality 
    if at least one side of the equation exists\<close>


\<comment>\<open>The domain of a morphisms serves as the right identity for composition.\<close>
        S5: "x\<cdot>(dom x) \<cong> x" and           
        S6: "(cod y)\<cdot>y \<cong> y" and   \<comment>\<open>So does the codomain as a left identity.\<close>


\<comment>\<open>Finally we make sure that there is only one non-existing morphism.\<close>
        L1: "\<^bold>\<not>(E m) \<^bold>\<rightarrow> (m = \<^bold>*)"


begin
\<comment>\<open>We show consistency.\<close>
lemma "True" nitpick[satisfy] oops

\<comment>\<open>As desired non-existing morphisms are equal.\<close>
lemma "(\<^bold>\<not>(E x) \<^bold>\<and> \<^bold>\<not>(E y)) \<^bold>\<rightarrow> (x = y \<^bold>\<and> x = \<^bold>*)"
  using L1 by blast

end

text
\<open>
We want to give a brief explanation of the symbols used. Again this will be a short treatment and
we refer to \cite{J40} and \cite{R58} for a more complete account. It is worth noting that the 
following functions were defined polymorphic in order for the free logic implementation to be used
type independent. This is why @{text "'a"} appears in the following as the type of the variables.

\begin{itemize}
\item The predicate @{text "E"} is defined as @{const_typ FreeLogic.fExistence} and tells us whether or 
not the individual passed as a parameter exists.

\item @{const ExId} is called the \emph{existing identity} and is defined as \[ @{abbrev FreeLogic.ExId}. \]
Therefore, it is only true if both elements being compared exist and are equal.

\item @{const KlEq} is called the \emph{Kleene equality} and is defined as \[ @{abbrev KlEq}. \] Therefore,
this equality does not imply the existence of the elements being compared.
\end{itemize}

Moreover, we will encounter @{text "\<^bold>\<forall>"} and @{text "\<^bold>\<exists>"} which have been
redefined to quantify only over the existing individuals. This is done by defining \[ @{abbrev fForall} \]
and \[ @{abbrev fExists}. \] Note that writing @{term "\<^bold>\<forall>x. \<Phi> x"} really means @{text "\<^bold>\<forall>\<Phi>::'a \<Rightarrow> bool"} since we
have the quantification in the definition of @{text "\<^bold>\<forall>"}. The situation is analogue for @{text "\<^bold>\<exists>"}.
\<close>

section\<open>Two axiomatizations of an inverse category\<close>

text
\<open>
Given this framework our goal now is to show that by adding to a category the axioms of an inverse semigroup that are 
responsible for shaping the inverse (definition \ref{def: inverse}, axioms 2), 3) and 4) ) we arrive at a category that is
equivalent to the definition of an inverse category.

\begin{definition}[Inverse category\footnotemark] \footcitetext{Kastl1979}
  A small category $\cat C$ is called an inverse category if for any morphism $s: X \to Y \in \cat C$
  there exists a unique morphisms $\hat{s}: Y \to X$ such that $s = s \cdot \hat{s} \cdot s$ and 
  $\hat{s} = \hat{s} \cdot s \cdot \hat{s}$.
\end{definition}

We will rewrite this in order to avoid to run into the problem with skolemization again as we did
in \ref{sec: inverseSemi}. In Isabelle/HOL we define the inverse in the @{text "locale category"} 
and then go on to define an inverse category.
\<close>


abbreviation (in category) inverseDef::"\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool" ("_ inverseOf _")
  where "t inverseOf s \<equiv> s \<cong> s\<cdot>(t\<cdot>s) \<^bold>\<and> t \<cong> t\<cdot>(s\<cdot>t)"
\<comment>\<open>On the right hand side we find the definition for the inverse.\<close>

locale inverseCategory = category +
\<comment>\<open>We introduce the new function symbol representing the inverse in the signature.\<close>
  fixes inverse::"\<alpha> \<Rightarrow> \<alpha>" ("inv _")
  assumes  uniqueInv:
\<comment>\<open>We axiomatize that every morphism has a unique inverse.\<close>
     "\<forall>s. (((inv s) inverseOf s) \<^bold>\<and> (\<forall>w. (w inverseOf s) \<^bold>\<rightarrow> w \<cong> (inv s)))"



\<comment>\<open>exNot: "$\exists x::\alpha. \neg (E x)$" was also tested as an axiom and nitpick confirmed satisfiability\<close>
begin
lemma "True" nitpick[satisfy] oops

\<comment>\<open>We prove that the existence of a morphism implies the existence of its inverse and the converse.\<close>
lemma exInv: "(E x) \<^bold>\<rightarrow> (E (inv x))"
  by (metis S1 S2 S3 uniqueInv)

lemma "E (inv x) \<^bold>\<rightarrow> (E x)"
  by (metis S1 S3 uniqueInv)

end

text
\<open>
Next we want to prove that the set of axioms used in an inverse semigroup to characterize the inverse
also hold in an inverse category.
\<close>

context inverseCategory begin

proposition Regularity: "x\<cdot>((inv x)\<cdot>x) \<cong> x"
  by (metis uniqueInv)

proposition InvInv: "((inv (inv x)) \<cong> x)" 
  by (metis uniqueInv)

proposition IdemComm: 
  "((x\<cdot>inv x)\<cdot>(y\<cdot>(inv y))) \<cong> ((y\<cdot>(inv y)) \<cdot> (x\<cdot>(inv x)))" oops

text
\<open>
The last proposition cannot be proved at this moment by automation. The case is very similar to
what we have already encountered in the proof of proposition \ref{prop: equInvToAx}. And in fact in this
section we did the proof by hand. The same proof works here in analogy once we establish
that given a morphism $x$ in an inverse category it holds that $x \cdot \hat{x}$ is idempotent.
\<close>

abbreviation (in category) Idem::"\<alpha> \<Rightarrow> bool" ("Idem _")
  where "Idem x \<equiv> (x \<cdot> x \<cong> x)"

lemma compIdem: "(Idem (x\<cdot>(inv x)))"
  by (metis S2 S3 S4 uniqueInv)
end

text
\<open>
Hence we have shown that those three inverse semigroup axioms hold in an inverse category.
Next we want to show that the converse also works and therefore we will have found a quantifier free
axiomatization of an inverse category.
\<close>


locale inverseCategoryQantFree = category +
\<comment>\<open>We introduce the new function symbol representing the inverse in the signature.\<close>
  fixes inverse::"\<alpha> \<Rightarrow> \<alpha>" ("inv _")
\<comment>\<open>We add the axioms that shape the inverse in an inverse semigroup.\<close>
  assumes C1: "x\<cdot>((inv x)\<cdot>x) \<cong> x" and
          C2: "((inv (inv x)) \<cong> x)" and
          C3: "((x\<cdot>inv x) \<cdot> (y\<cdot>(inv y))) \<cong> ((y\<cdot>(inv y)) \<cdot> (x\<cdot>(inv x)))"



begin
lemma "True" nitpick[satisfy] oops

\<comment>\<open>We show the strictness of @{text "E"} for the inverse\<close> 
lemma "(E x) \<^bold>\<leftrightarrow> (E (inv x))"
  by (metis C1 C2 S1 S2 S3)

\<comment>\<open>We need to build some theory in this context to show the result\<close>
lemma IdemComp: "Idem (x \<cdot> (inv x))" 
  by (smt S1 S3 S4 C1)

lemma (in inverseCategoryQantFree) IdempotentsCommute: 
  "((E x) \<^bold>\<and> (E y) \<^bold>\<and> (Idem x) \<^bold>\<and> (Idem y)) \<^bold>\<rightarrow> (x\<cdot>y \<cong> y\<cdot>x)"
    by (smt C3 S1 S2 S3 S4 inverseCategoryQantFree.C1 
        inverseCategoryQantFree.C2 inverseCategoryQantFree_axioms)


lemma inverseUnique: "((y inverseOf x) \<^bold>\<and> (z inverseOf x)) \<^bold>\<rightarrow> (y \<cong> z)"
  by (metis IdempotentsCommute S1 S2 S3 S4)

\<comment>\<open>The next proposition is the result we wanted to show.\<close>
proposition  inverseUnique2: 
  "\<forall>s. (((inv s) inverseOf s) \<^bold>\<and> (\<forall>w. (w inverseOf s) \<^bold>\<rightarrow> w \<cong> (inv s)))"
  by (smt C1 C2 S1 S2 S3 inverseUnique)

end

section\<open>Inverse category as a generalization of an inverse semigroup\<close>

text
\<open>
A category can be seen as a generalization of a monoid in the sense that a one object category is a
monoid. After what we have seen the inverse category seems to be a generalization of an inverse 
semigroup. We will prove now that this is indeed true.

\begin{proposition}
  Let $\cat C$ be an inverse category with exactly one object. Then $\cat C$ is an inverse semigroup.
\end{proposition}

We will try to do the proof by inclusion of locales in Isabelle/HOL. Therefore we will define an
inverse category for which we require to have exactly one object and then show that this is a 
sublocale of an inverse semigroup. Note that in this case we can assume all morphisms to exist
because the composition is total if there is just one object. We make use of the element @{text "\<^bold>*"} 
which represents the non-existing element if a non-existing element is present. Because we assume all morphisms
to exist we can use @{text "\<^bold>*"} to represent the single existing object.
Also note that as a result the quantifiers for free logic collapse to the quantifiers of classical logic
in a one-object inverse category.
\<close>

locale inverseCategoryOneObject = inverseCategoryQantFree +
  assumes only_star: "(E \<^bold>*) \<^bold>\<and> (\<forall>x. dom(x) = \<^bold>* \<^bold>\<and> cod(x) = \<^bold>*)"
begin
lemma "True"  nitpick[satisfy] oops

lemma "\<forall>x::\<alpha>. (E x)" 
  using S1 only_star by auto

lemma associative: "((x\<cdot>y)\<cdot>z) = (x\<cdot>(y\<cdot>z))" 
  using S2 S4 only_star by auto

\<comment>\<open>It is possible to have more than just one morphism. Exactly what we want.\<close>
lemma "\<forall>x::\<alpha>. x = star" nitpick oops

end

sublocale inverseCategoryOneObject \<subseteq> inverseSemigroup "inverse" "composition"
proof -
  have f1: "\<forall>a. E (a::\<alpha>)"
    by (metis S2 only_star)
  then have f2: 
      "\<forall>x. \<forall>y. ((y \<cdot> ((inv y) \<cdot> (x \<cdot> (inv x))) \<^bold>= (x \<cdot> ((inv x) \<cdot> (y \<cdot> (inv y))))))"
        using C3 associative by auto
  then show "inverseSemigroup inverse (\<cdot>)"
    using f1 by (simp add: C1 C2 associative inverseSemigroup.intro)
qed

text 
\<open>
We have succeeded to prove that an inverse category with one element is a semigroup with the
Isabelle/HOL command @{text "sledgehammer"}. It gave back a Isar proof in which we had to slightly
correct parentheses but except for that it worked out of the box.

As a result we may now try to formulate the semimodeloidal axioms in the context of inverse categories.
The outcome we want is that these axioms in a one object inverse category will form a semimodeloid.
\<close>

(*>*)
context inverseCategoryQantFree 
begin
(*
lemma "\<forall>x. E(dom x)  \<^bold>\<rightarrow> (\<^bold>\<exists>y. ((dom y) \<simeq> (cod y)))"
  by (metis S3 S5 S6)

lemma "(E x \<and> x \<cong> y)  \<^bold>\<rightarrow> E y" 
  by blast
*)
\<comment>\<open>It is to note that we do not need to specify the domain and codomain of the idempotent.\<close>
abbreviation natOrder:: "\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool" ("_ \<^bold>\<le> _" 111) where
  "(x \<^bold>\<le> y) \<equiv> (\<exists>e. (Idem e) \<and>  (x \<cong> y\<cdot>e))"
(*abbreviation atomar::"\<alpha> \<Rightarrow> bool" ("Atom _")
  where "(Atom e) \<equiv> (((E e) \<longrightarrow> (e \<noteq> zero)) \<and> (\<forall>f. ((f \<^bold>\<le> e) \<longrightarrow> ((f \<cong> e) \<or> ( f \<cong> zero)))))"

lemma "\<^bold>\<not>(E x) \<longrightarrow> (Atom x)"
  using S1 S3 by blast

lemma assumes "(E f) \<and> (E a) \<and> (E c) \<and> (c \<^bold>\<le> (f \<cdot> (a \<cdot> (inv f)))) \<and> (Idem a) \<and> (Atom a)" shows "(((inv f) \<cdot> (c \<cdot> f)) = zero) \<longrightarrow> (c inverseOf ((inv f) \<cdot> (c \<cdot> f)))" 
  by (smt IdempotentsCommute S1 S3 S4 assms inverseCategoryQantFree.C2 inverseCategoryQantFree0.axioms(2) inverseCategoryQantFree0_axioms inverseCategoryQantFree0_axioms_def inverseCategoryQantFree_axioms inverseUnique2) 

lemma assumes "(E f) \<and> (E a) \<and> (E c) \<and> (c \<^bold>\<le> (f \<cdot> (a \<cdot> (inv f)))) \<and> (Idem a) \<and> (Atom a)" shows "(((inv f) \<cdot> (c \<cdot> f)) = zero) \<longrightarrow> (c = zero)"
  by (smt IdemComp S2 S3 S4 assms inverseCategoryQantFree.IdempotentsCommute inverseCategoryQantFree0.axioms(2) inverseCategoryQantFree0_axioms inverseCategoryQantFree0_axioms_def inverseCategoryQantFree_axioms inverseUnique2)
*)

lemma Nr1: "((Idem a) \<^bold>\<and> (Idem b)) \<^bold>\<rightarrow> (a\<cdot>b = b\<cdot>a)"
  by (metis IdempotentsCommute L1 S1 S2 S3)

lemma Nr2a: "(E (t\<cdot>s)) \<^bold>\<rightarrow>  (dom(t\<cdot>s) \<simeq> dom(s))"
  by (metis S2 S3 S4 S5)

lemma Nr2b: "(E (t\<cdot>s)) \<^bold>\<rightarrow> (cod(t\<cdot>s) \<simeq> cod(t))"
  by (metis S1 S3 S4 S6)

lemma helpInvSwitch: "(s\<cdot>t)\<cdot>(((inv t) \<cdot> (inv s))\<cdot>(s\<cdot>t)) \<cong> (s\<cdot>t)"
proof -
  have "( s\<cdot> ( (t\<cdot>(inv t)) \<cdot> (((inv s)\<cdot>s)\<cdot>t))) \<cong> ((s \<cdot> (inv s)) \<cdot> s) \<cdot> ((t \<cdot> (inv t)) \<cdot> t)"
    by (smt Nr1 S1 S3 S4 inverseUnique2)
  then show ?thesis
by (smt S1 S2 S3 S4 inverseUnique2)
qed

lemma Nr3: "(inv (t\<cdot>s)) \<cong> (inv s) \<cdot> (inv t)"
  by (smt L1 helpInvSwitch inverseUnique2)

lemma Nr4a: "dom (inv (s)) \<cong> cod(s)"
  by (metis S1 S2 S3 inverseUnique2)

lemma Nr4b: "(cod (inv s)) \<cong> dom(s)"
  by (metis S1 S2 S3 inverseUnique2)

lemma Nr5: "(s \<^bold>\<le> t) \<^bold>\<rightarrow> ((inv s) \<^bold>\<le> (inv t))"
  by (metis S2 S3 S4 inverseUnique2)

lemma Nr6a: "(s \<^bold>\<le> t) \<^bold>\<rightarrow> (s \<cong> (t\<cdot>((inv s)\<cdot>s)))"
  by (smt Nr1 L1 category.S4 category_axioms inverseUnique2) 

lemma Nr6b: "(s \<^bold>\<le> t) \<^bold>\<rightarrow> (s \<cong> (s\<cdot>((inv s)\<cdot>t)))"
  by (smt C2 L1 Nr2b Nr3 Nr4b S1 S4 inverseUnique2)

lemma helpNr7: assumes "(s \<^bold>\<le> t)" shows "(t \<cdot> ((inv s) \<cdot> s)) \<cong> (s \<cdot> ((inv s) \<cdot> t))"
  by (smt Nr6a Nr6b assms)

\<comment>\<open>This proof somehow is really really hard for sledgehammer.\<close>
lemma Nr7: assumes f1: "((a \<^bold>\<le> s) \<^bold>\<and> (b \<^bold>\<le> t))" shows "((b\<cdot>a)\<^bold>\<le>(t\<cdot>s))"
proof-
  from f1 have f2: "a \<cong> s \<cdot> ((inv a) \<cdot> a)"
    using Nr6a by auto
  from f1 have f3: "b \<cong> (b \<cdot> (inv b)) \<cdot> t"
    by (smt Nr6b S4)
  have f4: "b\<cdot>a \<cong> ((b \<cdot> (inv b))\<cdot>t)\<cdot>(s \<cdot>((inv a) \<cdot> a))"
    by (metis L1 f2 f3)
  then have "(inv (b\<cdot>a)) \<cong> (inv (t\<cdot>(s\<cdot>((inv a)\<cdot>a)))) \<cdot> (b \<cdot> (inv b))"
    by (smt L1 Nr3 category.S4 category_axioms inverseUnique2)
  then have "(inv (b\<cdot>a)) \<^bold>\<le> (inv (t\<cdot>(s\<cdot>((inv a)\<cdot>a))))" 
    by (smt IdemComp)
  then have "(inv (inv (b\<cdot>a))) \<^bold>\<le> (inv (inv(t\<cdot>(s\<cdot>((inv a)\<cdot>a)))))"
    using Nr5 by auto
  then have f5: "(b\<cdot>a)  \<^bold>\<le> (t\<cdot>(s\<cdot>((inv a)\<cdot>a)))"
    by (metis C2 Nr2b S2)
  then have "\<exists>e. (Idem e) \<and> b\<cdot>a \<cong> ((t\<cdot>s)\<cdot>e)"
    by (smt C1 C2 IdemComp L1 Nr1 Nr2b Nr3 Nr4a S3 S4  category.S1 category.S2 category_axioms f2 f4 inverseUnique2)
  then show ?thesis
    by blast
qed
end

(*<*)
end
(*>*)