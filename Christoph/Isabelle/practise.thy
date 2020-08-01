theory practise imports Main

begin

fun sum_upTo ::  "nat \<Rightarrow> nat" where
"sum_upTo 0 = 0" |
"sum_upTo (Suc n) = (Suc n) + (sum_upTo n)"

value "sum_upTo 5"

theorem gaussumme: "sum_upTo n = (n * (n + 1)) div 2"
  apply(induction n)
   apply(auto)
  done

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] xs = xs" |
"itrev (x # xs) ys = itrev xs (x # ys)"

lemma abc: "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
   apply (auto)
  done

lemma "itrev xs [] = rev xs" sledgehammer
  by (simp add: abc)


end