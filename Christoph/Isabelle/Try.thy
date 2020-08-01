theory Try
  imports Main

begin
datatype bool = True | False

fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"conj True True = True" | 
"conj _ _ = False"

datatype nat = zero | Suc nat

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add zero n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_02[simp]: "add m zero = m"
  apply(induction m)
   apply(auto)
  done

thm add_02

lemma add_03[simp]: "Suc (add m n) = add m (Suc n)"
  apply(induction m)
   apply(auto)
  done

lemma add_com: "add m n = add n m"
  apply(induction m)
   apply(auto)
  done


fun double :: "nat \<Rightarrow> nat" where
"double zero = zero" |
"double (Suc m) = Suc (Suc (double m))" 



value "double (Suc (Suc (Suc zero)))"

theorem double_app: "double m = add m m"
  apply(induction m)
   apply(auto)
  done



datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" | 
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev (Cons True (Cons False Nil))"

(*It is important to know how to write comments!*)

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply(induction xs)
   apply(auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
   apply(auto)
  done


lemma rev_app [simp]: "rev (app xs ys) = app  (rev ys) (rev xs)"
  apply (induction xs)
   apply (auto)
  done

theorem rev_rev [simp]: "rev(rev xs) = xs"
  apply(induction xs)
   apply(auto)
  done

fun sum_upTo :: "nat \<Rightarrow> nat" where
"sum_upTo zero = zero" |
"sum_upTo (Suc n) = add (Suc n) (sum_upTo n)" 

value "sum_upTo (Suc (Suc zero))"

end