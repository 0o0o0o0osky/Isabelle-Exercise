theory "Exercise-1"
  imports Main
begin

no_notation Nil("[]") and Cons (infixr "#" 65) and append (infixr "@" 65)
hide_type list
hide_const rev

datatype 'a list = Nil ("[]") | Cons 'a "'a list" (infixr "#" 65)

primrec app:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"(infixr "@" 65)where
"[] @ ys = ys"|
"(x # xs) @ ys = x # (xs @ ys) "

primrec rev:: "'a list \<Rightarrow> 'a list" where
"rev [] = []"|
"rev (x#xs) = (rev xs) @ (x # [])"

lemma app_Nil[simp]:"xs @ [] = xs"
  apply(induct_tac xs)
  apply(auto)
  done
lemma app_assoc[simp]:"xs @ ys @ zs = (xs @ ys ) @ zs"
  apply(induct_tac xs)
  apply(auto)
  done
lemma rev_app [simp]:"rev(xs @ ys) =(rev ys) @( rev xs)"
  apply(induct_tac xs)
  apply(auto)
  done
theorem rev_rev[simp]: "rev(rev xs) = xs"
  apply(induct_tac xs)
  apply (auto)
  done


primrec add::"nat\<Rightarrow>nat\<Rightarrow>nat"where
"add 0 n=n"|
"add (Suc m) n = Suc (add m n )" 

lemma add_02[simp]: "add a 0 = a"
  apply(induction a)
  apply (auto)
  done

lemma add_assoc:"add (add a b) c = add a (add b c)"
  apply (induction a)
  apply (auto)
  done
lemma add_03[simp]:"add 0 y = add y 0 "
  apply (induction y)
  apply (auto)
  done
lemma add_04[simp]:"Suc (add m k) = add m (Suc k)"
  apply (induction m)
   apply auto
  done
lemma add_commu:"add x y = add y x"
  apply (induction x)
   apply auto
  done

primrec double::"nat\<Rightarrow>nat"where
"double 0 = 0"|
"double (Suc m) = Suc( Suc ( double m))"

theorem double_add:"double m = add m m"
  apply (induction m )
  apply auto
  done
primrec length::"'a list \<Rightarrow> nat"where
"length [] = 0"|
"length (x#xs) = Suc(length xs)"
primrec occurs :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"occurs a [] = 0"
| "occurs a (x#xs) = (if (x=a) then Suc (occurs a xs) else occurs a xs)"


lemma "occurs a xs <= length xs"
apply (induct xs)
apply auto
  done

primrec snoc :: "'a list \<Rightarrow>'a \<Rightarrow>'a list" where
"snoc [] a = a # Nil" |
"snoc (x # xs) a = x # (snoc xs a)" 

primrec reverse::"'a list \<Rightarrow> 'a list"where
"reverse [] =[]"|
"reverse (x # xs) = snoc (reverse xs) x"
lemma [simp]:"reverse (snoc xs x) = x # reverse xs"
  apply (induction xs)
   apply auto
  done
theorem "reverse (reverse xs) = xs"
  apply (induction xs)
   apply auto
  done

primrec sum_upto::"nat\<Rightarrow>nat"where
"sum_upto 0 = 0"|
"sum_upto (Suc m) = Suc m + sum_upto m"

theorem "sum_upto n = n*(n+1) div 2"
  apply(induction n)
   apply auto
  done
end


