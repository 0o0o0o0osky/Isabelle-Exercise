theory "Exercise-2"
  imports Main
begin 
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

primrec mirror::"'a tree \<Rightarrow> 'a tree"where
"mirror Tip = Tip"|
"mirror (Node l a r) = Node (mirror l) a (mirror r)"

lemma "mirror(mirror r) = r"
  apply (induction r)
   apply auto
  done

datatype 'a option = None | Some 'a

fun lookup::"('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option"where
"lookup [] x =None"|
"lookup ((a,b) # ps) x = (if a = x then Some b else lookup ps x)"

definition sq::"nat\<Rightarrow>nat" where
"sq n = n*n"

abbreviation sq'::"nat \<Rightarrow> nat"where
"sq' n \<equiv> n * n"

fun div2::"nat \<Rightarrow>nat"where
"div2 0 = 0"|
"div2 (Suc 0) = 0"|
"div2 (Suc(Suc n)) = Suc(div2 n)"
thm div2.induct
lemma "div2 n = n div 2"
  apply(induction n rule:div2.induct)
   apply auto
  done

fun contents::"'a tree \<Rightarrow> 'a list"where
"contents Tip = []"|
"contents (Node l a r) = (contents l) @ a # (contents r)"

fun treesum::"nat tree \<Rightarrow>nat"where
"treesum Tip = 0"|
"treesum (Node l a r) =( treesum l) + a +( treesum r)"

theorem "treesum t = sum_list (contents t)"
  apply(induct t )
  apply auto
  done

datatype 'a tree2 = Leaf 'a | Node "'a tree2" 'a "'a tree2"

fun mirror2::"'a tree2 \<Rightarrow> 'a tree2"where
"mirror2( Leaf a) = Leaf a"|
"mirror2 (Node l a r) = Node (mirror2 r) a (mirror2 l)"

fun pre_order::"'a tree2 \<Rightarrow> 'a list"where
"pre_order (Leaf a) = [a]"|
"pre_order (Node l a r) = [a] @ pre_order(l) @ pre_order(r)"

fun post_order::"'a tree2 \<Rightarrow> 'a list"where
"post_order (Leaf a) = [a]"|
"post_order (Node l a r) = post_order (l) @ post_order(r) @ [a]"

theorem pre_post:"pre_order (mirror2 t) = rev(post_order t)"
  apply(induction t)
   apply auto
  done

fun intersperse::"'a \<Rightarrow> 'a list \<Rightarrow> 'a list"where
"intersperse a [] = []"|
"intersperse a [x] = [x]"|
"intersperse a (x # xs)= x # a # intersperse a xs"

value "intersperse a [b,c,d,e]"
thm intersperse.induct
thm intersperse.cases
theorem map_intersperse:"map f(intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
  apply auto
  done

fun itrev::"'a list \<Rightarrow> 'a list \<Rightarrow>'a list"where
"itrev [] ys = ys"|
"itrev (x # xs) ys = itrev xs (x#ys)"

lemma itrev_rule[simp]: "itrev xs ys = rev xs @ ys"
proof(induction xs arbitrary:ys)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case by auto
qed
  

theorem "itrev xs [] = rev xs"
  apply(induction xs)
   apply(auto)
  done

primrec itadd::"nat\<Rightarrow>nat\<Rightarrow>nat"where
"itadd 0 m = m"|
"itadd (Suc m ) n = itadd m (Suc n)"
value "itadd 3 4"

text "Tail-recursive: f ...  = f ... "
primrec add::"nat\<Rightarrow>nat\<Rightarrow>nat"where
"add 0 n = n"|
"add (Suc m) n = Suc (add m n)"

lemma add_itadd[simp]:"add m (Suc n) = Suc (add m n)"
  apply (induction m)
   apply auto
  done
theorem "itadd m n = add m n"
  apply(induction m arbitrary:n)
   apply auto
  done

datatype tree0 = Leaf|Node "tree0" "tree0"

fun nodes::"tree0 \<Rightarrow>nat"where
"nodes Leaf =1"|
"nodes (Node l r) = 1 + (nodes l)+ (nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

theorem explode_count:"nodes(explode n t) = 2^n * (nodes t +1)-1 "
  apply(induction n arbitrary: t)
   apply (auto simp add:algebra_simps)
  done

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval::"exp\<Rightarrow>int\<Rightarrow>int"where
"eval Var v = v" |
"eval (Const e) v = e" |
"eval (Add e f) v = (eval e v) + (eval f v)" |
"eval (Mult e f) v = (eval e v) * (eval f v)"

fun evalp::"int list \<Rightarrow> int \<Rightarrow> int"where
"evalp [] v = 0"|
"evalp (x # xs) v = x + v*evalp xs v"

value "evalp [1,2,3] x"

fun add_coeffs::"int list \<Rightarrow> int list \<Rightarrow>int list"where
"add_coeffs [] ys = ys"|
"add_coeffs xs [] = xs"|
"add_coeffs (x#xs) (y#ys) = [x+y] @ (add_coeffs xs ys)"
value "add_coeffs [1,2,3] [4,5]"
fun mult::"int list \<Rightarrow> int \<Rightarrow>int list"where
"mult [] _ = []"|
"mult (x#xs) y = (x*y) # mult xs y" 
fun mult_coeffs::"int list \<Rightarrow> int list \<Rightarrow> int list"where
"mult_coeffs _ [] = []"|
"mult_coeffs xs (y # ys) = add_coeffs (mult xs y) (mult_coeffs (0#xs) ys)"
value "mult_coeffs [1,2,3] [4,5]"
fun coeffs :: "exp \<Rightarrow> int list"where
"coeffs Var = [0,1]"|
"coeffs (Const e) = [e]"|
"coeffs (Add e f) = add_coeffs (coeffs e) (coeffs f)"|
"coeffs (Mult e f) = mult_coeffs (coeffs e) (coeffs f)"
thm algebra_simps

lemma [simp]:"evalp (add_coeffs xs ys) x = evalp xs x + evalp ys x"
  apply(induction rule:add_coeffs.induct)
  apply (auto simp add:algebra_simps)
  done

lemma [simp]:"evalp (mult xs y) a = y * evalp xs a"
  apply(induction xs arbitrary:y)
   apply (auto simp add:algebra_simps)
  done

lemma [simp]:"evalp (mult_coeffs xs ys) a = (evalp xs a )*(evalp ys a)"
  apply (induction rule:mult_coeffs.induct)
   apply (auto simp add:algebra_simps)
  done

theorem "evalp (coeffs e) x = eval e x"
  apply (induction e)
  apply auto
  done