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

lemma "div2 n = n div 2"
  apply(induction n rule: div2.induct)
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

theorem map_intersperse:"map f(intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
  apply auto
  done

fun itrev::"'a list \<Rightarrow> 'a list \<Rightarrow>'a list"where
"itrev [] ys = ys"|
"itrev (x # xs) ys = itrev xs (x#ys)"

lemma "itrev xs ys = rev xs @ ys"
  apply(induction xs)
  apply auto
  done
theorem "itrev xs [] = rev xs"
  apply(induction xs)
  apply(auto)
  done
