theory Playground
imports Main
begin

datatype boolean = True | False 

fun conjuction :: "boolean \<Rightarrow> boolean \<Rightarrow> boolean" where
"conjuction True True = True" |
"conjuction _    _    = False"

fun double :: "nat \<Rightarrow> nat" where
"double x = x + x"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0       n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_02: "add m 0 = m"
apply(induction m) (* Do the induction on m, thus splitting initial goal into two subgoals *)
apply(auto)        (* Try to prove subgoals automatically - i.e. using simplification *)
done

(* NB Natural numbers and arithmetic operators are overloaded. *)

(* thm add_02: add 10 0 = 10 done *)

(* NB can omit quotes around variables, e.g. datatype 'a lst = Nil | Cons 'a "'a lst" *)
datatype 'a lst = Nil | Cons "'a" "'a lst"

fun app :: "'a lst \<Rightarrow> 'a lst \<Rightarrow> 'a lst" where
"app Nil         ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun reverse_go :: "'a lst \<Rightarrow> 'a lst \<Rightarrow> 'a lst" where
"reverse_go Nil         ys = ys" |
"reverse_go (Cons x xs) ys = reverse_go xs (Cons x ys)"
  
fun reverse :: "'a lst \<Rightarrow> 'a lst" where
"reverse xs = reverse_go xs Nil"

(* The "value" command evaluates a term *)
value "add 1 2"

value "reverse (Cons False (Cons True (Cons True Nil)))"

(* Can also work symbolically *)
value "reverse (Cons (a + 1) (Cons b Nil))"

(* Don't qualify ambiguous names when printing *)
declare [[names_short]]

end