theory Playground
imports Main
begin

(*
datatype boolean = True | False 

fun conjuction :: "boolean \<Rightarrow> boolean \<Rightarrow> boolean" where
"conjuction True True = True" |
"conjuction _    _    = False"
*)

(*
fun double :: "nat \<Rightarrow> nat" where
"double x = x + x"
*)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0       n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_0: "add m 0 = m"
apply(induction m) (* Do the induction on m, thus splitting initial goal into two subgoals *)
apply(auto)        (* Try to prove subgoals automatically - i.e. using simplification *)
done

(* NB Natural numbers and arithmetic operators are overloaded. *)

(* thm add_02: add 10 0 = 10 done *)


(* Don't qualify ambiguous names when printing, i.e. print "lst" constructors unqualified *)
declare [[names_short]]

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

fun rev' :: "'a lst \<Rightarrow> 'a lst" where
"rev' Nil         = Nil" |
"rev' (Cons x xs) = app (rev' xs) (Cons x Nil)"

(* The "value" command evaluates a term *)
value "add 1 (add 2 0)"

value "reverse (Cons False (Cons True (Cons True Nil)))"

(* Can also work symbolically *)
value "reverse (Cons (a + 1) (Cons b Nil))"

lemma app_Nil [simp] : "app xs Nil = xs"
apply(induction xs)
apply(auto)
done

lemma app_assoc [simp] : "app (app xs ys) zs = app xs (app ys zs)"
apply(induction xs)
apply(auto)
done

lemma rev'_app [simp] : "rev' (app xs ys) = app (rev' ys) (rev' xs)"
apply(induction xs)
apply(auto)
done

(* Define new theorem (can be a lemma, all the same). The [simp] annotation means that it will
   be automatically applied when using simplification to prove new theorems. *)
theorem rev'_rev' [simp] : "rev' (rev' xs) = xs"
apply(induction xs)
apply(simp)
apply(simp)
done

value "rev (rev xs)"

(* Predefined lists:
   [                 - empty list
   x # xs            - cons x onto xs
   [x1, x2, ..., xn] = x1 # x2 # ... # xn # []
   xs @ ys           - append xs and ys
   
   List library:
   length :: 'a list \<Rightarrow> nat
   map    :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list
   hd     :: 'a list \<Rightarrow> 'a
   tl     :: 'a list \<Rightarrow> 'a list
   *)

(* HOL is logic of total functions, the head function (as well as hd) has some result on
   empty list, but we don'n know what it is.
   
   Thus (head []) is underdefined rather than undefined. This means that head [] will not be
   simplified (reduced).
   *)

fun head :: "'a lst \<Rightarrow> 'a" where
"head (Cons x S) = x"

value "head Nil"

(* Exercises 2.2 *)

(* 2.1 *)

value "1 + (2 :: nat)"
value "1 + (2 :: int)"
value "1 - (2 :: nat)"
value "1 - (2 :: int)"
value "1 - 2"
value "2 + 1"

(* 2.2 *)

theorem add_associative : "add (add x y) z = add x (add y z)"
apply(induction x)
apply(auto)
done

theorem add0 [simp] : "add x 0 = x"
apply(induction x)
apply(auto)
done

theorem add_nonzero_snd [simp] : "add x (Suc y) = Suc (add x y)"
apply(induction x)
apply(auto)
done

theorem add_commutative : "add x y = add y x"
apply(induction x)
apply(auto)
done

fun double :: "nat \<Rightarrow> nat" where
"double 0        = 0" |
"double (Suc n) = Suc (Suc (double n))"

theorem double_eq_add [simp] : "double x = add x x"
apply(induction x)
apply(simp)
apply(simp)
(*apply(auto)*)
done

(* 2.3 *)

fun cond :: "bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"cond True  t _ = t" |
"cond False _ f = f"

(*
theorem cond_nonzero_left [simp] : "(x \<le> y) \<and> (cond c (Suc x) x \<le> Suc y)"
apply(induction c)
apply(auto)
done
*)

lemma cond_distribute [simp] : "cond c t f \<le> x = cond c (t \<le> x) (f \<le> x)"
apply(induction c)
apply(auto)
done

lemma cond_same_opt_branches [simp] : "cond c x x = x"
apply(induction c)
apply(auto)
done

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x []       = 0" |
"count x (y # ys) = cond (x = y) (Suc (count x ys)) (count x ys)"

value "equal 1 1 :: bool"
value "op \<le>"

theorem count_lt_length : "count x xs \<le> length xs"
apply(induction xs)
apply(auto)
done

(* 2.4 *)

fun snoc :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"snoc x []       = [x]" |
"snoc x (y # ys) = y # snoc x ys"

fun reverse' :: "'a list \<Rightarrow> 'a list" where
"reverse' []       = []" |
"reverse' (x # xs) = snoc x (reverse' xs)"

lemma reverse_snoc [simp] : "reverse' (snoc x xs) = x # reverse' xs"
apply(induction xs)
apply(auto)
done

value "reverse' (snoc x (a # xs)) = reverse' (a # snoc x xs)"
value "reverse' (a # snoc x xs) = snoc a (reverse' (snoc x xs))"
(* by IH *)
value "snoc a (reverse' (snoc x xs)) = snoc a (x # reverse' xs)"
value "snoc a (x # reverse' xs) = x # snoc a (reverse' xs)"

theorem reverse'_reverse' : "reverse' (reverse' xs) = xs"
apply(induction xs)
apply(auto)
done

(* 2.5 *)

fun sum_up_to :: "nat \<Rightarrow> nat" where
"sum_up_to 0       = 0" |
"sum_up_to (Suc n) = add (Suc n) (sum_up_to n)"

value "sum_up_to 3"

fun mul :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"mul 0       _ = 0" |
"mul (Suc n) m = add m (mul n m)"

lemma add_into_div [simp] : "add n (x div 2) = (add n (add n x)) div 2"
apply(induction n)
apply(auto)
done

lemma add_commutative2 [simp] : "add x (add y z) = add y (add x z)"
apply(induction x)
apply(auto)
done

lemma add_mul [simp] : "add n (mul n m) = mul n (Suc m)"
apply(induction n)
apply(auto)
done

theorem sum_up_to_n : "sum_up_to n = mul n (Suc n) div 2"
apply(induction n)
apply(auto)
done

(* 2.3 Type and Function Definitions *)

type_synonym string = "char  list"

datatype ('a, 'b) three =
    One "'a"
  | Two "'b"
  | Three

(* case expressions are supported *)

fun three_to_nat :: "('a, 'b) three \<Rightarrow> nat" where
"three_to_nat x = (case x of
    One _ \<Rightarrow> 1
  | Two _ \<Rightarrow> 2
  | Three \<Rightarrow> 3
  )"

datatype 'a option = None | Some 'a

(* NB Tuples are simulated by pairs nested to the right.
      I.e. (a * b * c) is a shorthand for (a * (b * c))
 *)

fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup []             _  = None" |
"lookup ((k, v) # kvs) k' = (if k = k' then Some v else lookup kvs k')"

value "lookup [(1, 2), (2, 3)] (2 :: nat) :: nat option"

(* Definitions are non-recursive functions that are not allowed to pattern-match *)

definition sq :: "nat \<Rightarrow> nat" where
"sq x = x + x"

(* Can also define abbreviations, which are similar to definitions but are expanded upon parsing
   and folded back on prettyprinting.
 *)

(* NB to enter \<equiv> either leave == in ascii, enter == and complete or enter \<equiv> and complete *)

abbreviation sq' :: "nat \<Rightarrow> nat" where
"sq' x \<equiv> x * x"

(* Recursive functions are defined with fun keyword. They must be total and must always
   terminate.

   Every function defines it's own customized induction rule, e.g.
 *)

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0             = 0" |
"div2 (Suc 0)       = 0" |
"div2 (Suc (Suc n)) = Suc (div2 n)"

lemma div2_is_div : "div2 n = n div 2"
(* apply customized induction rule *)
apply(induction n rule: div2.induct)
apply(auto)
done

(* Customized induction rule is more convenient for proving properties of non-trivial functions,
   where there's more than one equation for each constructor of input
 *)

(* If function takes several arguments then induction rule is applied like this:
   apply(induction x1, x2, ..., xN rule: f.induct
  *)

(* Exercises 2.3 *)

(* 2.6 *)

datatype 'a tree =
    Leaf
  | Branch "'a" "'a tree" "'a tree"

value "listsum [1, 2, 3] :: int"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Leaf = []" |
"contents (Branch x left right) = contents left @ x # contents right"

fun treesum :: "nat tree \<Rightarrow> nat" where
"treesum Leaf = 0" |
"treesum (Branch x left right) = treesum left + treesum right + x"

theorem treesum_is_listsum : "treesum t = listsum (contents t)"
apply(induction t)
apply(auto)
done

(* Try to find out which theorems about addition were used to prove treesum_is_listsum *)
(*
fun my_add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"my_add 0       m = m" |
"my_add (Suc n) m = Suc (my_add n m)"

fun my_listsum :: "nat list \<Rightarrow> nat" where
"my_listsum []       = 0" |
"my_listsum (x # xs) = my_add x (my_listsum xs)"

fun my_treesum :: "nat tree \<Rightarrow> nat" where
"my_treesum Leaf = 0" |
"my_treesum (Branch x left right) = my_add x (my_add (my_treesum left) (my_treesum right))"

lemma my_listsum_distributes_over_append [simp] : "my_listsum (xs @ ys) = my_add (my_listsum xs) (my_listsum ys)"
apply(induction xs)
apply(auto)
apply(induction ys)
apply(auto)
done

theorem my_treesum_is_my_listsum : "my_treesum t = my_listsum (contents t)"
apply(induction t)
apply(auto)
done

*)

(* 2.7 *)

datatype 'a tree2 =
    Leaf 'a
  | Branch 'a "'a tree2" "'a tree2"

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror2 (Leaf x)              = Leaf x" |
"mirror2 (Branch x left right) = Branch x (mirror2 right) (mirror2 left)"

(* NB Function is an involution if it is its own inverse, i.e. it cancels itself *)
lemma mirror2_is_involution : "mirror2 (mirror2 t) = t"
apply(induction t)
apply(auto)
done

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leaf x)              = [x]" |
"pre_order (Branch x left right) = x # pre_order left @ pre_order right"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Leaf x)              = [x]" |
"post_order (Branch x left right) = post_order left @ post_order right @ [x]"

value "rev [1, 2, 3] :: int list"

theorem pre_post_order : "pre_order (mirror2 t) = rev (post_order t)"
apply(induction t)
apply(auto)
done

(* 2.8 *)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse x []       = []" |
"intersperse x (y # ys) = y # concat (map (\<lambda> z. [x, z]) ys)"

lemma map_over_concat [simp] : "map f (concat xs) = concat (map (map f) xs)"
apply(induction xs)
apply(auto)
done

lemma map_f_comp_list_valued_lambda [simp] : "map f \<circ> (\<lambda>y. [x, y]) = (\<lambda>y. [f x, y]) \<circ> f"
apply(auto)
done

theorem intersperse_distributes_over_map : "map f (intersperse x xs) = intersperse (f x) (map f xs)"
apply(induction xs)
apply(auto)
done

end