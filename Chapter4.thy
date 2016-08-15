theory Chapter4
imports Main
begin

(* Chapter 4 Logic and Proof Beyond Equality *)

(* Formulas are terms of type bool.

   The impliation \<Longrightarrow> is part of the Isabelle framework and should be used to structure theorems and
   proofs.

   There's also a formula for implication: \<longrightarrow>. It's part of HOL.

   Both \<Longrightarrow> and \<longrightarrow> are logically equivalent, but \<Longrightarrow> should be preferred in proofs because of its
   special treatment by Isabelle. Theorems must be of the form \<lbrakk> A\<^sub>1; A\<^sub>2; ...; A\<^sub>n \<rbrakk> \<Rightarrow> A rather
   than A\<^sub>1 \<and> A\<^sub>2 \<and> ... \<and> A\<^sub>n \<longrightarrow> A.
*)

(* Exercise 4.1 *)

datatype 'a tree =
    Tip
  | Node "'a" "'a tree" "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip                 = {}" |
"set (Node x left right) = {x} \<union> set left \<union> set right"

datatype 'a bounds = Bounds 'a 'a 'a

fun element :: "'a bounds \<Rightarrow> 'a" where
"element (Bounds x _ _) = x"

fun lower_bound :: "'a bounds \<Rightarrow> 'a" where
"lower_bound (Bounds _ y _) = y"

fun upper_bound :: "'a bounds \<Rightarrow> 'a" where
"upper_bound (Bounds _ _ z) = z"

fun tree_lower_bound :: "'a \<Rightarrow> ('a bounds) tree \<Rightarrow> 'a" where
"tree_lower_bound x Tip          = x" |
"tree_lower_bound _ (Node b _ _) = lower_bound b"

fun tree_upper_bound :: "'a \<Rightarrow> ('a bounds) tree \<Rightarrow> 'a" where
"tree_upper_bound x Tip          = x" |
"tree_upper_bound _ (Node b _ _) = upper_bound b"

fun annotate_with_bounds :: "'a tree \<Rightarrow> ('a bounds) tree" where
"annotate_with_bounds Tip                 = Tip" |
"annotate_with_bounds (Node x left right) =
 (let left'  = annotate_with_bounds left;
      right' = annotate_with_bounds right
  in  Node (Bounds x (tree_lower_bound x left') (tree_upper_bound x right')) left' right')"

fun is_ordered :: "(int bounds) tree \<Rightarrow> bool" where
"is_ordered Tip = True" |
"is_ordered (Node b left right) =
 (let elem = element b in
  is_ordered left \<and>
  is_ordered right \<and>
  elem \<ge> tree_upper_bound elem left \<and>
  elem \<le> tree_lower_bound elem right)"

fun ord :: "int tree \<Rightarrow> bool" where
"ord t = is_ordered (annotate_with_bounds t)"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip                 = Node x Tip Tip" |
"ins x (Node y left right) =
 (if x < y
  then Node y (ins x left) right
  else if x = y
  then Node y left right
  else Node y left (ins x right))"

theorem ins_adds_element : "set (ins x t) = {x} \<union> set t"
apply(induction t)
apply(auto)
done

lemma ins_maintains_lower_bound :
  "tree_lower_bound d (annotate_with_bounds t) \<ge> y \<Longrightarrow>
   x \<ge> y \<Longrightarrow>
   d \<ge> y \<Longrightarrow>
   tree_lower_bound d (annotate_with_bounds (ins x t)) \<ge> y"
apply(induction t arbitrary: d)
apply(simp_all)
apply(auto simp add: Let_def)
done

lemma ins_maintains_upper_bound :
  "tree_upper_bound d (annotate_with_bounds t) \<le> y \<Longrightarrow>
   x \<le> y \<Longrightarrow>
   d \<le> y \<Longrightarrow>
   tree_upper_bound d (annotate_with_bounds (ins x t)) \<le> y"
apply(induction t arbitrary: d)
apply(simp_all)
apply(auto simp add: Let_def)
done

theorem ins_preserves_ordering : "ord t \<Longrightarrow> ord (ins x t)"
apply(induction t)
apply(auto simp add: Let_def ins_maintains_lower_bound ins_maintains_upper_bound)
done

(* 4.5 Inductive definitions *)

inductive ev :: "nat \<Rightarrow> bool" where
ev0  : "ev 0" |
evSS : "ev n \<Longrightarrow> ev (Suc (Suc n))"

thm "evSS"

(* Inductive ev created two new "lemmas", ev0 and evSS, which can be used in proofs.

   They can be applied either in forward fashion

   evSS[OF evSS[OF ev0]]

   or in backward way when prooving a lemma. E.g.
   *)

lemma "ev (Suc (Suc (Suc (Suc 0))))"
apply(rule evSS)
apply(rule evSS)
apply(rule ev0)
done

(* The "for r" part is merely a hint to Isabelle that r is a fixed parameter of star.
   This hint allows to generate simpler induction rule.
   *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl : "star r x x" |
step : "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

thm "star.induct"

lemma star_trans : "star r a b \<Longrightarrow> star r b c \<Longrightarrow> star r a c"
apply(induction rule: star.induct)
apply(assumption) (* Prove first case "star r x c \<Longrightarrow> star r x c" *)
apply(metis step)
done

end
