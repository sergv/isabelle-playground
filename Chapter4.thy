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

   They can be applied either in forward fashion *)

thm evSS[OF evSS[OF ev0]]

(* Or in backward way when prooving a lemma. E.g. *)

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

(* Exercise 4.2 *)

inductive palindrome :: "'a list \<Rightarrow> bool" where
pempty     : "palindrome []"  |
psingleton : "palindrome [x]" |
pstep      : "palindrome xs \<Longrightarrow> palindrome (x # xs @ [x])"

theorem palindrome_reverse : "palindrome xs \<Longrightarrow> rev xs = xs"
apply(induction rule: palindrome.induct)
apply(simp_all)
done

(* Exercise 4.3 *)

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl' : "star' r x x" |
step' : "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

thm "star'.induct"
thm "refl'"
thm "step'"
thm step'[OF refl']
thm step'[OF step'[OF refl']]
thm "star'.intros"

lemma star'_singleton : "r x y \<Longrightarrow> star' r x y"
(*apply(metis step' refl')*)
apply(rule step'[OF refl'])
apply(assumption)
done

lemma ext_star'_from_left : "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
apply(induction rule: star'.induct)
apply(rule star'_singleton)
apply(assumption)
apply(simp)
apply(metis step')
done

theorem star_implies_star' : "star r a b \<Longrightarrow> star' r a b"
apply(induction rule: star.induct)
apply(rule refl')
apply(simp add: step ext_star'_from_left)
done

lemma star_singleton : "r a b \<Longrightarrow> star r a b"
by(metis step refl)

lemma ext_star_from_right : "star r a b \<Longrightarrow> r b c \<Longrightarrow> star r a c"
apply(induction rule: star.induct)
apply(rule star_singleton)
apply(assumption)
apply(simp)
apply(metis step)
done

theorem star'_implies_star : "star' r a b \<Longrightarrow> star r a b"
apply(induction rule: star'.induct)
apply(rule refl)
apply(simp add: step ext_star_from_right)
done

(* Exercise 4.4 *)

value "Suc"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
irefl : "iter r 0 x x" |
istep : "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

thm "iter.induct"

theorem star_implies_iter : "star r x y \<Longrightarrow> \<exists> n. iter r n x y"
apply(induction rule: star.induct)
apply(metis irefl)
apply(metis istep)
done

(* Exercise 4.5 *)

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
emptyS     : "S []"                    |
balanceS   : "S s \<Longrightarrow> S (a # s @ [b])" |
duplicateS : "S x \<Longrightarrow> S y \<Longrightarrow> S (x @ y)"

inductive T :: "alpha list \<Rightarrow> bool" where
emptyT   : "T []" |
balanceT : "T x \<Longrightarrow> T y \<Longrightarrow> T (x @ [a] @ y @ [b])"

thm balanceT[OF emptyT]
lemmas balanceT' = balanceT[OF emptyT, simplified]

theorem T_implies_S : "T w \<Longrightarrow> S w"
apply(induction rule: T.induct)
apply(metis emptyS)
thm duplicateS[OF _ balanceS]
apply(simp)
apply(rule duplicateS[OF _ balanceS])
apply(assumption)
apply(assumption)
done

lemma balance_composite_first : "T (z @ x) \<Longrightarrow> T y \<Longrightarrow> T (z @ x @ [a] @ y @ [b])"
apply(simp)
apply(rule balanceT[of "z @ x" y, simplified])
apply(assumption)
apply(assumption)
done

lemma composite_T : "T y \<Longrightarrow> T x \<Longrightarrow> T (x @ y)"
apply(induction arbitrary: x rule: T.induct)
apply(simp)
apply(rename_tac x y z)
apply(rule balance_composite_first)
apply(auto)
done

theorem S_implies_T : "S w \<Longrightarrow> T w"
apply(induction rule: S.induct)
apply(metis emptyT)
apply(rule balanceT')
apply(assumption)
apply(rule composite_T)
apply(assumption)
apply(assumption)
done

end