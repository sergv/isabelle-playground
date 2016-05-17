theory Chapter3
imports Main
begin

(* Section 3.1 *)

datatype var_name = VarName string

(*
fun abc_var :: "var_name" where
"abc_var = VarName ''abc''"
*)

datatype arith_expr =
    N int
  | V var_name
  | Plus arith_expr arith_expr

type_synonym val   = int
type_synonym state = "var_name \<Rightarrow> val"

fun arith_expr_value :: "arith_expr \<Rightarrow> state \<Rightarrow> val" where
"arith_expr_value (N n)      _ = n"   |
"arith_expr_value (V v)      s = s v" |
"arith_expr_value (Plus x y) s = arith_expr_value x s + arith_expr_value y s"

value "arith_expr_value (Plus (N 3) (V (VarName ''x''))) ((\<lambda> _. 0) (VarName ''x'' := 5))"

fun undef_state :: "state" where
"undef_state (VarName []) = 1"

value "arith_expr_value (Plus (N 3) (V (VarName ''x''))) undef_state"

(*fun mk_state :: "int \<Rightarrow> (string * int) list \<Rightarrow> state" where
"mk_state initial bindings = "
*)

fun init_state :: "state" where
"init_state _ = 0"

fun asimp_const :: "arith_expr \<Rightarrow> arith_expr" where
"asimp_const (N n) = N n" |
"asimp_const (V v) = V v" |
"asimp_const (Plus x y) =
 (case (asimp_const x, asimp_const y) of
   (N x', N y') \<Rightarrow> N (x' + y') |
   (x',   y')   \<Rightarrow> Plus x' y')"

lemma asimp_const_preserves_semantics : "arith_expr_value (asimp_const e) s = arith_expr_value e s"
apply(induction e)
apply(auto split: arith_expr.split)
done

fun plus :: "arith_expr \<Rightarrow> arith_expr \<Rightarrow> arith_expr" where
"plus (N x) (N y) = N (x + y)"                               |
"plus (N x) y     = (if x = 0 then y else Plus (N x) y)"     |
"plus x     (N y) = (if y = 0 then x else Plus x     (N y))" |
"plus x     y     = Plus x y"

lemma plus_adds : "arith_expr_value (plus e1 e2) s = arith_expr_value e1 s + arith_expr_value e2 s"
apply(induction e1 e2 rule: plus.induct)
apply(auto)
done

fun asimp :: "arith_expr \<Rightarrow> arith_expr" where
"asimp (N x)      = N x" |
"asimp (V x)      = V x" |
"asimp (Plus x y) = plus x y"

lemma "arith_expr_value (asimp e) s = arith_expr_value e s"
apply(induction e)
apply(auto simp add: plus_adds)
done

(* Exercise 3.1 *)

fun optimal :: "arith_expr \<Rightarrow> bool" where
"optimal (N _)              = True"  |
"optimal (V _)              = True"  |
"optimal (Plus (N _) (N _)) = False" |
"optimal (Plus x     y)     = (optimal x \<and> optimal y)"

theorem asimp_const_is_optimal : "optimal (asimp_const e)"
apply(induction e)
apply(auto split: arith_expr.split)
done

(* Exercise 3.2 *)

value "Some 1"
value "None"
value "fst"
value "let (x, y) = (1, 2 :: int) in x + y"

datatype arith_expr_simplified =
    Constant int
  | Term arith_expr int

fun unsimplify :: "arith_expr_simplified \<Rightarrow> arith_expr" where
"unsimplify (Constant n) = N n" |
"unsimplify (Term e n)   = Plus e (N n)" (*(if n = 0 then e else Plus e (N n))"*)

fun full_asimp_helper :: "arith_expr \<Rightarrow> arith_expr_simplified" where
"full_asimp_helper (N n)      = Constant n" |
"full_asimp_helper (V v)      = Term (V v) 0" |
"full_asimp_helper (Plus x y) =
 (case (full_asimp_helper x, full_asimp_helper y) of
   (Constant n, Constant m) \<Rightarrow> Constant (n + m) |
   (Constant n, Term e m)   \<Rightarrow> Term e (n + m)   |
   (Term e n,   Constant m) \<Rightarrow> Term e (n + m)   |
   (Term e n,   Term e' m)  \<Rightarrow> Term (Plus e e') (n + m))"

fun full_asimp :: "arith_expr \<Rightarrow> arith_expr" where
"full_asimp e = unsimplify (full_asimp_helper e)"

theorem full_asimp_preserves_semantics : "arith_expr_value (full_asimp e) s = arith_expr_value e s"
apply(induction e)
apply(auto simp add: algebra_simps split: arith_expr_simplified.split)
(* apply(auto simp add: split_def Let_def split: option.split) (* split_def is needed to expand cases over tuples *) *)
done

end
