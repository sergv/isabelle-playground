theory Chapter3
imports Main HOL.Fun
begin

(* Section 3.1 *)

datatype var_name = VarName string

(*
fun abc_var :: "var_name" where
"abc_var = VarName ''abc''"
*)

datatype aexp =
    N int
  | V var_name
  | Plus aexp aexp

type_synonym val   = int
type_synonym state = "var_name \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n)      _ = n"   |
"aval (V v)      s = s v" |
"aval (Plus x y) s = aval x s + aval y s"

value "aval (Plus (N 3) (V (VarName ''x''))) ((\<lambda> _. 0) (VarName ''x'' := 5))"

fun undef_state :: "state" where
"undef_state (VarName []) = 1"

value "aval (Plus (N 3) (V (VarName ''x''))) undef_state"

(*fun mk_state :: "int \<Rightarrow> (string * int) list \<Rightarrow> state" where
"mk_state initial bindings = "
*)

fun init_state :: "state" where
"init_state _ = 0"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V v) = V v" |
"asimp_const (Plus x y) =
 (case (asimp_const x, asimp_const y) of
   (N x', N y') \<Rightarrow> N (x' + y') |
   (x',   y')   \<Rightarrow> Plus x' y')"

lemma asimp_const_preserves_semantics : "aval (asimp_const e) s = aval e s"
apply(induction e)
apply(auto split: aexp.split)
done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N x) (N y) = N (x + y)"                               |
"plus (N x) y     = (if x = 0 then y else Plus (N x) y)"     |
"plus x     (N y) = (if y = 0 then x else Plus x     (N y))" |
"plus x     y     = Plus x y"

lemma plus_adds : "aval (plus e1 e2) s = aval e1 s + aval e2 s"
apply(induction e1 e2 rule: plus.induct)
apply(auto)
done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N x)      = N x" |
"asimp (V x)      = V x" |
"asimp (Plus x y) = plus x y"

lemma "aval (asimp e) s = aval e s"
apply(induction e)
apply(auto simp add: plus_adds)
done

(* Exercise 3.1 *)

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N _)              = True"  |
"optimal (V _)              = True"  |
"optimal (Plus (N _) (N _)) = False" |
"optimal (Plus x     y)     = (optimal x \<and> optimal y)"

theorem "optimal (asimp_const e)"
apply(induction e)
apply(auto split: aexp.split)
done

(* Exercise 3.2 *)

value "Some 1"
value "None"
value "fst"
value "let (x, y) = (1, 2 :: int) in x + y"

datatype aexp_simplified =
    Constant int
  | VanillaTerm aexp
  (* Term plus some constant *)
  | Term aexp int (* integer is always nonzero *) 

fun unsimplify :: "aexp_simplified \<Rightarrow> aexp" where
"unsimplify (Constant n)    = N n" |
"unsimplify (VanillaTerm e) = e"   |
"unsimplify (Term e n)      = Plus e (N n)"

fun addConstant :: "int \<Rightarrow> aexp_simplified \<Rightarrow> aexp_simplified" where
"addConstant n e =
 (if n = 0
  then e
  else case e of
    Constant m    \<Rightarrow> Constant (n + m) |
    VanillaTerm e \<Rightarrow> Term e n         |
    Term e m      \<Rightarrow> Term e (n + m)
  )"
(*
  "addConstant n (Constant m)    = Constant (n + m)"                            |
"addConstant n (VanillaTerm e) = (if n = 0 then VanillaTerm e else Term e n)" |
"addConstant n (Term e m)      = Term e (n + m)"
*)

fun full_asimp_helper :: "aexp \<Rightarrow> aexp_simplified" where
"full_asimp_helper (N n)      = Constant n"        |
"full_asimp_helper (V v)      = VanillaTerm (V v)" |
"full_asimp_helper (Plus x y) =
 (case (full_asimp_helper x, full_asimp_helper y) of
   (Constant n,    e)              \<Rightarrow> addConstant n e         |
   (e,             Constant m)     \<Rightarrow> addConstant m e         |
   (VanillaTerm e, VanillaTerm e') \<Rightarrow> VanillaTerm (Plus e e') |
   (VanillaTerm e, Term e' m)      \<Rightarrow> Term (Plus e e') m      |
   (Term e n,      VanillaTerm e') \<Rightarrow> Term (Plus e e') n      |
   (Term e n,      Term e' m)      \<Rightarrow> Term (Plus e e') (n + m))"
   
fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp x = (unsimplify \<circ> full_asimp_helper) x" (* Enter composition via \circ *)

lemma addConstant_preserves_semantics : 
  "aval (unsimplify (addConstant n e)) s = n + aval (unsimplify e) s"
apply(induction e)
apply(auto split: aexp_simplified.split)
done

theorem full_asimp_preserves_semantics : "aval (full_asimp e) s = aval e s"
apply(induction e)
apply(auto split: aexp_simplified.split simp add: addConstant_preserves_semantics)
(* apply(auto simp add: split_def Let_def split: option.split) (* split_def is needed to expand cases over tuples *) *)
done

end
