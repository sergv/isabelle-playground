theory Chapter3
imports Main HOL.Fun
begin

(** Section 3.1 Arithmetic expressions **)

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

lemma asimp_preserves_semantics : "aval (asimp e) s = aval e s"
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

(* Exercise 3.3 *)

fun subst :: "var_name \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst _ _ (N n)       = N n"                          |
"subst v x (V v')      = (if v = v' then x else V v')" |
"subst v x (Plus e e') = Plus (subst v x e) (subst v x e')"

lemma substitution_lemma : "aval (subst v x e) s = aval e (s (v := aval x s))"
apply(induction e)
apply(auto)
done

lemma substitute_equals_preserves_semantics : "aval x s = aval y s \<Longrightarrow> aval (subst v x e) s = aval (subst v y e) s"
apply(induction e)
apply(auto)
done

(* Exercise 3.5 *)

datatype aexp\<^sub>2 =
    N\<^sub>2 int
  | V\<^sub>2 var_name
  | Plus\<^sub>2 aexp\<^sub>2 aexp\<^sub>2
  | Div aexp\<^sub>2 aexp\<^sub>2
  | PostIncrement var_name

fun liftOpt :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option" where
"liftOpt _ None     _        = None" |
"liftOpt _ _        None     = None" |
"liftOpt f (Some x) (Some y) = Some (f x y)"

fun aval\<^sub>2 :: "aexp\<^sub>2 \<Rightarrow> state \<Rightarrow> val option \<times> state" where
"aval\<^sub>2 (N\<^sub>2 n)       s  = (Some n, s)"   |
"aval\<^sub>2 (V\<^sub>2 v)       s  = (Some (s v), s)" |
"aval\<^sub>2 (Plus\<^sub>2 e\<^sub>1 e\<^sub>2) s\<^sub>1 =
 (let (v\<^sub>1, s\<^sub>2) = aval\<^sub>2 e\<^sub>1 s\<^sub>1;
      (v\<^sub>2, s\<^sub>3) = aval\<^sub>2 e\<^sub>2 s\<^sub>2 in
  (liftOpt (op +) v\<^sub>1 v\<^sub>2, s\<^sub>3))" |
"aval\<^sub>2 (Div e\<^sub>1 e\<^sub>2) s\<^sub>1 =
 (let (v\<^sub>1, s\<^sub>2) = aval\<^sub>2 e\<^sub>1 s\<^sub>1;
      (v\<^sub>2, s\<^sub>3) = aval\<^sub>2 e\<^sub>2 s\<^sub>2;
      v        = if v\<^sub>2 = Some 0
                 then None
                 else liftOpt (op div) v\<^sub>1 v\<^sub>2
  in (v, s\<^sub>3))" |
"aval\<^sub>2 (PostIncrement v) s =
 (let v' = s v in
  (Some v', s (v := v' + 1)))"

value "
aval\<^sub>2
  (Plus\<^sub>2
    (PostIncrement (VarName ''x''))
    (Plus\<^sub>2
      (PostIncrement (VarName ''x''))
      (Div
        (PostIncrement (VarName ''x''))
        (N\<^sub>2 2))))
  (\<lambda> _ \<Rightarrow> 0)"

(* Exercise 3.6 *)

datatype lexp =
    Nl int
  | Vl var_name
  | Plusl lexp lexp
  | LET var_name lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> val" where
"lval (Nl n)      _ = n"                   |
"lval (Vl v)      s = s v"                 |
"lval (Plusl x y) s = lval x s + lval y s" |
"lval (LET v x y) s = lval y (s (v := lval x s))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl n)      = N n"                        |
"inline (Vl v)      = V v"                        |
"inline (Plusl x y) = Plus (inline x) (inline y)" |
"inline (LET v x y) = subst v (inline x) (inline y)"

lemma inline_preserves_semantics : "lval e s = aval (inline e) s"
apply(induction e arbitrary: s)
apply(auto)
apply(simp add: substitution_lemma)
done

(** Section 3.2 Boolean expressions **)

datatype bexp =
    Bc bool
  | Not bexp
  | And bexp bexp
  | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc x)     _ = x" |
"bval (Not e)    s = (\<not> bval e s)" |
"bval (And x y)  s = (bval x s \<and> bval y s)" |
"bval (Less x y) s = (aval x s < aval y s)"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc b)     = Bc (\<not> b)"      |
"not (Not e)    = e"             |
"not (And x y)  = Not (And x y)" |
"not (Less x y) = Not (Less x y)"

lemma not_preserves_semantics : "bval (not e) s = (\<not> bval e s)"
apply(induction e)
apply(auto)
done

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and x          (Bc True)  = x"        |
"and (Bc True)  y          = y"        |
"and _          (Bc False) = Bc False" |
"and (Bc False) _          = Bc False" |
"and x          y          = And x y"

value "False = False"
value "bval (and (Bc True) (Bc False)) undef_state"
value "bval (Bc True) undef_state \<and> bval (Bc False) undef_state"
value "bval (and (Bc True) (Bc False)) undef_state = (bval (Bc True) undef_state \<and> bval (Bc False) undef_state)"

lemma and_preserves_semantics : "bval (and e\<^sub>1 e\<^sub>2) s = (bval e\<^sub>1 s \<and> bval e\<^sub>2 s)"
apply(induction e\<^sub>1 e\<^sub>2 rule: and.induct)
apply(auto)
done

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N x) (N y) = Bc (x < y)" |
"less x     y     = Less x y"

lemma less_preserves_semantics : "bval (less e\<^sub>1 e\<^sub>2) s = (aval e\<^sub>1 s < aval e\<^sub>2 s)"
apply(induction e\<^sub>1 e\<^sub>2 rule: less.induct)
apply(auto)
done

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc x)     = Bc x"    |
"bsimp (Not e)    = not e"   |
"bsimp (And x y)  = and x y" |
"bsimp (Less x y) = less (asimp x) (asimp y)"

lemma bsimp_preserves_semantics : "bval (bsimp e) s = bval e s"
apply(induction e)
apply(auto simp add: not_preserves_semantics and_preserves_semantics)
apply(auto simp add: less_preserves_semantics asimp_preserves_semantics)
done

(* Exercise 3.7 *)

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq x y = And (Not (Less x y)) (Not (Less y x))"

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le x y = Not (Less y x)"

lemma eq_is_correct : "bval (Eq e\<^sub>1 e\<^sub>2) s = (aval e\<^sub>1 s = aval e\<^sub>2 s)"
apply(auto)
done

lemma le_is_correct : "bval (Le e\<^sub>1 e\<^sub>2) s = (aval e\<^sub>1 s \<le> aval e\<^sub>2 s)"
apply(auto)
done

end
