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

(* Exercise 3.8 *)

datatype ifexp =
    Bc2 bool
  | If ifexp ifexp ifexp
  | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 b)     _ = b"                                            |
"ifval (If c t f)  s = (if ifval c s then ifval t s else ifval f s)" |
"ifval (Less2 x y) s = (aval x s < aval y s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc b)     = Bc2 b"                                  |
"b2ifexp (Not x)    = If (b2ifexp x) (Bc2 False) (Bc2 True)"  |
"b2ifexp (And x y)  = If (b2ifexp x) (b2ifexp y) (Bc2 False)" |
"b2ifexp (Less x y) = Less2 x y"

lemma b2ifexp_preserves_semantics : "ifval (b2ifexp e) s = bval e s"
apply(induction e)
apply(auto)
done

fun or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"or x y = Not (And (Not x) (Not y))"

lemma or_is_correct : "bval (or e\<^sub>1 e\<^sub>2) s = (bval e\<^sub>1 s \<or> bval e\<^sub>2 s)"
apply(auto)
done

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 b)     = Bc b"                                                                 |
"if2bexp (If c t f)  = or (And (if2bexp c) (if2bexp t)) (And (Not (if2bexp c)) (if2bexp f))" |
"if2bexp (Less2 x y) = Less x y"

lemma if2bexp_preserves_semantics : "bval (if2bexp e) s = ifval e s"
apply(induction e)
apply(auto)
done 

(* Exercise 3.9 *)

datatype pbexp =
    VAR var_name
  | NOT pbexp
  | AND pbexp pbexp
  | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (var_name \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR v)    s = s v"                       |
"pbval (NOT e)    s = (\<not> pbval e s)"             |
"pbval (AND e\<^sub>1 e\<^sub>2) s = (pbval e\<^sub>1 s \<and> pbval e\<^sub>2 s)" |
"pbval (OR e\<^sub>1 e\<^sub>2)  s = (pbval e\<^sub>1 s \<or> pbval e\<^sub>2 s)"

(* Is argument expression in Negation Normal Form - i.e. NOT is only applied to variables *)
fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR _)       = True"                  |
"is_nnf (NOT (VAR _)) = True"                  |
"is_nnf (NOT _)       = False"                 |
"is_nnf (AND x y)     = (is_nnf x \<and> is_nnf y)" |
"is_nnf (OR x y)      = (is_nnf x \<or> is_nnf y)"

(* Convert expression to NNF *)
fun nnf_go :: "bool \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"nnf_go negate (VAR v)   = (if negate then NOT (VAR v) else VAR v)"  |
"nnf_go negate (NOT x)   = nnf_go (\<not> negate) x"                      |
"nnf_go False  (AND x y) = AND (nnf_go False x) (nnf_go False y)"     |
"nnf_go False  (OR x y)  = OR  (nnf_go False x) (nnf_go False y)"     |
"nnf_go True   (AND x y) = OR  (nnf_go True x)  (nnf_go True y)"      |
"nnf_go True   (OR x y)  = AND (nnf_go True x)  (nnf_go True y)"

lemma nnf_go_preserves_semantics : "pbval (nnf_go b e) s = (if b then \<not> pbval e s else pbval e s)"
apply(induction b e rule: nnf_go.induct)
apply(simp_all)
done

lemma nnf_go_is_correct : "is_nnf (nnf_go b e)"
apply(induction b e rule: nnf_go.induct)
apply(auto)
done


definition nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf x = nnf_go False x"

theorem nnf_preserves_semantics : "pbval (nnf e) s = pbval e s"
apply(simp add: nnf_def nnf_go_preserves_semantics)
done

theorem nnf_is_correct : "is_nnf (nnf e)"
apply(induction e)
apply(auto simp add: nnf_def nnf_go_is_correct)
done

fun is_conjunct :: "pbexp \<Rightarrow> bool" where
"is_conjunct (VAR _)   = True"                            |
"is_conjunct (NOT _)   = True"                            |
"is_conjunct (AND x y) = (is_conjunct x \<and> is_conjunct y)" |
"is_conjunct (OR x y)  = False"

fun is_disj_of_conj :: "pbexp \<Rightarrow> bool" where
"is_disj_of_conj (VAR _)   = True"                            |
"is_disj_of_conj (NOT _)   = True"                            |
"is_disj_of_conj (AND x y) = (is_conjunct x \<and> is_conjunct y)" |
"is_disj_of_conj (OR x y)  = (is_disj_of_conj x \<and> is_disj_of_conj y)"

definition is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf e = (is_nnf e \<and> is_disj_of_conj e)"

fun mk_dnf_conj :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
(*"mk_dnf_conj (OR x\<^sub>1 y\<^sub>1) (OR x\<^sub>2 y\<^sub>2) =
  OR (mk_dnf_conj x\<^sub>1 y\<^sub>1)
     (OR (mk_dnf_conj x\<^sub>1 y\<^sub>2)
         (OR (mk_dnf_conj x\<^sub>2 y\<^sub>1)
             (mk_dnf_conj x\<^sub>2 y\<^sub>2)))" | *)
"mk_dnf_conj e         (OR y\<^sub>1 y\<^sub>2) = OR (mk_dnf_conj e y\<^sub>1) (mk_dnf_conj e y\<^sub>2)" |
"mk_dnf_conj (OR x\<^sub>1 x\<^sub>2) e         = OR (mk_dnf_conj x\<^sub>1 e) (mk_dnf_conj x\<^sub>2 e)" |
"mk_dnf_conj x          y         = AND x y"

lemma mk_dnf_conj_preserves_semantics : "pbval (mk_dnf_conj e\<^sub>1 e\<^sub>2) s = (pbval e\<^sub>1 s \<and> pbval e\<^sub>2 s)"
apply(induction e\<^sub>1 e\<^sub>2 rule: mk_dnf_conj.induct)
apply(auto)
done

lemma mk_dnf_conj_maintains_is_nnf : "is_nnf e\<^sub>1 \<Longrightarrow> is_nnf e\<^sub>2 \<Longrightarrow> is_nnf (mk_dnf_conj e\<^sub>1 e\<^sub>2)"
apply(induction e\<^sub>1 e\<^sub>2 rule: mk_dnf_conj.induct)
apply(auto)
done

lemma mk_dnf_conj_maintains_is_disj_of_conj : "is_disj_of_conj e\<^sub>1 \<Longrightarrow> is_disj_of_conj e\<^sub>2 \<Longrightarrow> is_disj_of_conj (mk_dnf_conj e\<^sub>1 e\<^sub>2)"
apply(induction e\<^sub>1 e\<^sub>2 rule: mk_dnf_conj.induct)
apply(auto)
done

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR v)   = VAR v"                                     |
"dnf_of_nnf (NOT e)   = NOT (dnf_of_nnf e)"                        |
"dnf_of_nnf (AND x y) = mk_dnf_conj (dnf_of_nnf x) (dnf_of_nnf y)" |
"dnf_of_nnf (OR x y)  = OR (dnf_of_nnf x) (dnf_of_nnf y)"

lemma dnf_of_nnf_preserves_semantics : "pbval (dnf_of_nnf e) s = pbval e s"
apply(induction e)
apply(simp_all add: mk_dnf_conj_preserves_semantics)
done


lemma nnf_of_negation : "is_nnf (NOT e) \<Longrightarrow> is_nnf e"
apply(induction e)
apply(simp_all)
done

lemma is_nnf_of_not : "is_nnf (NOT e) \<Longrightarrow> is_nnf (dnf_of_nnf e) \<Longrightarrow> is_nnf (NOT (dnf_of_nnf e))"
apply(induction e)
apply(simp_all)
done

lemma dnf_of_nnf_maintains_is_nnf : "is_nnf e \<Longrightarrow> is_nnf (dnf_of_nnf e)"
apply(induction e)
apply(auto simp add: nnf_of_negation)
apply(simp add: is_nnf_of_not)
apply(simp add: mk_dnf_conj_maintains_is_nnf)
done

lemma dnf_of_nnf_maintains_is_disj_of_conj : "is_disj_of_conj (dnf_of_nnf e)"
apply(induction e)
apply(auto simp add: mk_dnf_conj_maintains_is_disj_of_conj)
done

theorem dnf_of_nnf_is_correct : "is_nnf e \<Longrightarrow> is_dnf (dnf_of_nnf e)"
apply(induction e)
apply(simp_all add: is_dnf_def)
apply(simp add: dnf_of_nnf_maintains_is_nnf nnf_of_negation is_nnf_of_not)
apply(auto simp add: dnf_of_nnf_maintains_is_nnf dnf_of_nnf_maintains_is_disj_of_conj)
apply(simp add: dnf_of_nnf_maintains_is_nnf mk_dnf_conj_maintains_is_nnf)
apply(simp add: dnf_of_nnf_maintains_is_disj_of_conj mk_dnf_conj_maintains_is_disj_of_conj)
done

end
