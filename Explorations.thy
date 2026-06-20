(* Trying things out to see how they work. No intention to prove anything *)
theory Explorations
imports Main
begin

fun itrev_helper :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev_helper []       ys = ys" |
"itrev_helper (x # xs) ys = itrev_helper xs (x # ys)"

fun itrev :: "'a list \<Rightarrow> 'a list" where
(*definition itrev :: "'a list \<Rightarrow> 'a list" where*)
"itrev xs = itrev_helper xs []"

(*
  Cannot prove weaker statement, "itrev_helper xs [] = rev xs", by
  induction - IH would be too weak to prove the step.

  Can, and sometimes must, further strengthen IH by universally
  quantifying over free variables that we're not inducting over.
*)

(* lemma itrev_helper_reverses: "itrev_helper xs ys = rev xs @ ys"
apply(induction xs arbitrary: ys)
apply(auto)
done

lemma itrev_helper_reverses_alt: "\<forall> ys. itrev_helper xs ys = rev xs @ ys"
apply(induction xs)
apply(auto)
done

theorem itrev_reverses: "itrev xs = rev xs"
apply(auto simp add: itrev_helper_reverses)
done *)

fun is_even_length :: "'a list \<Rightarrow> bool" where
"is_even_length []            = True" |
"is_even_length (x # ys # xs) = is_even_length xs" |
"is_even_length [_]           = False"

lemma itrev_helper_reverses_isar:
  fixes xs ys
  assumes xs_even: "is_even_length xs"
  assumes ys_even: "is_even_length ys"
  shows "itrev_helper xs ys = rev xs @ ys"
proof (induction xs arbitrary: ys)
  case Nil
  print_cases
  thm Nil
  then show ?case by auto
next
  case zs: (Cons a xs)
  (* have xs_even_induct: "is_even_length zs" by try0 *)
  (* have xs_even_induct: "is_even_length (Cons a xs)" by auto *)
  print_cases
  thm zs zs.IH
  thm Cons
  then show ?case by auto
qed

lemma itrev_helper_reverses_isar2:
  fixes xs :: "'a list"
  fixes ys :: "'a list"
  assumes xs_even: "is_even_length xs"
  assumes ys_even: "is_even_length ys"
  shows "itrev_helper xs ys = rev xs @ ys"
proof (induction xs arbitrary: ys)
  fix ys :: "'a list"
  show "itrev_helper [] ys = rev [] @ ys" by auto
next
  fix a   :: "'a"
  fix xs2 :: "'a list"
  fix ys2 :: "'a list"
  (* assume xs_induct: "xs = Cons a xs2" *)
  assume IH : "\<And>ys. itrev_helper xs2 ys = rev xs2 @ ys"

  (* have xs_even_induct: "is_even_length (Cons a xs2)" using xs_even by auto *)

  show "itrev_helper (Cons a xs2) ys2 = rev (Cons a xs2) @ ys2" using IH by auto
qed

(* lemma itrev_helper_reverses_isar3:
  fixes xs :: "'a list"
  fixes ys :: "'a list"
  assumes xs_even: "is_even_length xs"
  assumes ys_even: "is_even_length ys"
  shows "itrev_helper xs ys = rev xs @ ys"
using assms
proof (induction xs arbitrary: ys)
  fix ys :: "'a list"
  show "itrev_helper [] ys = rev [] @ ys" by auto
next
  fix a   :: "'a"
  fix xs2 :: "'a list"
  fix ys2 :: "'a list"
  (* assume xs_induct: "xs = Cons a xs2" *)
  assume IH : "\<And>ys. itrev_helper xs2 ys = rev xs2 @ ys"

  have xs_even_induct: "is_even_length (Cons a xs2)" using xs_even by auto

  show "itrev_helper (Cons a xs2) ys2 = rev (Cons a xs2) @ ys2" using IH by auto
qed *)


lemma itrev_helper_reverses_isar4:
  fixes xs ys
  assumes xs_even: "is_even_length xs"
  assumes ys_even: "is_even_length ys"
  shows "itrev_helper xs ys = rev xs @ ys"
  using assms
proof (induction xs arbitrary: ys rule: is_even_length.induc)
  case Nil
  print_cases
  thm Nil
  then show ?case by auto
next
  case zs: (Cons a xs)
  (* have xs_even_induct: "is_even_length zs" by try0 *)
  have xs_even_induct: "is_even_length (Cons a xs)" by auto
  print_cases
  thm zs zs.IH
  thm Cons
  then show ?case by auto
qed


end
