theory Chapter5
imports Main
begin

value "List.coset [1, 2, 3 :: int]"
(* value "surj" *)
thm surj_def
thm sym
thm surj_def[symmetric]

lemma flip_eq: "c = (a = b) \<Longrightarrow> c = (b = a)"
  apply(auto)
done

thm flip_eq[of x surj_def]

value "[1, 2, 3 :: int]"

(* Isar abbreviations:
   then  = from this
   thus  = then show
   hence = then have
*)

thm All_def
thm allI
thm allE

thm notI
thm someI

lemma no_surj_for_powerset: "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall> y. \<exists> x. y = f x" by(simp add: surj_def)
  (*from 1 have 2: "\<forall> y. \<exists> x. f x = y" by(simp add: sym)*)
  from 1 have 2: "\<exists> x. {y. y \<notin> f y} = f x" by simp
  from 2 show "False" by blast
qed

(* Linear flow of proof facts is to be preferred to labels
  this - proposition proved in the previous step
 *)

lemma no_surj_for_powerset_without_labels: "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists> x. {y. y \<notin> f y} = f x" by (simp add: surj_def)
  from this show "False" by blast
qed

(* Convenient abbreviations:
  then  = from this
  hence = then have
  thus  = then show
 *)

lemma no_surj_for_powerset_without_labels_with_abbrev: "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> x. {y. y \<notin> f y} = f x" by (simp add: surj_def)
  thus "False" by blast
qed

(* De-emphasize used facts:
  from F (have|show) P = (have|show) P using F
  from F this ...      = ... with F
 *)


(* Structured lemma format *)

lemma surjective_func_to_powerset_does_not_exist:
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof
  - (* Nil proof method - don't automatically search for an introduction rule for proof goal *)
  have "\<exists> x. {y. y \<notin> f y} = f x" using s by (simp add: surj_def)
  (* assms - list of all assumptions. Can index it with assms(1) or take range with assms(2-4) *)
  have "\<exists> x. {y. y \<notin> f y} = f x" using assms by (simp add: surj_def)
  thus "False" by blast
qed

lemma no_surj_for_powerset_without_labels_with_abbrev_no_auto_intro:
  "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  (rule notI)
  assume "surj f"
  hence "\<exists> x. {y. y \<notin> f y} = f x" by (simp add: surj_def)
  thus "False" by blast
qed

(*

lemma surjective_func_to_powerset_does_not_exist_with_cases:
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof
  - (* Nil proof method - don't automatically search for an introduction rule for proof goal *)
  have 1: "\<exists> x. {y. y \<notin> f y} = f x" using s by (simp add: surj_def)
  fix x :: "'a"
  from 1 have 2: "{y. y \<notin> f y} = f x" by auto
  show "False"
  proof cases
    assume "x \<in> f x"
    from 2 have "x \<notin> f x" by auto
    hence "False" by auto
  (*next
    assume "x \<notin> f x"
    hence "False" using 2 by auto *)
  qed
qed

*)



(*
lemma "\<not> (surj (f :: 'a \<Rightarrow> 'a set))"
proof
  assume 0: "surj f"
  from 0 have "\<forall> A. \<exists> a. A = f a" by (simp add: surj_def)
  from this have diag_set: "\<exists> a. {x. x \<notin> f x} = f a" by blast
  from diag_set show "False" by blast
qed

(* Structured lemma format *)
lemma
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes a: "surj f"
  shows "False"
proof - (* Use - as empty proof method to suppress automatic search for introduction rule for the
           goal since there's none for False. *)
  have "\<exists> a. {x. x \<notin> f x} = f a" using a by (auto simp: surj_def)
  thus "False" by blast
qed

*)

end
