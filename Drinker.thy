theory Drinker
  imports Main
begin

(*
lemma de_Morgan:
  assumes "\<not> (\<forall> x. P x)"
  shows "\<exists> x. \<not> (P x)"
proof
  show ?thesis by (simp add: Meson.not_allD)
qed
*)

theorem Drinker's_Principle: "\<exists>x. (drunk x \<longrightarrow> (\<forall>y. drunk y))"
proof cases
  assume "\<forall>x. drunk x"
  then have "drunk a \<longrightarrow> (\<forall>x. drunk x)" for a ..
  then show ?thesis ..
next
  assume "\<not> (\<forall>x. drunk x)"
  then have "\<exists>x. \<not> drunk x" by (rule Meson.not_allD)
  then obtain a where "\<not> drunk a" ..
  have "drunk a \<longrightarrow> (\<forall>x. drunk x)"
  proof
    assume "drunk a"
    with \<open>\<not> drunk a\<close> show "\<forall>x. drunk x" by contradiction
  qed
  then show ?thesis ..
qed

thm exI exI[of _ XXX]
thm allI

lemma quantifiers_test:
  assumes "\<exists> x. \<forall> y. R x y"
  shows   "\<forall> y. \<exists> x. R x y"
proof
  obtain x where p: "\<forall> y. R x y" using assms .. (* \<exists>-elimination *)
  fix y have "R x y" using p ..                 (* \<forall>-elimination *)
  then show "\<exists> x. R x y" ..                     (* \<exists>-introduction *)
qed

lemma forall_example:
  assumes prop_a: "\<forall> y. A y"
  assumes prop_b: "\<forall> y. B y"
  shows           "\<forall> y. A y \<and> B y"
proof
  (*fix y have "A y" using prop_a ..
  fix y have "B y" using prop_b ..*)

  fix z
  have a: "A z" using prop_a ..
  have b: "B z" using prop_b ..
  from a b show "A z \<and> B z" .. (* NB show the formula *under* the quantifier, the quantifer in thesis became part of proof context *)
qed

lemma de_Morgan1:
  assumes "\<not> (\<exists> x. P x)"
  shows   "\<forall> x. \<not> (P x)"
proof
  fix a
  show "\<not> (P a)"
  proof (cases "P a")
    case True
    assume "P a"
    then have "\<exists> y. P y" ..
    then show ?thesis using assms by contradiction
  next
    case False
    assume "\<not> (P a)"
    thus ?thesis .
  qed
qed

lemma de_Morgan2:
  assumes "\<exists> x. \<not> (P x)"
  shows   "\<not> (\<forall> x. P x)"
proof
  assume forall_assumption: "\<forall> x. P x"
  from assms obtain y where not_y: "\<not> (P y)" ..
  from forall_assumption have yes_y: "P y" ..
  show "False" using yes_y not_y by contradiction
qed

thm HOL.notnotD ccontr notE
thm mp FalseE
thm mp [THEN FalseE]

lemma double_negation:
  assumes "\<not> (\<not> P)"
  shows   "P"
proof(cases "P")
  case True
  assume "P"
  then show ?thesis .
next
  case False
  assume not_p: "\<not> P"
  then show ?thesis using assms by contradiction
qed

thm double_negation double_negation[of "\<exists> x. \<not> (P x)"] mp
(*thm mp[of "\<not> (\<not> (\<exists> x. \<not> (P x)))" "\<exists> x. \<not> (P x)"] impI[THEN double_negation[of "\<exists> x. \<not> (P x)"]]
thm mp[of "\<not> (\<not> (\<exists> x. \<not> (P x)))" "\<exists> x. \<not> (P x)"][impI[THEN double_negation[of "\<exists> x. \<not> (P x)"]]]*)

lemma meta_mp:
  assumes p:  "P"
  and     pq: "P \<Longrightarrow> Q"
  shows   "Q"
proof -
  show "Q" using pq p .
qed

thm de_Morgan1[of "\<lambda> x. \<not> (P x)"] double_negation

thm all_reg
(*lemma apply_under_all:
  assumes prop_p:  "\<forall> x. P x"
  assumes prop_pq: "\<forall> y. (P y \<longrightarrow> Q y)"
  shows   "\<forall> z. Q z"
proof
  fix z
  from prop_p have "P z" ..
  then have "Q z" using prop_pq ..
*)

thm double_negation double_negation[of "P x"]

lemma de_Morgan3:
  assumes "\<not> (\<forall> x. P x)"
  shows   "\<exists> x. \<not> (P x)"
proof(cases "\<not> (\<exists> x. \<not> (P x))")
  case False
  assume not_not: "\<not> (\<not> (\<exists> x. \<not> (P x)))"
  show "(\<exists> x. \<not> (P x))" using double_negation[of "\<exists> x. \<not> (P x)"] not_not .
next
  case True
  assume not_ex: "\<not> (\<exists> x. \<not> (P x))"
  have not_not_p: "\<forall> x. \<not> (\<not> (P x))" using de_Morgan1[of "\<lambda> x. \<not> (P x)"] not_ex .
  have "\<forall> x. P x"
  proof
    fix x
    have not_not_x: "\<not> (\<not> (P x))" using not_not_p ..
    show "P x" using double_negation not_not_x .
  qed
  then show ?thesis using assms by contradiction
qed

theorem drinker_paradox: "\<exists> x. (drunk x \<longrightarrow> (\<forall> y. drunk y))"
proof(cases "\<forall> z. drunk z")
  case True
  assume "\<forall> z. drunk z"
  then have "drunk a \<longrightarrow> (\<forall> z. drunk z)" for a ..
  then show ?thesis by (rule exI)
next
  case False
  assume not_all_drunk: "\<not> (\<forall> z. drunk z)"
  have "\<exists> z. \<not> (drunk z)" using de_Morgan3 not_all_drunk .
  then obtain zz where "\<not> (drunk zz)" ..
  then have "drunk zz \<longrightarrow> (\<forall> y. drunk y)" by simp
  then show ?thesis by (simp only: exI)
qed

(*
theorem drinker_paradox_bad: "\<exists> x. (drunk x \<longrightarrow> (\<forall> y. drunk y))"
  proof(rule exI, rule impI, rule allI, cases "\<forall> z. drunk z")
  case True
  fix x
  have "\<forall> z. drunk z"
  then show "drunk y" by blast
next
  case False
  fix x
  have "\<not> (\<forall> z. drunk z)"

  assume "\<not> (drunk x)"
  case False
  then show ?thesis sorry
qed
*)

end
