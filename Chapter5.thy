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

text \<open>
Isar abbreviations:
   then  = from this
   thus  = then show
   hence = then have
\<close>

thm All_def
thm allI
thm allE

thm notI
thm someI

lemma no_surj_for_powerset: "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall> y. \<exists> x. y = f x" by (simp add: surj_def)
  (*from 1 have 2: "\<forall> y. \<exists> x. f x = y" by(simp add: sym)*)
  from 1 have 2: "\<exists> x. {y. y \<notin> f y} = f x" by simp
  from 2 show "False" by blast
qed

text \<open>
Linear flow of proof facts is to be preferred to labels
  this - proposition proved in the previous step
\<close>

lemma no_surj_for_powerset_without_labels: "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  from this have "\<exists> x. {y. y \<notin> f y} = f x" by (simp add: surj_def)
  from this show "False" by blast
qed

text \<open>
Convenient abbreviations:
  then  = from this
  hence = then have
  thus  = then show
\<close>

lemma no_surj_for_powerset_without_labels_with_abbrev: "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> x. {y. y \<notin> f y} = f x" by (simp add: surj_def)
  thus "False" by blast
qed

text \<open>
De-emphasize used facts:
  from F (have|show) P = (have|show) P using F
  from F this ...      = ... with F
\<close>

section \<open>Structured lemma format\<close>

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


lemma no_surj_for_powerset_without_labels_detailed_with_obtain:
  "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists> x. {y. y \<notin> f y} = f x" by (simp add: surj_def)
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  hence "a \<in> f a \<longleftrightarrow> a \<notin> f a" by auto
  thus "False" by simp
qed

thm dvd_def

lemma
  fixes a b :: int
  assumes "b dvd (a + b)"
  shows "b dvd a"
proof -
  { fix k :: int
    assume k_init: "a + b = b * k"
    have "\<exists> n. a = b * n"
    proof
      show "a = b * (k - 1)" using k_init by (simp add: algebra_simps)
    qed
  }
  note a_shape = this
  show ?thesis using assms a_shape by (auto simp add: dvd_def)
qed



lemma "p \<longrightarrow> (p \<and> p)"
proof (rule impI)
  assume 1: p
  show "p \<and> p" using 1 1 ..
qed

lemma "(p \<longrightarrow> q) \<and> (q \<longrightarrow> r) \<longrightarrow> (p \<longrightarrow> r)"
proof (rule impI)
  assume pqqr: "(p \<longrightarrow> q) \<and> (q \<longrightarrow> r)" (is "?pq \<and> ?qr")
  have pq: "?pq" using pqqr ..
  have qr: "?qr" using pqqr ..
  show "p \<longrightarrow> r"
  proof (rule impI)
    assume p: "p"
    have q: "q" using pq p ..
    show "r" using qr q ..
  qed
qed

theorem modus_ponens: "(\<forall> x. P x \<longrightarrow> Q x) \<and> P a \<longrightarrow> Q a"
proof (rule impI)
  assume assm: "(\<forall> x. P x \<longrightarrow> Q x) \<and> P a"
  have "(\<forall> x. P x \<longrightarrow> Q x)" using assm ..
  hence pq: "P a \<longrightarrow> Q a" ..
  have p: "P a" using assm ..
  show "Q a" using pq p ..
qed



definition even :: "nat => bool" where
  "even n \<equiv> \<exists> k. n = 2 * k"

definition odd :: "nat \<Rightarrow> bool" where
  "odd n \<equiv> \<exists> k. n = 2 * k + 1"

theorem
  assumes oN: "odd n"
  and     oM: "odd m"
  shows "even (n + m)"
proof -
  from oN have "\<exists> k. n = 2 * k + 1" unfolding odd_def .
  then obtain k where k_prop: "n = 2 * k + 1" ..
  from oM have "\<exists> q. m = 2 * q + 1" unfolding odd_def .
  then obtain q where q_prop: "m = 2 * q + 1" ..
  from k_prop q_prop have "n + m = 2 * k + 2 * q + 2" by simp
  also hence "... = 2 * (k + q + 1)" by simp
  finally have "n + m = 2 * (k + q + 1)" by simp
  hence "\<exists> p. n + m = 2 * p" ..
  thus "even (n + m)" unfolding even_def .
qed


subsection \<open>Exercise 5.1\<close>

thm disjE

lemma
  assumes T:   "\<forall> x y. T x y \<or> T y x"
  and     A:   "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and     TA:  "\<forall> x y. T x y \<longrightarrow> A x y"
  and     axy: "A x y"
  shows   "T x y"
proof -
  have "T x y \<or> T y x" using T by auto
  thus ?thesis
  proof (rule disjE)
    assume "T x y"
    thus "T x y" .
  next
    assume tyx_assm: "T y x"
    have ayx:  "A y x" using tyx_assm TA by auto
    have xisy: "x = y" using axy ayx A by auto
    have "T x y" using xisy tyx_assm by auto
    thus ?thesis .
  qed
qed

subsection \<open>Exercise 5.2\<close>

thm disjI1 disjI2 someI

thm List.length_take List.length_drop dvd_def semiring_parity_class.evenE

lemma
  " (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs)
  \<or> (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof cases
  assume xs_len_even: "2 dvd length xs"
  show ?thesis
  proof (rule disjI1)
    show "\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs"
    proof
      fix ys
      show "\<exists> zs. xs = ys @ zs \<and> length ys = length zs"
      proof
        fix zs
        show "xs = ys @ zs \<and> length ys = length zs"
        proof -
          from xs_len_even have "\<exists> k. length xs = k * 2" unfolding dvd_def by auto
          then obtain k where k_def: "length xs = k * 2" ..
          assume ys_def: "ys = take k xs"
          assume zs_def: "zs = drop k xs"
          have "xs = ys @ zs" using ys_def zs_def by simp
          moreover have "length ys = length zs" using ys_def zs_def k_def by auto
          ultimately show "xs = ys @ zs \<and> length ys = length zs" ..
        qed
      qed
    qed
  qed
next
  assume xs_len_odd: "\<not> (2 dvd length xs)"
  show ?thesis
  proof (rule disjI2)
    show "\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1"
    proof
      show "\<exists> zs. xs = ys @ zs \<and> length ys = length zs + 1"
      proof
        fix ys zs
        show "xs = ys @ zs \<and> length ys = length zs + 1" sorry
      qed
    qed
  qed
qed




(*
lemma length_of_take: "n \<le> length xs \<Longrightarrow> length (take n xs) = n"
  apply(induction n)
  apply(simp)
  apply(simp)
done

lemma length_of_drop: "n \<le> length xs \<Longrightarrow> length (drop n xs) = length xs - n"
  apply(induction n)
  apply(simp)
  apply(simp)
done

lemma x_div_2_smaller_than_x: "x div 2 \<le> (x :: nat)"
  apply(auto)
done

lemma min_of_x_and_x_div_2: "min (x :: nat) (x div 2) = x div 2"
  apply(induction x)
  apply(simp)
  apply(simp)
done
*)

(*
lemma x_minus_x_div_2: "((x :: nat) - x div 2) = x div 2 \<or> ((x :: nat) - x div 2) = x div 2 + 1"
  apply(induction x)
  apply(simp)
  apply(simp)
done
*)

thm List.length_take List.length_drop

(* lemma
  " (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs)
  \<or> (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof (rule disjI1)
  fix as bs len
  assume len_def: "len = length xs div 2"
  assume as_def: "as = take len xs"
  assume bs_def: "bs = drop len xs"

  have xs_ok: "xs = as @ bs" using as_def bs_def by simp
  have "len \<le> length xs" using len_def x_div_2_smaller_than_x by simp
  hence as_len: "length as = len" using as_def length_of_take by (simp del: List.length_take)
  (*have "length xs = len + len" using as_def bs_def xs_ok by*)
  have bs_len: "length bs = len" using bs_def len_def by (simp)
  (*also have "length as = length bs" using as_def bs_def length_of_take length_of_drop len_def by simp*)
   (*using as_def bs_def length_of_take by simp*)
  
qed
 *)

(* 
lemma
  " (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs)
  \<or> (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof (rule disjI1)
  show "\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs"
  proof
    show "\<exists> zs. xs = ys @ zs \<and> length ys = length zs"
    proof
      show "xs = ys @ zs \<and> length ys = length zs"
      proof
        assume ys_def: "ys = take (length xs div 2) xs"
        assume zs_def: "zs = drop (length xs div 2) xs"
        show "xs = ys @ zs" using ys_def zs_def by auto
qed
 *)









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


end
