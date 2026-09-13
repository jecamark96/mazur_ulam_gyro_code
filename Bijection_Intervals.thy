theory Bijection_Intervals
  imports Complex_Main "HOL-Library.FuncSet"
begin

definition A :: "real set" where
  "A = {x. x < 0}"

definition B :: "real set" where
  "B = {x. x \<le> -1}"

definition h :: "real \<Rightarrow> real" where
  "h x = (if x \<in> Ints \<and> x < 0 then x else x - 1)"

definition h_inv :: "real \<Rightarrow> real" where
  "h_inv y = (if y \<in> Ints \<and> y < 0 then y else y + 1)"

lemma Ints_sub_1_iff [simp]:
  fixes x :: real
  shows "x - 1 \<in> Ints \<longleftrightarrow> x \<in> Ints"
proof
  assume h: "x - 1 \<in> Ints"
  have "(x - 1) + 1 \<in> Ints"
    using Ints_1 Ints_add h by blast
 
  then show "x \<in> Ints"
    by simp
next
  assume "x \<in> Ints"
  then show "x - 1 \<in> Ints"
    by simp
qed

lemma Ints_add_1_iff [simp]:
  fixes x :: real
  shows "x + 1 \<in> Ints \<longleftrightarrow> x \<in> Ints"
proof
  assume h: "x + 1 \<in> Ints"
  have "(x + 1) - 1 \<in> Ints"
    using Ints_sub_1_iff h by blast
  then show "x \<in> Ints"
    by simp
next
  assume "x \<in> Ints"
  then show "x + 1 \<in> Ints"
    by simp
qed

lemma Ints_neg_le_minus_one:
  fixes x :: real
  assumes "x \<in> Ints" "x < 0"
  shows "x \<le> -1"
proof -
  from assms(1) obtain z :: int where z: "x = of_int z"
    by (auto simp: Ints_def)
  with assms(2) have "z < 0"
    by simp
  then have "z \<le> -1"
    by simp
  with z show ?thesis
    by simp
qed

lemma h_into_B:
  "h \<in> A \<rightarrow> B"
proof
  fix x
  assume xA: "x \<in> A"
  then have xneg: "x < 0"
    by (simp add: A_def)

  show "h x \<in> B"
  proof (cases "x \<in> Ints \<and> x < 0")
    case True
    then have "x \<le> -1"
      using Ints_neg_le_minus_one by blast
    then show ?thesis
      using True by (simp add: B_def h_def)
  next
    case False
    have "x - 1 \<le> -1"
      using xneg by linarith
    with False show ?thesis
      
      by (metis False \<open>x - 1 \<le> - 1\<close> h_def B_def mem_Collect_eq)
      
  qed
qed

lemma h_inv_into_A:
  "h_inv \<in> B \<rightarrow> A"
proof
  fix y
  assume yB: "y \<in> B"
  then have yle: "y \<le> -1"
    by (simp add: B_def)

  show "h_inv y \<in> A"
  proof (cases "y \<in> Ints \<and> y < 0")
    case True
    then show ?thesis
      by (simp add: A_def h_inv_def)
  next
    case False
    have yneg: "y < 0"
      using yle by linarith
    with False have ynot: "y \<notin> Ints"
      by blast

    have "y \<noteq> -1"
    proof
      assume "y = -1"
      then have "y \<in> Ints"
        by simp
      with ynot show False
        by contradiction
    qed

    with yle have "y < -1"
      by linarith
    then have "y + 1 < 0"
      by linarith

    with False show ?thesis
      by (simp add: A_def h_inv_def)
  qed
qed

lemma h_inv_h:
  assumes "x \<in> A"
  shows "h_inv (h x) = x"
proof -
  have xneg: "x < 0"
    using assms by (simp add: A_def)

  show ?thesis
  proof (cases "x \<in> Ints \<and> x < 0")
    case True
    then show ?thesis
      by (simp add: h_def h_inv_def)
  next
    case False
    with xneg have xnot: "x \<notin> Ints"
      by blast
    then have "x - 1 \<notin> Ints"
      by simp
    with False show ?thesis
      by (simp add: h_def h_inv_def)
  qed
qed

lemma h_h_inv:
  assumes "y \<in> B"
  shows "h (h_inv y) = y"
proof -
  have yle: "y \<le> -1"
    using assms by (simp add: B_def)
  then have yneg: "y < 0"
    by linarith

  show ?thesis
  proof (cases "y \<in> Ints \<and> y < 0")
    case True
    then show ?thesis
      by (simp add: h_def h_inv_def)
  next
    case False
    with yneg have ynot: "y \<notin> Ints"
      by blast
    then have "y + 1 \<notin> Ints"
      by simp
    with False show ?thesis
      by (simp add: h_def h_inv_def)
  qed
qed

theorem h_bij:
  "bij_betw h A B"
  by (rule bij_betwI[OF h_into_B h_inv_into_A h_inv_h h_h_inv])

corollary h_bij_interval:
  "bij_betw h {x::real. x < 0} {x::real. x \<le> -1}"
  using h_bij by (simp add: A_def B_def)

corollary exists_bij_interval:
  "\<exists>h. bij_betw h {x::real. x < 0} {x::real. x \<le> -1}"
  using h_bij_interval by blast

end