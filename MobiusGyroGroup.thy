theory MobiusGyroGroup
  imports Complex_Main HOL.Real_Vector_Spaces HOL.Transcendental MoreComplex
          GyroGroup 
begin

definition oplus_m' :: "complex \<Rightarrow> complex \<Rightarrow> complex"  where
  "oplus_m' a z = (a + z) / (1 + (cnj a) * z)"

lemma oplus_m'_in_disc:
  assumes "cmod c1 < 1" "cmod c2 < 1"
  shows "cmod (oplus_m' c1 c2) < 1"
proof-
  have "Im ((c1 + c2) * (cnj c1 + cnj c2)) = 0"
    by (metis complex_In_mult_cnj_zero complex_cnj_add)
  moreover
  have "Im ((1 + cnj c1 * c2) * (1 + c1 * cnj c2)) = 0"
    by (cases c1, cases c2, simp add: field_simps)
  ultimately
  have 1: "Re (oplus_m' c1 c2 * cnj (oplus_m' c1 c2)) = 
        Re (((c1 + c2) * (cnj c1 + cnj c2))) /
        Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2)))"
    unfolding oplus_m'_def
    by (simp add: complex_is_Real_iff)

  have "Re (((c1 + c2) * (cnj c1 + cnj c2))) = 
       (cmod c1)\<^sup>2 + (cmod c2)\<^sup>2 + Re (cnj c1 * c2 + c1 * cnj c2)"
    by (smt Re_complex_of_real complex_norm_square plus_complex.simps(1) semiring_normalization_rules(34) semiring_normalization_rules(7))
  moreover
  have "Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2))) =
        Re (1 + cnj c1 * c2 + cnj c2 * c1 + c1 * cnj c1 * c2 * cnj c2)"
    by (simp add: field_simps)
  hence *: "Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2))) =
        1 + Re (cnj c1 * c2 + c1 * cnj c2) + (cmod c1)\<^sup>2 * (cmod c2)\<^sup>2"
    by (smt Re_complex_of_real ab_semigroup_mult_class.mult_ac(1) complex_In_mult_cnj_zero complex_cnj_one complex_norm_square one_complex.simps(1) one_power2 plus_complex.simps(1) power2_eq_square semiring_normalization_rules(7) times_complex.simps(1))
  moreover
  have "(cmod c1)\<^sup>2 + (cmod c2)\<^sup>2 < 1 + (cmod c1)\<^sup>2 * (cmod c2)\<^sup>2"
  proof-
    have "(cmod c1)\<^sup>2 < 1" "(cmod c2)\<^sup>2 < 1"
      using assms
      by (simp_all add: cmod_def)
    hence "(1 - (cmod c1)\<^sup>2) * (1 - (cmod c2)\<^sup>2) > 0"
      by simp
    thus ?thesis
      by (simp add: field_simps)
  qed
  ultimately
  have "Re (((c1 + c2) * (cnj c1 + cnj c2))) < Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2)))"
    by simp
  moreover
  have "Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2))) > 0"
    by (smt "*" Re_complex_div_lt_0 calculation complex_cnj_add divide_self mult_zero_left one_complex.simps(1) zero_complex.simps(1))
  ultimately
  have 2: "Re (((c1 + c2) * (cnj c1 + cnj c2))) / Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2))) < 1"
    by (simp add: divide_less_eq)
  
  have "Re (oplus_m' c1 c2 * cnj (oplus_m' c1 c2)) < 1"
    using 1 2
    by simp
    
  thus ?thesis
    by (simp add: complex_mod_sqrt_Re_mult_cnj)
qed

definition ominus_m' :: "complex \<Rightarrow> complex" where
  "ominus_m' z = - z"  


lemma ominus_m'_in_disc:
  assumes "cmod z < 1"
  shows "cmod (ominus_m' z) < 1"
  using assms
  unfolding ominus_m'_def
  by simp

lemma m_left_id:
  shows "\<And>a. a \<in> {z. cmod z < 1} \<longrightarrow> oplus_m' 0 a = a"
  by (simp add: oplus_m'_def)

lemma m_left_inv:
  shows "\<And>a. a \<in> {z. cmod z < 1} \<longrightarrow> oplus_m' (ominus_m' a) a = 0"
    by (simp add: ominus_m'_def oplus_m'_def)

definition gyr_m' :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex" where
  "gyr_m' a b z = ((1 + a * cnj b) / (1 + cnj a * b)) * z"


lemma gyr_m_closed:
  assumes "cmod a < 1" "cmod b < 1" "cmod z < 1"
    shows"cmod (gyr_m' a b z) < 1"
  by (metis assms(1) assms(2) assms(3) cmod_mix_cnj gyr_m'_def mult.commute mult_cancel_right1 norm_mult)
 
lemma gyr_m_commute:
  assumes "a \<in> {z. cmod z < 1}" " b \<in> {z. cmod z < 1}"
  shows "oplus_m' a b = gyr_m' a b (oplus_m' b  a)"
  by (smt (verit, ccfv_SIG) add.commute assms(1) assms(2) den_not_zero gyr_m'_def mem_Collect_eq mult.commute nonzero_mult_div_cancel_left oplus_m'_def times_divide_eq_right)

lemma gyr_m_left_assoc:
  assumes "a \<in> {z. cmod z < 1}" " b \<in> {z. cmod z < 1}" "z \<in> {z. cmod z < 1}"  
  shows "oplus_m' a  (oplus_m' b z) = oplus_m' (oplus_m' a b)  (gyr_m' a b z)"
proof-
  {
  fix a b z
  assume *: "cmod a < 1" "cmod b < 1" "cmod z < 1"
 
  have 1: "oplus_m' a (oplus_m' b z) =
          (a + b + (1 + a * cnj b) * z) / 
          ((cnj a + cnj b) * z + (1 + cnj a * b))"
      unfolding gyr_m'_def oplus_m'_def
      by (smt "*"(2) "*"(3) ab_semigroup_mult_class.mult_ac(1) add.left_commute add_divide_eq_iff combine_common_factor den_not_zero divide_divide_eq_right mult.commute mult_cancel_right2 nonzero_mult_div_cancel_left semiring_normalization_rules(1) semiring_normalization_rules(23) semiring_normalization_rules(34) times_divide_eq_right)
  moreover  have 2: "oplus_m' (oplus_m' a b) (gyr_m' a b z) = 
          ((a + b) + (1 + a * cnj b) * z) / 
          ((cnj a + cnj b) * z + (1 + cnj a * b))"
  proof-
    have x: "((a + b) / (1 + cnj a * b) +
           (1 + a * cnj b) / (1 + cnj a * b) * z) = 
          ((a + b) + (1 + a * cnj b) * z) / (1 + cnj a * b)"
      by (metis add_divide_distrib times_divide_eq_left)
    moreover
    have "1 + cnj ((a + b) / (1 + cnj a * b)) *
               ((1 + a * cnj b) / (1 + cnj a * b) * z) = 
          1 + (cnj a + cnj b) / (1 + cnj a * b) * z"
      using divide_divide_times_eq divide_eq_0_iff mult_eq_0_iff nonzero_mult_div_cancel_left
      by force
    hence y: "1 + cnj ((a + b) / (1 + cnj a * b)) *
               ((1 + a * cnj b) / (1 + cnj a * b) * z) =
          ((cnj a + cnj b) * z + (1 + cnj a * b)) / (1 + cnj a * b)"
      by (metis "*"(1) "*"(2) add.commute add_divide_distrib den_not_zero divide_self times_divide_eq_left)
    ultimately
    show ?thesis
      unfolding gyr_m'_def oplus_m'_def  
      by (subst x, subst y, simp add: "*"(1) "*"(2) den_not_zero)
  qed
  ultimately have "oplus_m' a  (oplus_m' b z) = oplus_m' (oplus_m' a b)  (gyr_m' a b z)"
    by argo
}
  then show ?thesis 
    using assms(1) assms(2) assms(3) by blast
qed


lemma gyr_m_inv:
  assumes  "a \<in> {z. cmod z < 1}" " b \<in> {z. cmod z < 1}" "z \<in> {z. cmod z < 1}"
  shows "gyr_m' a b (gyr_m' b a z) = z"
  by (smt (verit, best) assms(1) assms(2) den_not_zero gyr_m'_def mem_Collect_eq mult.commute nonzero_eq_divide_eq times_divide_eq_left)

lemma gyr_m_bij:
  assumes "a\<in>{z. cmod z < 1}" "b\<in>{z. cmod z < 1}"
  shows "bij_betw (gyr_m' a b) {z. cmod z <1} {z. cmod z < 1} "
proof-
  have "inj_on (gyr_m' a b) {z. cmod z < 1}"
    by (smt (verit, del_insts) assms(1) assms(2) gyr_m_inv inj_on_inverseI)
  moreover have "(gyr_m' a b) `{z. cmod z <1} = {z. cmod z < 1}"
  proof
    show "gyr_m' a b ` {z. cmod z < 1} \<subseteq> {z. cmod z < 1}"
      using assms(1) assms(2) gyr_m_closed by blast
  next
    show "{z. cmod z < 1} \<subseteq> gyr_m' a b ` {z. cmod z < 1}"
    proof
      show " \<And>x. x \<in> {z. cmod z < 1} \<Longrightarrow> x \<in> gyr_m' a b ` {z. cmod z < 1}"
        by (metis (no_types, lifting) assms(1) assms(2) gyr_m_closed gyr_m_inv imageI mem_Collect_eq)
    qed
  qed
  ultimately show ?thesis 
    by (simp add: bij_betw_def)
qed



lemma gyr_m_not_degenerate:
  assumes "a\<in>{z. cmod z < 1}" "b\<in>{z. cmod z < 1}"
  shows "\<exists> z1 z2. z1\<in>{z. cmod z < 1} \<and> z2\<in>{z. cmod z < 1} \<and>gyr_m' a b z1 \<noteq> gyr\<^sub>_m' a b z2"
proof-
  obtain z1 z2 where "z1 \<noteq> z2 \<and>  z1\<in>{z. cmod z < 1} \<and> z2\<in>{z. cmod z < 1}"
  proof -
    assume a1: "\<And>z1 z2. z1 \<noteq> z2 \<and> z1 \<in> {z. cmod z < 1} \<and> z2 \<in> {z. cmod z < 1} \<Longrightarrow> thesis"
    have "\<forall>r. cmod (cor r) = \<bar>r\<bar>"
      using norm_of_real by blast
    then show ?thesis
      using a1 by (metis abs_of_nonneg dense linorder_not_less mem_Collect_eq not_one_less_zero sgn_pos zero_le_sgn_iff zero_less_one)
  qed
  hence "gyr_m' a b z1 \<noteq> gyr_m' a b z2"
    by (metis assms(1) assms(2) gyr_m_inv)
  thus ?thesis
    by (metis \<open>z1 \<noteq> z2 \<and> z1 \<in> {z. cmod z < 1} \<and> z2 \<in> {z. cmod z < 1}\<close>)
qed

lemma gyr_m_left_loop:
  assumes "a\<in>{z. cmod z < 1}" "b\<in> {z. cmod z < 1}"
  shows "\<forall>z\<in>{z. cmod z< 1}. gyr_m' a b z = gyr_m' (oplus_m' a  b) b z"
proof- 
  have "\<exists> z. z\<in>{z. cmod z < 1} \<and> gyr_m' (oplus_m' a  b) b z \<noteq> 0"
    by (metis assms(1) assms(2) gyr_m_not_degenerate mem_Collect_eq oplus_m'_in_disc)
  moreover have "\<And> z. z\<in>{z. cmod z < 1}\<longrightarrow>gyr_m' a b z = gyr_m' (oplus_m' a  b) b z"
  proof-
    fix z
    show "z\<in>{z. cmod z < 1}\<longrightarrow>gyr_m' a b z = gyr_m' (oplus_m' a  b) b z"
    proof
      assume "z\<in>{z. cmod z < 1}"
      show "gyr_m' a b z = gyr_m' (oplus_m' a  b) b z"
      proof-   
(* assume "\<exists>z\<in>{z. cmod z < 1}. gyr_m' (oplus_m' a b) b z \<noteq> 0"*)
      obtain z' where
      "cmod z' < 1" "gyr_m' (oplus_m' a b) b z' \<noteq> 0"
        using \<open>\<exists>z. z \<in> {z. cmod z < 1} \<and> gyr_m' (oplus_m' a b) b z \<noteq> 0\<close> by blast
      moreover have *: "1 + (a + b) / (1 + cnj a * b) * cnj b \<noteq> 0"
 
        using calculation(2) gyr_m'_def oplus_m'_def by auto
    (*assume  "cmod z < 1"*)    
      moreover have 1: "1 + (a + b) / (1 + cnj a * b) * cnj b = 
          (1 + cnj a * b + a * cnj b + b * cnj b) / (1 + cnj a * b)"
      using assms
      by (simp add: add_divide_eq_iff den_not_zero distrib_right)
    moreover have 2: "1 + cnj ((a + b) / (1 + cnj a * b)) * b = 
             (1 + cnj a * b + a * cnj b + b * cnj b) / (1 + a * cnj b)"
      by (smt "1" complex_cnj_add complex_cnj_cnj complex_cnj_divide complex_cnj_mult complex_cnj_one semiring_normalization_rules(23) semiring_normalization_rules(7))
    moreover have "1 + cnj a * b + a * cnj b + b * cnj b \<noteq> 0"
      using * 1
      by auto
    ultimately show "gyr_m' a b z = gyr_m' (oplus_m' a b) b z"
      unfolding gyr_m'_def oplus_m'_def
      by (subst 1, subst 2, simp)
  qed
qed
qed
  thus ?thesis
    by blast
qed

lemma gyr_m_distrib:
  assumes "a\<in>{z. cmod z < 1}" "b\<in>{z. cmod z < 1}"
  "a'\<in>{z. cmod z < 1}" "b'\<in>{z. cmod z < 1}"
  shows "gyr_m' a b (oplus_m' a' b') = oplus_m' (gyr_m' a b a') (gyr_m' a b b')"
  apply transfer
  apply (auto simp add: gyr_m'_def oplus_m'_def)
  apply (simp add: add_divide_distrib distrib_left)
  done


interpretation Moebius_gyrogroup: gyrogroup "{z::complex. cmod z < 1}" 0 oplus_m' ominus_m' gyr_m'
proof
  show " 0 \<in> {z. cmod z < 1}"
    by simp
next 
  show "\<And>a b. a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1} \<longrightarrow>
           oplus_m' a b \<in> {z. cmod z < 1}"
    by (simp add: oplus_m'_in_disc)
next
  show "\<exists>a. a \<in> {z. cmod z < 1} \<and> a \<noteq> 0"
    by (metis (no_types) abs_of_nonneg dense linorder_not_less mem_Collect_eq norm_of_real not_one_less_zero sgn_pos zero_le_sgn_iff zero_less_one)
next
  show "\<And>a. a \<in> {z. cmod z < 1} \<longrightarrow> ominus_m' a \<in> {z. cmod z < 1}"
    by (simp add: ominus_m'_in_disc)
next
  show " \<And>a b c.
       a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1} \<and> c \<in> {z. cmod z < 1} \<longrightarrow>
       gyr_m' a b c \<in> {z. cmod z < 1}"
    by (simp add: gyr_m_closed)
next
  show "\<And>a. a \<in> {z. cmod z < 1} \<longrightarrow> oplus_m' 0 a = a"
    by (simp add: oplus_m'_def)
next
  show "\<And>a. a \<in> {z. cmod z < 1} \<longrightarrow> oplus_m' (ominus_m' a) a = 0"
    by (simp add: ominus_m'_def oplus_m'_def)
next
  show "\<And>a b z.
       a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1} \<and> z \<in> {z. cmod z < 1} \<longrightarrow>
       oplus_m' a (oplus_m' b z) = oplus_m' (oplus_m' a b) (gyr_m' a b z)"
    using gyr_m_left_assoc by presburger
next
  show " \<And>a b. a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1} \<longrightarrow>
           (\<forall>x\<in>{z. cmod z < 1}. gyr_m' a b x = gyr_m' (oplus_m' a b) b x)"
    using gyr_m_left_loop by force
next
  fix a b
  show "a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1} \<longrightarrow>
           gyrogroupoid.gyroaut {z. cmod z < 1} oplus_m' (gyr_m' a b)"
  proof
    assume "a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1}"
    show " gyrogroupoid.gyroaut {z. cmod z < 1} oplus_m' (gyr_m' a b)"
      using gyrogroupoid.gyroaut_def
    proof-
      have "(\<forall>a'\<in>{z. cmod z < 1}. \<forall>b'\<in>{z. cmod z < 1}. (gyr_m' a b) (oplus_m' a' b')
 = oplus_m' ((gyr_m' a b) a') ((gyr_m' a b) b'))"
        using \<open>a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1}\<close> gyr_m_distrib by blast
      moreover have "bij_betw (gyr_m' a b) {z. cmod z < 1} {z. cmod z < 1}"
        using \<open>a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1}\<close> gyr_m_bij by blast
      moreover have "gyrogroupoid {z. cmod z < 1} 0 oplus_m'"
        by (smt (verit, ccfv_threshold) gyr_m_not_degenerate gyrogroupoid_def mem_Collect_eq norm_zero oplus_m'_in_disc)
      ultimately show ?thesis
        using gyrogroupoid.gyroaut_def
        by (metis (no_types, lifting))
    qed
  qed
qed







                                    









interpretation Mobius_gyrocommutative_gyrogroup: gyrocommutative_gyrogroup "{z. cmod z < 1}" 0 oplus_m' ominus_m' gyr_m'
proof
  show "\<forall>a\<in>{z. cmod z < 1}.
       \<forall>b\<in>{z. cmod z < 1}. oplus_m' a b = gyr_m' a b (oplus_m' b a)"
    using gyr_m_commute by blast
qed


lemma gyr_m_alternative_gyr_m:
  assumes "u\<in>{z. cmod z < 1}" "v\<in>{z. cmod z < 1}" "w\<in>{z. cmod z < 1}"
  shows "gyr_m' u v w = oplus_m' (ominus_m' (oplus_m' u v))  (oplus_m' u  (oplus_m' v  w))"
  using Moebius_gyrogroup.gyr_def assms(1) assms(2) assms(3) by blast

definition oplus_m'_alternative :: "complex \<Rightarrow> complex \<Rightarrow> complex" where 
  "oplus_m'_alternative u v =
      ((1 + 2*inner u v + (norm v)^2) *\<^sub>R u + (1 - (norm u)^2) *\<^sub>R v) /
       (1 + 2*inner u v + (norm u)^2 * (norm v)^2)"

lemma oplus_m'_alternative:
  assumes "cmod u < 1" "cmod v < 1"
  shows "oplus_m'_alternative u v = oplus_m' u v"
proof-
  have *: "2 * inner u v = cnj u * v + cnj v * u"
    using two_inner_cnj
    by auto
  
  have "(1 + 2*inner u v + (norm v)^2) * u =
        (1 + cnj u *v + cnj v * u + (norm v)^2) * u"
    using *
    by auto

  moreover

  have "1 + 2*inner u v + (norm u)^2 * (norm v)^2 = 
        1 + cnj u * v + cnj v * u + (norm u)^2 * (norm v)^2"
    using *
    by auto

  moreover

  have "(1 + cnj u * v + cnj v * u + (norm v)^2) * u + (1 - (norm u)^2) * v =
        (1 + cnj v * u) * (u + v)"
  proof-
    have *: "(1 + cnj u * v + cnj v * u + (norm v)^2) * u = 
             u + (norm u)^2 * v + cnj v * u^2 + (norm v)^2 * u"
      by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1) comm_semiring_class.distrib complex_norm_square mult.commute mult_cancel_right1 power2_eq_square)
    have **: "(1 + cnj v * u) * (u + v) = u + cnj v * u * u + v + cnj v * u * v"
      by (simp add: distrib_left ring_class.ring_distribs(2))
    have "u + cnj u * v *u + v + cnj u* v * v = u + cnj u * v^2 + (norm u)^2 * v + v"
      by (simp add: cnj_cmod mult.commute power2_eq_square)
    have ***: "(1 - (norm u)^2) * v = v - (norm u)^2 * v"
      by (simp add: mult.commute right_diff_distrib')
    have "(1 + cnj u * v + cnj v * u + (norm v)^2) * u + (1 - (norm u)^2) * v =
          u + (norm u)^2 * v + (cnj v) * u^2 + (norm v)^2 * u + v - (norm u)^2 * v"
      using * ***
      by force
    have ****: "(1 + cnj u * v + cnj v * u + (norm v)^2) * u + (1-(norm u)^2) * v =
                u + cnj v *u^2 + (norm v)^2 * u + v"
      using * *** 
      by auto

    have "(1 + cnj v * u) * (u+v) = u + (norm v)^2 *u + v + cnj v * u^2"
      using **
      by (simp add: cnj_cmod mult.commute power2_eq_square)

    then show ?thesis
      using ****
      by auto
  qed

  moreover have "1 + cnj u * v + cnj v *u + (norm u)^2 * (norm v)^2  =
                (1 + cnj u * v) * (1 + cnj v * u)"
    by (smt (verit, del_insts) cnj_cmod comm_semiring_class.distrib complex_cnj_cnj complex_cnj_mult complex_mod_cnj is_num_normalize(1) mult.commute mult_numeral_1 norm_mult numeral_One power_mult_distrib)
  
  ultimately
  show ?thesis 
    using assms
    unfolding oplus_m'_alternative_def oplus_m'_def
    by (metis (no_types, lifting) den_not_zero divide_divide_eq_left' nonzero_mult_div_cancel_left scaleR_conv_of_real)
qed



end
