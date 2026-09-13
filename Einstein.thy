theory Einstein
  imports Complex_Main GyroGroup NGL GammaFactor HOL.Real_Vector_Spaces
  MobiusGyroGroup MobiusGyroVectorSpace HOL.Transcendental  GGV GV
begin



definition oplus_e' :: "complex \<Rightarrow> complex \<Rightarrow> complex"  where
  "oplus_e' u v = (if u\<in>{z. cmod z < 1} \<and> v\<in>{z. cmod z<1}
then (1 / (1 + inner u v)) *\<^sub>R (u + (1 / \<gamma> u) *\<^sub>R v + ((\<gamma> u / (1 + \<gamma> u)) * (inner u v)) *\<^sub>R u)
else undefined)"

lemma noroplus_m'_e:
  assumes "norm u < 1" "norm v <1"
  shows "norm (oplus_e' u v)^2 =
         1 / (1 + inner u v)^2 * (norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - (inner u v)^2))"
proof-
  let ?uv = "inner u v"
  let ?gu = "\<gamma> u / (1 + \<gamma> u)"

 
  have 1: "norm (oplus_e' u v)^2 = 
           norm (1 / (1 + ?uv))^2 * norm ((u + ((1 / \<gamma> u) *\<^sub>R v) + (?gu * ?uv) *\<^sub>R u))^2"  

    by (smt (verit, best) assms(1) assms(2) mem_Collect_eq norm_scaleR oplus_e'_def power_mult_distrib real_norm_def)
    

  have 2: "norm (1 / (1 + ?uv))^2 =  1 / (1 + ?uv)^2"
    by (simp add: power_one_over)

  have "norm((u + ((1 / \<gamma> u) *\<^sub>R v) + (?gu * ?uv) *\<^sub>R u))^2 = 
        inner (u + (1 / \<gamma> u) *\<^sub>R v + (?gu * ?uv) *\<^sub>R u) 
              (u + (1 / \<gamma> u) *\<^sub>R v + (?gu * ?uv) *\<^sub>R u)"
    by (simp add: dot_square_norm)
  also have "\<dots> = 
        (norm u)^2 + 
        (norm ((1 / \<gamma> u) *\<^sub>R v))^2 + 
        (norm ((?gu * ?uv) *\<^sub>R u))^2 + 
        2 * inner u ((1 / \<gamma> u) *\<^sub>R v) + 
        2 * inner u ((?gu * ?uv) *\<^sub>R u) +
        2 * inner ((?gu * ?uv) *\<^sub>R u) ((1 / \<gamma> u) *\<^sub>R v)" (is "?lhs = ?a + ?b + ?c + ?d + ?e + ?f")
    by (smt (verit) inner_commute inner_left_distrib power2_norm_eq_inner)
  also have "\<dots> = (norm u)^2 + 
                  1 / (\<gamma> u)^2 * (norm v)^2 + 
                  ?gu^2 * (inner u v)^2 * (norm u)^2 +
                  2 / \<gamma> u * (inner u v) +
                  2 * ?gu * ?uv * (inner u u) +
                  2 * ?gu * ?uv * (1 / \<gamma> u) * (inner u v)"
  proof-
    have "?b = 1 / (\<gamma> u)^2 * (norm v)^2"
      by (simp add: power_divide)
    moreover
    have "?c = ?gu^2 * (inner u v)^2 * (norm u)^2"
      by (simp add: power2_eq_square)
    moreover
    have "?d = 2 / \<gamma> u * (inner u v)"
      using inner_scaleR_right
      by auto
    moreover
    have "?e = 2 * ?gu * ?uv * (inner u u)"
      using inner_scaleR_right
      by auto
    moreover
    have "?f = 2 * ?gu * ?uv * (1 / \<gamma> u) * (inner u v)"
      by force
    ultimately
    show ?thesis
      by presburger
  qed
  also have "\<dots> = 2 * inner u v + (inner u v)^2 + (norm u)^2 + (1 - (norm u)^2) * (norm v)^2"  (is "?a + ?b + ?c + ?d + ?e + ?f = ?rhs")
  proof-
    have "?a + ?b = (norm u)^2 + (1 - (norm u)^2) * (norm v)^2"
      using assms norm_square_gamma_factor
      by force

    

    moreover have "?d + ?e = 2 * inner u v" (is "?lhs = ?rhs")
    proof-
      have "?e = 2 * (\<gamma> u * (norm u)^2 / (1 + \<gamma> u)) * inner u v"
        by (simp add: dot_square_norm)
      moreover
      have "1 / \<gamma> u + \<gamma> u * (norm u)^2 / (1 + \<gamma> u) = 1"
        using assms(1) gamma_expression_eq_one_1
        by blast
      moreover
      have "?d + 2 * (\<gamma> u * (norm u)^2 / (1 + \<gamma> u)) * inner u v = 2 * inner u v * (1 / \<gamma> u + \<gamma> u * (norm u)^2 / (1 + \<gamma> u))"
        by (simp add: distrib_left)
      ultimately 
      show ?thesis
        by (metis mult.right_neutral)
    qed

    moreover

    have "?c + ?f = (inner u v)^2"
    proof-
      have "?c + ?f = ?gu^2 * (norm u)^2 * (inner u v)^2 + 2 * (1 / \<gamma> u) * ?gu * (inner u v)^2"
        by (simp add: mult.commute mult.left_commute power2_eq_square)
      then have "?c + ?f = ((\<gamma> u / (1 + \<gamma> u))^2 * (norm u)^2 + 2 * (1 / \<gamma> u) * (\<gamma> u / (1 + \<gamma> u))) * (inner u v)^2"
        by (simp add: ring_class.ring_distribs(2))
      moreover
      have "(\<gamma> u / (1 + \<gamma> u))^2 * (norm u)^2 + 2 * (1 / \<gamma> u) * (\<gamma> u / (1 + \<gamma> u)) = 1"
      proof -
        have "\<forall> (x::real) y n. (x / y) ^ n = x ^ n / y ^ n"
          by (simp add: power_divide)
        then show ?thesis
          using gamma_expression_eq_one_2[OF assms(1)]
          by fastforce
      qed
      ultimately
      show ?thesis
        by simp
    qed

    ultimately
    show ?thesis
      by auto
  qed
  also have "\<dots> = ((cmod (u + v))\<^sup>2 - ((cmod u)\<^sup>2 * (cmod v)\<^sup>2 - ?uv\<^sup>2))"
    unfolding dot_square_norm[symmetric]
    by (simp add: inner_commute inner_right_distrib field_simps)
  finally
  have 3: "norm ((u + ((1 / \<gamma> u) *\<^sub>R v) + (?gu * ?uv) *\<^sub>R u))^2 =
           norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2)"
    by simp

  show ?thesis
    using 1 2 3
    by simp
qed

lemma gamma_oplus_e':
  assumes "norm u < 1" "norm v < 1"
  shows "1 / sqrt(1 - norm (oplus_e' u v)^2) = \<gamma> u * \<gamma> v * (1 + inner u v)"
proof-
  let ?uv = "inner u v"

  have abs: "abs (1 + ?uv) = 1 + ?uv"
    using abs_inner_lt_1 assms by fastforce

  have "1 - norm (oplus_e' u v)^2 = 
        1 - 1 / (1 + ?uv)^2 * (norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2))"
    using assms noroplus_m'_e
    by presburger
  also have "\<dots> = ((1 + ?uv)^2 - (norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2))) /
                  (1 + ?uv)^2"
  proof-
    have "?uv \<noteq> -1"
      using abs_inner_lt_1[OF assms]
      by auto
    then have "(1 + ?uv)^2 \<noteq> 0"
      by auto
    then show ?thesis
      by (simp add: diff_divide_distrib)
  qed
  also have "\<dots> = (1 - (norm u)^2 - (norm v)^2 + (norm u)^2 * (norm v)^2) / (1 + ?uv)^2"
  proof-
    have "(1 + ?uv)^2  = 1 + 2*?uv + ?uv^2"
      by (simp add: power2_eq_square field_simps)
    moreover
    have "norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2) = 
         (norm u)^2 + 2*?uv + (norm v)^2 - (norm u)^2*(norm v)^2 + ?uv^2"
      by (smt (z3) dot_norm field_sum_of_halves)
    ultimately
    show ?thesis
      by auto
  qed
  finally have "1 / sqrt (1 - norm (oplus_e' u v)^2) = 
                1 / sqrt((1 - (norm u)^2 - (norm v)^2 + (norm u)^2*(norm v)^2) / (1 + ?uv)^2)"
    by simp
  then have 1: "1 / sqrt (1 - norm (oplus_e' u v)^2) = 
                (1 + ?uv) / sqrt (1 - (norm u)^2 - (norm v)^2 + (norm u)^2*(norm v)^2)"
    using abs
    by (simp add: real_sqrt_divide)

  have "\<gamma> u = 1 / sqrt(1 - (norm u)^2)" "\<gamma> v = 1 / sqrt(1 - (norm v)^2)"
    using assms
    by (metis gamma_factor_def)+
  then have "\<gamma> u * \<gamma> v = (1 / sqrt (1 - (norm u)^2)) * (1 / sqrt (1 - (norm v)^2))"
    by simp
  also have "\<dots> = 1 / sqrt ((1 - (norm u)^2) * (1 - (norm v)^2))"
    by (simp add: real_sqrt_mult)
  finally have 2: "\<gamma> u * \<gamma> v = 1 / sqrt ((1 - (norm u)^2 - (norm v)^2 + (norm u)^2*(norm v)^2))"
    by (simp add: field_simps power2_eq_square)

  show ?thesis
    using 1 2
    by (metis (no_types, lifting) mult_cancel_right1 times_divide_eq_left)
qed

lemma gamma_oplus_e'_not_zero:
  assumes "norm u < 1" "norm v < 1"
  shows "1 / sqrt(1 - norm(oplus_e' u v)^2) \<noteq> 0"
  using assms
  using gamma_oplus_e' gamma_factor_def gamma_factor_nonzero noroplus_m'_e
  by (smt (verit, del_insts) divide_eq_0_iff mult_eq_0_iff zero_eq_power2)
  (*by fastforce*)

lemma oplus_e'_in_unit_disc:
  assumes "norm u < 1" "norm v < 1"
  shows "norm (oplus_e' u v) < 1"
proof-
  let ?uv = "inner u v"
  have "1 + ?uv > 0"
    using abs_inner_lt_1[OF assms]
    by fastforce
  then have "\<gamma> u * \<gamma> v * (1 + inner u v) > 0"
    using gamma_factor_positive[OF assms(1)] 
          gamma_factor_positive[OF assms(2)]
    by fastforce
  then have "0 < sqrt (1 - (cmod (oplus_e' u v))\<^sup>2)"
    using gamma_oplus_e'[OF assms] gamma_oplus_e'_not_zero[OF assms]
    by (metis zero_less_divide_1_iff)
  then have "(norm (oplus_e' u v))^2 < 1"
    using real_sqrt_gt_0_iff
    by simp
  then show ?thesis
    using real_less_rsqrt by force
qed

lemma gamma_factor_oplus_e':
  assumes "norm u < 1" "norm v < 1"
  shows "\<gamma> (oplus_e' u v) = (\<gamma> u) * (\<gamma> v) * (1 + inner u v)"
proof-
  have "\<gamma> (oplus_e' u v) = 1 / sqrt(1 - norm (oplus_e' u v)^2)"
    by (simp add: assms(1) assms(2) oplus_e'_in_unit_disc gamma_factor_def)
  then show ?thesis
    using assms
    using gamma_oplus_e' by force
qed



(* ------------------------------------------------------------------------------------- *)
  
definition ominus_e' :: "complex \<Rightarrow> complex" where
  "ominus_e' v = (if v \<in> {z. cmod z < 1} then - v else undefined)"                                      

lemma ominus_e'_in_unit_disc:
  assumes "norm z < 1"
  shows "norm (ominus_e' z) < 1"
  using assms
  unfolding ominus_e'_def
  by simp


lemma ominus_e_ominus_m:
  assumes "a\<in>{z. cmod z < 1}"
  shows "ominus_e' a = ominus_m' a"
  using assms ominus_e'_def ominus_m'_def by presburger
  

lemma ominus_e_scale:
  assumes "u\<in>{z. cmod z < 1}"
  shows "otimes' k (ominus_e' u) = ominus_e' (otimes' k u)"
  using Mobius_gyrospace_ax3 assms ominus_e_ominus_m ominus_m_scale by force
 
(* ------------------------------------------------------------------------------------- *)

lemma gamma_factor_p_positive:
  assumes "a\<in>{z. cmod z <1}"
  shows "\<gamma> a > 0"
  using assms gamma_factor_positive by blast
  

lemma gamma_factor_p_oplus_e:
  assumes "u\<in>{z. cmod z < 1}" "v\<in>{z. cmod z < 1}"
  shows "\<gamma> (oplus_e' u  v) = \<gamma> u * \<gamma> v * (1 + inner u v)"
  using gamma_factor_oplus_e' 
  using assms(1) assms(2) by blast

abbreviation \<gamma>\<^sub>2 :: "complex \<Rightarrow> real" where
  "\<gamma>\<^sub>2 u \<equiv> (if u\<in>{z. cmod z < 1} then \<gamma> u / (1 + \<gamma> u) else undefined)"

lemma norm_square_gamma_half_scale:
  assumes "norm u < 1"
  shows "(norm (\<gamma>\<^sub>2 u *\<^sub>R u))\<^sup>2 = (\<gamma> u - 1) / (1 + \<gamma> u)"
proof-
  have "(norm (\<gamma>\<^sub>2 u *\<^sub>R u))\<^sup>2 = (\<gamma>\<^sub>2 u)\<^sup>2 * (norm u)\<^sup>2"
    by (simp add: power2_eq_square)
  also have "\<dots> = (\<gamma>\<^sub>2 u)\<^sup>2 * ((\<gamma> u)\<^sup>2 - 1) / (\<gamma> u)\<^sup>2"
    using assms
    by (simp add: norm_square_gamma_factor')
  also have "\<dots> = (\<gamma> u)\<^sup>2 / (1 + \<gamma> u)\<^sup>2 * ((\<gamma> u)\<^sup>2 - 1) / (\<gamma> u)\<^sup>2"
    by (simp add: assms power_divide)
 
  also have "\<dots> = ((\<gamma> u)\<^sup>2 - 1) / (1 + \<gamma> u)\<^sup>2"
    using assms gamma_factor_positive 
    by fastforce
  also have "\<dots> = (\<gamma> u - 1) * (\<gamma> u + 1) / (1 + \<gamma> u)\<^sup>2"
    by (simp add: power2_eq_square square_diff_one_factored)
  also have "\<dots> = (\<gamma> u - 1) / (1 + \<gamma> u)"
    by (simp add: add.commute power2_eq_square)
  finally
  show ?thesis
    by simp
qed
  
lemma norm_half_square_gamma:
  assumes "norm u < 1"
  shows "(norm (half' u))\<^sup>2 = (\<gamma>\<^sub>2 u)\<^sup>2 * (cmod u)\<^sup>2"
  unfolding half'_def 
  using norm_square_gamma_half_scale assms
  by (smt (verit, best) divide_nonneg_nonneg gamma_factor_positive mem_Collect_eq norm_scaleR power_mult_distrib)
 
lemma norm_half_square_gamma':
  assumes "cmod u < 1"
  shows "(norm (half' u))\<^sup>2 = (\<gamma> u - 1) / (1 + \<gamma> u)"
  using assms
  using half'_def norm_square_gamma_half_scale
  by auto

lemma inner_half_square_gamma:
  assumes "cmod u < 1" "cmod v < 1"
  shows "inner (half' u) (half' v) = \<gamma>\<^sub>2 u * \<gamma>\<^sub>2 v * inner u v"
  unfolding half'_def scaleR_conv_of_real
  by (smt (z3) assms(1) assms(2) inner_commute inner_mult_right inner_real_def mem_Collect_eq)

lemma iso_me_help1:
  assumes "norm v < 1"
  shows "1 + (\<gamma> v - 1) / (1 + \<gamma> v) = 2 * \<gamma> v / (1 + \<gamma> v)"
proof-
  have "1 + \<gamma> v \<noteq> 0"
    using assms gamma_factor_positive
    by fastforce
  then show ?thesis 
    by (smt (verit, del_insts) diff_divide_distrib divide_self)
qed

lemma  iso_me_help2:
  assumes "norm v < 1"
  shows "1 - (\<gamma> v - 1) / (1 + \<gamma> v) = 2 / (1 + \<gamma> v)"
proof-
  have "1 + \<gamma> v \<noteq> 0"
    using assms gamma_factor_positive 
    by fastforce
  then show ?thesis 
    by (smt (verit, del_insts) diff_divide_distrib divide_self)
qed

lemma  iso_me_help3:
  assumes "norm v < 1" "norm u <1"
  shows "1 + ((\<gamma> v - 1) / (1 + \<gamma> v)) * ((\<gamma> u - 1) / (1 + \<gamma> u)) =
         2 * (1 + (\<gamma> u) * (\<gamma> v)) / ((1 + \<gamma> v) * (1 + \<gamma> u))" (is "?lhs = ?rhs")
proof-
  have *: "1 + \<gamma> v \<noteq> 0" "1 + \<gamma> u \<noteq> 0"
    using assms gamma_factor_positive by fastforce+
  have "(1 + \<gamma> v) * (1 + \<gamma> u) = 1 + (\<gamma> v) + (\<gamma> u) + (\<gamma> u)*(\<gamma> v)"
    by (simp add: field_simps)
  moreover 
  have "(\<gamma> v - 1) * (\<gamma> u - 1) =  (\<gamma> u)*(\<gamma> v) - (\<gamma> u) - (\<gamma> v) +1"
    by (simp add: field_simps)
  moreover 
  have "?lhs = ((1 + \<gamma> v) * (1 + \<gamma> u) + (\<gamma> u - 1) * (\<gamma> v - 1)) / ((1 + \<gamma> v) * (1 + \<gamma> u))"
    using *
    by (simp add: add_divide_distrib)
  ultimately show ?thesis 
    by (simp add: mult.commute)
qed

lemma half'_oplus_e':
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "half' (oplus_e' u v) = 
         \<gamma> u * \<gamma> v / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1) * (u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u)) * inner u v * u)"
proof-
  have "half' (oplus_e' u v) = 
       \<gamma> u * \<gamma> v * (1 + inner u v) / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1) *
       ((1 / (1 + inner u v)) * (u + (1 / \<gamma> u)*v + (\<gamma> u / (1 + \<gamma> u)) * inner u v * u))"
    unfolding half'_def
    unfolding gamma_factor_oplus_e'[OF assms] scaleR_conv_of_real
    unfolding oplus_e'_def scaleR_conv_of_real
    by (smt (verit, best) assms(1) assms(2) mem_Collect_eq oplus_e'_def oplus_e'_in_unit_disc scaleR_conv_of_real)
  then show ?thesis
    using assms
    by (smt (verit, best) ab_semigroup_mult_class.mult_ac(1) gamma_oplus_e' gamma_oplus_e'_not_zero inner_mult_left' inner_real_def mult.commute mult_eq_0_iff nonzero_mult_divide_mult_cancel_right2 of_real_1 of_real_divide of_real_mult real_inner_1_right times_divide_times_eq)
qed



lemma oplus_m'_half':
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "oplus_m' (half' u) (half' v) =
        (\<gamma> u * \<gamma> v / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1)) * 
        (u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u) * inner u v) * u)"
proof-
  have *: "\<gamma> u \<noteq> 0" "\<gamma> v \<noteq> 0" "1 + \<gamma> u \<noteq> 0" "1 + \<gamma> v \<noteq> 0"
    using assms gamma_factor_positive 
    by fastforce+

  let ?den = "(1 + \<gamma> v) * (1 + \<gamma> u)"
  let ?DEN = "\<gamma> u * \<gamma> v * (1 + inner u v) + 1"
  let ?NOM = "u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u) * inner u v) * u"

  have **: "cmod (half' u) < 1" "cmod (half' v) < 1"
    using assms
    using half_is_in_domain apply blast
    using assms(2) half_is_in_domain by blast
  then have "oplus_m' (half' u) (half' v) = oplus_m'_alternative (half' u) (half' v)"
    by (simp add: oplus_m'_alternative)
  also have "\<dots> = ((2 * \<gamma>\<^sub>2 v + 2 * \<gamma>\<^sub>2 v * \<gamma>\<^sub>2 u * inner u v) * \<gamma>\<^sub>2 u * u  +  2 * \<gamma> v / ?den * v) /
                  (2 * \<gamma> u * \<gamma> v * inner u v / ?den + 2 * (1 + \<gamma> u * \<gamma> v) / ?den)"
  proof-
    have "(1 + 2 * inner (half' u) (half' v) + (norm (half' v))\<^sup>2) *\<^sub>R (half' u) = 
          (2 * \<gamma>\<^sub>2 v + 2 * \<gamma> v * \<gamma> u / ?den * inner u v) * \<gamma>\<^sub>2 u * u"
    proof-
      have *: "half' u = (\<gamma> u / (1 + \<gamma> u)) * u"
        by (simp add: assms(1) half'_def scaleR_conv_of_real)
  
      have "1 + 2 * inner (half' u) (half' v) + (cmod (half' v))\<^sup>2 = 
            1 + 2 * (\<gamma>\<^sub>2 u * \<gamma>\<^sub>2 v * inner u v) + (\<gamma>\<^sub>2 v)\<^sup>2 * (cmod v)\<^sup>2"
        using inner_half_square_gamma norm_half_square_gamma assms
        by simp
      also have "\<dots> = 2 * \<gamma> v / (1 + \<gamma> v) + 2 * \<gamma> v * \<gamma> u / ?den * inner u v"
        using assms norm_half_square_gamma norm_square_gamma_half_scale[OF assms(2)] iso_me_help1[OF assms(2)] half'_def
        proof-
       have p: "\<gamma> u \<noteq> 0" "\<gamma> v \<noteq> 0" "1 + \<gamma> u \<noteq> 0" "1 + \<gamma> v \<noteq> 0"
         using assms gamma_factor_positive 
         by fastforce+
       moreover have " half' v = (\<gamma> v / (1 + \<gamma> v)) *\<^sub>R v"
          by (simp add: assms(2) half'_def)
       moreover  have " half' u = (\<gamma> u / (1 + \<gamma> u)) *\<^sub>R u"
         by (simp add: "*" scaleR_conv_of_real)
       moreover have "\<gamma>\<^sub>2 u = \<gamma> u / (1 + \<gamma> u)"
         using assms(1) by fastforce
      moreover have "\<gamma>\<^sub>2 v = \<gamma> v / (1 + \<gamma> v)"
         using assms(2) by fastforce
       ultimately show ?thesis 
         by (smt (verit, del_insts) \<open>(cmod (\<gamma>\<^sub>2 v *\<^sub>R v))\<^sup>2 = (\<gamma> v - 1) / (1 + \<gamma> v)\<close> \<open>1 + (\<gamma> v - 1) / (1 + \<gamma> v) = 2 * \<gamma> v / (1 + \<gamma> v)\<close> ab_semigroup_mult_class.mult_ac(1) add.commute assms(2) distrib_left divide_divide_eq_left dot_square_norm inner_scaleR_left inner_scaleR_right mem_Collect_eq mult.commute mult.left_commute mult.right_neutral mult_2_right power2_eq_square times_divide_eq_left times_divide_eq_right)
     qed
       finally
      show ?thesis
        using *
        by (simp add: assms(1) assms(2) scaleR_conv_of_real)
    qed
    moreover
    have "(1 - (norm (half' u))\<^sup>2)   *\<^sub>R (half' v) = 
         ( 2 * (\<gamma> v) / ?den) * v"
    proof-
      have "(norm (half' u))\<^sup>2 = (\<gamma> u - 1) / (1 + \<gamma> u) "
        using assms(1) norm_half_square_gamma' by blast
      moreover have "1 - (\<gamma> u - 1) / (1 + \<gamma> u) = 2/  (1 + \<gamma> u)"
        using assms(1) iso_me_help2 by blast
      ultimately show ?thesis 

        using half'_def mult.commute scaleR_conv_of_real
          proof-
       have p: "\<gamma> u \<noteq> 0" "\<gamma> v \<noteq> 0" "1 + \<gamma> u \<noteq> 0" "1 + \<gamma> v \<noteq> 0"
         using assms gamma_factor_positive 
         by fastforce+
       moreover have " half' v = (\<gamma> v / (1 + \<gamma> v)) *\<^sub>R v"
          by (simp add: assms(2) half'_def)
       moreover  have " half' u = (\<gamma> u / (1 + \<gamma> u)) *\<^sub>R u"
         by (simp add: assms(1) half'_def)
       moreover have "\<gamma>\<^sub>2 u = \<gamma> u / (1 + \<gamma> u)"
         using assms(1) by fastforce
      moreover have "\<gamma>\<^sub>2 v = \<gamma> v / (1 + \<gamma> v)"
        using assms(2) by fastforce
      ultimately show ?thesis 
      proof -
        have "(\<gamma> v * 2 / (1 + \<gamma> u) / (1 + \<gamma> v)) *\<^sub>R v = (2 / (1 + \<gamma> u)) *\<^sub>R half' v"
          by (simp add: \<open>half' v = (\<gamma> v / (1 + \<gamma> v)) *\<^sub>R v\<close>)
        then show ?thesis
          by (simp add: \<open>(cmod (half' u))\<^sup>2 = (\<gamma> u - 1) / (1 + \<gamma> u)\<close> \<open>1 - (\<gamma> u - 1) / (1 + \<gamma> u) = 2 / (1 + \<gamma> u)\<close> mult.commute of_real_def)
      qed
      qed
    qed
    moreover
    have"1 + 2 * inner (half' u) (half' v) + (cmod (half' u))\<^sup>2 * (cmod (half' v))\<^sup>2 =
         2 * \<gamma> u * \<gamma> v * inner u v / ?den + 2 * (1 + \<gamma> u * \<gamma> v) / ?den"
      using assms inner_half_square_gamma iso_me_help3 norm_half_square_gamma'
      by (simp add: field_simps)
    ultimately
    show ?thesis
       unfolding oplus_m'_alternative_def
       by (simp add: assms(1) assms(2))
  qed
  also have "\<dots> = (2 * \<gamma> v * \<gamma> u * u + 2 * \<gamma> v * \<gamma> u * inner u v * \<gamma>\<^sub>2 u * u + 2 * \<gamma> v * v) / 
                  (2 * \<gamma> u * \<gamma> v * inner u v + (2 + 2 * \<gamma> u * \<gamma> v))"
  proof-
    have "1 / ?den \<noteq> 0"
      using *
      by simp
    moreover 
    have "(2 * \<gamma>\<^sub>2 v + 2 * \<gamma>\<^sub>2 v * \<gamma>\<^sub>2 u * inner u v) * \<gamma>\<^sub>2 u * u + 2 * \<gamma> v / ?den * v =
           (1 / ?den) * (2 * \<gamma> v * \<gamma> u * u + 2 * \<gamma> v * \<gamma> u * inner u v * \<gamma>\<^sub>2 u * u + 2 * \<gamma> v * v)"
       proof-
       have p: "\<gamma> u \<noteq> 0" "\<gamma> v \<noteq> 0" "1 + \<gamma> u \<noteq> 0" "1 + \<gamma> v \<noteq> 0"
         using assms gamma_factor_positive 
         by fastforce+
       moreover have " half' v = (\<gamma> v / (1 + \<gamma> v)) *\<^sub>R v"
          by (simp add: assms(2) half'_def)
       moreover  have " half' u = (\<gamma> u / (1 + \<gamma> u)) *\<^sub>R u"
         by (simp add: assms(1) half'_def)
       moreover have "\<gamma>\<^sub>2 u = \<gamma> u / (1 + \<gamma> u)"
         using assms(1) by fastforce
      moreover have "\<gamma>\<^sub>2 v = \<gamma> v / (1 + \<gamma> v)"
        using assms(2) by fastforce
     
      ultimately show ?thesis
             by (simp add: mult.commute ring_class.ring_distribs(1))
         qed
    moreover 
    have "2 * \<gamma> u * \<gamma> v * inner u v / ?den + 2 * (1 + \<gamma> u * \<gamma> v) / ?den =
          (1 / ?den) * (2 * \<gamma> u * \<gamma> v * inner u v + (2 + 2 * \<gamma> u * \<gamma> v))"
      by argo
    ultimately 
    show ?thesis
      by (smt (verit, ccfv_threshold) divide_divide_eq_left' division_ring_divide_zero eq_divide_eq inner_commute inner_real_def mult_eq_0_iff mult_eq_0_iff nonzero_mult_divide_mult_cancel_left nonzero_mult_divide_mult_cancel_left numeral_One of_real_1 of_real_1 of_real_divide of_real_inner_1 of_real_mult one_divide_eq_0_iff real_inner_1_right times_divide_times_eq)
  qed
  also have "\<dots> = 2 * (\<gamma> v * \<gamma> u * u + \<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u) * u + \<gamma> v * v) / (2 * ?DEN)"
  proof-
    have "(cor (2 * \<gamma> v * \<gamma> u) * u + cor (2 * \<gamma> v * \<gamma> u * inner u v * \<gamma>\<^sub>2 u) * u +
     cor (2 * \<gamma> v) * v) /
    cor (2 * \<gamma> u * \<gamma> v * inner u v + (2 + 2 * \<gamma> u * \<gamma> v)) = 
( (2 * \<gamma> v * \<gamma> u) * u +  (2 * \<gamma> v * \<gamma> u * inner u v * \<gamma>\<^sub>2 u) * u +
     (2 * \<gamma> v) * v) /
     (2 * \<gamma> u * \<gamma> v * inner u v + (2 + 2 * \<gamma> u * \<gamma> v))"
      by meson
    moreover have "   2 *
    (cor (\<gamma> v * \<gamma> u) * u + cor (\<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u)) * u +
     cor (\<gamma> v) * v) /
    cor (2 * (\<gamma> u * \<gamma> v * (1 + inner u v) + 1)) =    2 *
    ( (\<gamma> v * \<gamma> u) * u +  (\<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u)) * u +
      (\<gamma> v) * v) /
     (2 * (\<gamma> u * \<gamma> v * (1 + inner u v) + 1))"
      by meson
    moreover have " \<gamma>\<^sub>2 u = \<gamma> u / (1 + \<gamma> u)"
      by (simp add: assms(1))
    moreover have "(2 * \<gamma> u * \<gamma> v * inner u v + (2 + 2 * \<gamma> u * \<gamma> v)) 
=  (2 * (\<gamma> u * \<gamma> v * (1 + inner u v) + 1))"
      by argo
    moreover have "(2 * \<gamma> v * \<gamma> u) * u +  (2 * \<gamma> v * \<gamma> u * inner u v * \<gamma>\<^sub>2 u) * u +
     (2 * \<gamma> v) * v =  2 *
    ( (\<gamma> v * \<gamma> u) * u +  (\<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u)) * u +
      (\<gamma> v) * v)" 
    proof-
      have "(2 * \<gamma> v * \<gamma> u) * u  =  2 *
    (\<gamma> v * \<gamma> u) * u " 
        by argo
      moreover have " (2 * \<gamma> v * \<gamma> u * inner u v * \<gamma>\<^sub>2 u) * u = 2 *  (\<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u)) * u"
        using \<open>\<gamma>\<^sub>2 u = \<gamma> u / (1 + \<gamma> u)\<close> by force
      moreover have "(2 * \<gamma> v) * v = 2 * (\<gamma> v) * v"
        by blast
      moreover have "(2::real) \<noteq> 0"
        by auto
      ultimately show ?thesis 
        by auto
    qed
    ultimately show ?thesis 
      by presburger
    qed
  also have "\<dots> = (\<gamma> v * \<gamma> u * u + \<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u) * u + \<gamma> v * v) / ?DEN"
    by (metis (no_types, opaque_lifting) nonzero_mult_divide_mult_cancel_left of_real_mult of_real_numeral zero_neq_numeral)
  also have "\<dots> = ((\<gamma> v * \<gamma> u) * u + (\<gamma> v * \<gamma> u) * (inner u v * \<gamma> u / (1 + \<gamma> u) * u) + (\<gamma> u * \<gamma> v) * (v / \<gamma> u)) / ?DEN"
    using \<open>\<gamma> u \<noteq> 0\<close>
    by simp
  also have "\<dots> = (\<gamma> v * \<gamma> u) * ?NOM / ?DEN"
  proof-
    have "(\<gamma> v * \<gamma> u) * u + (\<gamma> v * \<gamma> u) * (inner u v * \<gamma> u / (1 + \<gamma> u) * u) + (\<gamma> u * \<gamma> v) * (v / \<gamma> u) = (\<gamma> v * \<gamma> u) * ?NOM"
      by (simp add: field_simps)
    then show ?thesis
      by simp
  qed
  finally show ?thesis
    by simp
qed

lemma iso_me_oplus:
  assumes "u\<in>{z. cmod z < 1}" "v\<in>{z. cmod z < 1}"
  shows "otimes' (1/2)  (oplus_e' u v) = oplus_m' (otimes' (1/2) u) (otimes' (1/2)  v)"
proof-
  have "otimes' (1 / 2) (oplus_e' u v) = half' (oplus_e' u v)"
    using assms(1) assms(2) half' oplus_e'_in_unit_disc by force
   
  moreover
  have "otimes' (1 / 2) u = half' u" "otimes' (1 / 2) v = half' v"
    using assms(1) half apply presburger
    using assms(2) half by auto
  moreover
  have "half' (oplus_e' u v) = oplus_m' (half' u) (half' v)"
    using assms(1) assms(2) half'_oplus_e' oplus_m'_half' by auto
  ultimately
  show "otimes' (1 / 2) (oplus_e' u v) = oplus_m' (otimes' (1 / 2) u) (otimes' (1 / 2) v)"
    by simp
qed

lemma oplus_e_oplus_m:
  assumes "u\<in>{z. cmod z < 1}" "v\<in>{z. cmod z < 1}"
  shows "oplus_e' u  v = otimes' 2 (oplus_m' (otimes' (1/2) u) (otimes' (1/2)  v))"
  by (metis assms(1) assms(2) half iso_me_oplus mem_Collect_eq oplus_e'_in_unit_disc otimes_2_half)

definition oplus_e::"complex \<Rightarrow> complex \<Rightarrow> complex" where
  "oplus_e u v = (if u\<in>{z. cmod z < 1}\<and>v\<in>{z. cmod z < 1} then oplus_e' u v else
undefined)"

definition gyr_e'::"complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex" where
 "gyr_e' u v w =
(if u\<in>{z. cmod z < 1} \<and> v\<in>{z. cmod z < 1} \<and> w\<in>{z. cmod z < 1} then
 oplus_e' (ominus_e' (oplus_e' u v))  (oplus_e' u  (oplus_e' v w)) else undefined)"


lemma two_plus_is_oplus_e'_help1:
  assumes "u\<in>{z. cmod z < 1}" "v\<in>{z. cmod z < 1}"
  shows "two_plus u v =  otimes' 2 (oplus_m' (otimes' (1/2) u) (otimes' (1/2)  v))"
  using two_plus_def
  using assms(1) assms(2) by force

lemma two_plus_is_oplus_e':
  shows "two_plus = oplus_e"
proof-
  have "\<forall>a. \<forall>b. (two_plus a b = oplus_e a b)"
    by (simp add: oplus_e_def oplus_e_oplus_m two_plus_def)
  then show ?thesis 
    by presburger
qed

lemma iso_me_gyr:
  assumes "u\<in>{z. cmod z < 1}" "v\<in>{z. cmod z < 1}" "w\<in>{z. cmod z < 1}"
  shows "otimes' (1/2) (gyr_e' u v w) = gyr_m' (otimes' (1/2) u) (otimes' (1/2) v) (otimes' (1/2)  w)"
proof-
  let ?u = "(otimes' (1/2) u)"
  let ?v = "(otimes' (1/2) v)"
  let ?w = "(otimes' (1/2) w)"
  have "gyr_m' (otimes' (1/2) u) (otimes' (1/2) v) (otimes' (1/2)  w) =
  oplus_m' (ominus_m' (oplus_m' ?u ?v)) (oplus_m' ?u (oplus_m' ?v ?w))"
    by (meson Mobius_gyrospace_ax3 Moebius_gyrogroup.gyrogroup_axioms assms(1) assms(2) assms(3) gyrogroup.gyr_def)
  moreover have "(if u \<in> {z. cmod z < 1} \<and> v \<in> {z. cmod z < 1} \<and> w \<in> {z. cmod z < 1}
      then oplus_e' (ominus_e' (oplus_e' u v)) (oplus_e' u (oplus_e' v w))
      else undefined) = oplus_e' (ominus_e' (oplus_e' u v)) (oplus_e' u (oplus_e' v w))"
    using assms(1) assms(2) assms(3) by presburger
  ultimately show ?thesis 
unfolding gyr_e'_def gyr_m'_def
  using iso_me_oplus ominus_e_ominus_m ominus_e_scale
  using Mobius_gyrospace_ax3 assms(1) assms(2) assms(3) ominus_e'_in_unit_disc oplus_e'_in_unit_disc by auto
qed

lemma gyr_e_gyr_m:
 assumes "u\<in>{z. cmod z < 1}" "v\<in>{z. cmod z < 1}" "w\<in>{z. cmod z < 1}"
  shows "gyr_e' u v w = otimes' 2  (gyr_m' (otimes' (1/2) u) (otimes' (1/2) v) (otimes' (1/2)  w))"
proof-
  have "(gyr_e' u v w) \<in> {z. cmod z < 1}"
    using assms(1) assms(2) assms(3) gyr_e'_def ominus_e'_in_unit_disc oplus_e'_in_unit_disc by auto
  then show ?thesis
 using iso_me_gyr[OF assms] half[OF assms(1)]
half[OF assms(2)] half[OF assms(3)] otimes_2_half[OF assms(1)]
otimes_2_half[OF assms(2)] otimes_2_half[OF assms(3)]
    using \<open>otimes' (1 / 2) (gyr_e' u v w) = gyr_m' (otimes' (1 / 2) u) (otimes' (1 / 2) v) (otimes' (1 / 2) w)\<close> half otimes_2_half by force
qed

lemma gyr_e_equal:
  shows "(\<lambda> a b c. (if ((a\<in>{z. cmod z < 1}) \<and> (b\<in>{z. cmod z < 1})\<and> (c\<in>{z. cmod z < 1})) 
then  otimes'  2  (gyr_m'  (otimes' (1/2)  a) ( otimes' (1/2)  b) (otimes' (1/2)  c)) 
else undefined)) = gyr_e'"
  using gyr_e'_def gyr_e_gyr_m by fastforce

lemma Einstein_normed_ok2:
  shows " normed_gyrolinear_space {z. cmod z < 1} 0 oplus_e
  (\<lambda>x. if x \<in> {z. cmod z < 1} then ominus_m' x else undefined)
  gyr_e'
  (\<lambda>r a. if a \<in> {z. cmod z < 1} then otimes' r a else undefined)
  (\<lambda>x. if x \<in> {z. cmod z < 1} then cmod x else undefined)
  (\<lambda>x. if x \<in> cmod ` {z. cmod z < 1} then \<bar>1 / 2\<bar> * artanh x else undefined)"
  using Einstein_normed_ok gyr_e_equal two_plus_is_oplus_e' by argo

interpretation Einstein_gyrocommutative_gyrogroup: gyrocommutative_gyrogroup "{z::complex. cmod z < 1}" 0 oplus_e "(\<lambda>x. (if x \<in>{z. cmod z < 1} then ominus_m' x else undefined))"
gyr_e'
  using Einstein_normed_ok2 gyrocommutative_gyrogroup_def gyrolinear_space.axioms(1) normed_gyrolinear_space_def by fastforce



lemma Mobius_gyro_iso_lemma:
  shows "gyro_iso {z. cmod z < 1} 0 oplus_m' ominus_m' gyr_m' otimes'
cmod artanh id"
proof-
  have "normed_gyrolinear_space {z. cmod z < 1} 0 oplus_m' ominus_m' gyr_m' otimes' cmod artanh"
    using Mobius_gyrolinear.normed_gyrolinear_space_axioms by linarith
  moreover have "\<forall>a\<in>{z. cmod z <1}. cmod a = (\<lambda>x. (cmod ((\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined) x))) a"
    by force
  ultimately show ?thesis 

    by (metis gyro_iso.intro gyro_iso_axioms_def id_apply)
qed


interpretation Mobius_gyro_iso: gyro_iso "{z. cmod z < 1}" 0 oplus_m' ominus_m' gyr_m' otimes'
cmod artanh id
  using Mobius_gyro_iso_lemma by blast
     
lemma zero_smaller_half:
  shows "(0::real) < (1/2)"
  by simp

lemma oplus_e_equal:
  shows " \<forall>a b. oplus_e a b =
        (if a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1}
         then otimes' (1 / (1 / 2))
               (oplus_m' (otimes' (1 / 2) a) (otimes' (1 / 2) b))
         else undefined)"
  using oplus_e_def
  using two_plus_def two_plus_is_oplus_e' by auto

lemma vector_space_for_e:
  shows "gyrovector_space {z. cmod z < 1} 0 oplus_m' ominus_m' gyr_m' otimes'
   Mobius_gyro_iso.oplus' Mobius_gyro_iso.smult' 0"
  (* (\<lambda>x. if x \<in> {z. cmod z < 1} then x else undefined)"*)
  using Mobius_is_gyrospace
proof-
  have "Mobius_gyro_iso.f' = artanh'"
 using Mobius_gyro_iso.f'_def artanh'_def
  by argo
  moreover have " Mobius_gyrolinear.norms_all = cmod_norms_all"
    using Mobius_gyrolinear.norms_all_def Mobius_gyrolinear.norms_def Mobius_gyrolinear.norms_neg_def cmod_norms_all_def by argo
  moreover have " Mobius_gyro_iso.oplus'  = mobius_oplus'"
    using  Mobius_gyro_iso.oplus'_def mobius_oplus'_def
    using Mobius_gyro_iso.f'_def artanh'_def
    using calculation(2) by presburger
  moreover have " Mobius_gyro_iso.smult' = mobius_otimes'"
    using  Mobius_gyro_iso.smult'_def mobius_otimes'_def
    using calculation(1) calculation(2)
    by presburger
  ultimately show ?thesis 
    using Mobius_is_gyrospace by argo
qed

lemma ggv_vector_space_for_e:
  shows "ggv_space {z. cmod z < 1} 0 oplus_m' ominus_m' gyr_m' otimes'
   Mobius_gyro_iso.oplus' Mobius_gyro_iso.smult' id 0"
  using  vector_space_for_e gspace_id_is_ggv_space
  by blast
  
  
lemma Einstein_is_gyrospace:
  shows " ggv_space {z. cmod z < 1} 0 oplus_e  (\<lambda>x. if x \<in> {z. cmod z < 1} then ominus_m' x else undefined) gyr_e' (\<lambda>r a. if a \<in> {z. cmod z < 1} then otimes' r a else undefined)
mobius_oplus' mobius_otimes' id  0 " (* (\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined)"*)
  using Mobius_gyro_iso.proposition_3_11_gyrospace[of "1/2" oplus_e, OF zero_smaller_half  oplus_e_equal
  ggv_vector_space_for_e]
proof-
have "Mobius_gyro_iso.f' = artanh'"
 using Mobius_gyro_iso.f'_def artanh'_def
  by argo
  moreover have " Mobius_gyrolinear.norms_all = cmod_norms_all"
    using Mobius_gyrolinear.norms_all_def Mobius_gyrolinear.norms_def Mobius_gyrolinear.norms_neg_def cmod_norms_all_def by argo
  moreover have " Mobius_gyro_iso.oplus'  = mobius_oplus'"
    using  Mobius_gyro_iso.oplus'_def mobius_oplus'_def
    using Mobius_gyro_iso.f'_def artanh'_def
    using calculation(2) by presburger
  moreover have " Mobius_gyro_iso.smult' = mobius_otimes'"
    using  Mobius_gyro_iso.smult'_def mobius_otimes'_def
    using calculation(1) calculation(2)
    by presburger
  ultimately show ?thesis 

  proof -
    show ?thesis
      
      by (metis (lifting) ext \<open>Mobius_gyro_iso.oplus' = mobius_oplus'\<close>
          \<open>Mobius_gyro_iso.smult' = mobius_otimes'\<close>
          \<open>ggv_space {z. cmod z < 1} 0 oplus_e (\<lambda>x. if x \<in> {z. cmod z < 1} then ominus_m' x else undefined) (\<lambda>a b c. if a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1} \<and> c \<in> {z. cmod z < 1} then otimes' (1 / (1 / 2)) (gyr_m' (otimes' (1 / 2) a) (otimes' (1 / 2) b) (otimes' (1 / 2) c)) else undefined) (\<lambda>r a. if a \<in> {z. cmod z < 1} then otimes' r a else undefined) Mobius_gyro_iso.oplus' Mobius_gyro_iso.smult' id 0\<close>
          div_by_1[of "2"] divide_divide_eq_right[of "1" "1" "2"] gyr_e_equal
          mult_cancel_right2[of "1" "2"])
  qed
qed





lemma einstein_gyroauto:
  assumes "u\<in>{z. cmod z < 1}" "v\<in>{z. cmod z < 1}" "a\<in>{z. cmod z < 1}"
    "b\<in>{z. cmod z < 1}"
  shows "inner (gyr_e' u v a)  (gyr_e' u v b) = inner a b"
  using moebius_gyroauto
proof-
  have "otimes'  2  (gyr_m'  (otimes' (1/2)  u) ( otimes' (1/2)  v) (otimes' (1/2)  a))  = gyr_e' u v a"
    using assms(1,2,3) gyr_e_gyr_m by presburger
  moreover have "otimes'  2  (gyr_m'  (otimes' (1/2)  u) ( otimes' (1/2)  v) (otimes' (1/2)  b))  = gyr_e' u v b"
    using assms(1,2,4) gyr_e_gyr_m by presburger
  ultimately show ?thesis using moebius_gyroauto
    by (metis (no_types, lifting) Mobius_gyrospace_ax3 assms(1,2,3,4)
        gyr_m_gyrospace2 half otimes_2_half)
qed

interpretation Einstein_gyrospace: gyrovector_space "{z. cmod z < 1}" 0 oplus_e  "(\<lambda>x. if x \<in> {z. cmod z < 1} then ominus_m' x else undefined)" gyr_e' "(\<lambda>r a. if a \<in> {z. cmod z < 1} then otimes' r a else undefined)"
mobius_oplus' mobius_otimes' 0
  using ggv_space_id_is_gspace[OF Einstein_is_gyrospace]
einstein_gyroauto
  by blast



end
