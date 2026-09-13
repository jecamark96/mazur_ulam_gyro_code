theory MobiusGyroVectorSpace
  imports Main MobiusGyroGroup  NGL  GammaFactor HyperbolicFunctions
 HOL.Transcendental GGV GV
begin

(* --------------------------------------------------------- *)
definition otimes'_k :: "real \<Rightarrow> complex \<Rightarrow> real" where
  "otimes'_k r z = ((1 + cmod z) powr r - (1 - cmod z) powr r) /
                   ((1 + cmod z) powr r + (1 - cmod z) powr r)" 


lemma otimes'_k_tanh: 
  assumes "cmod z < 1"
  shows "otimes'_k r z = tanh (r * artanh (cmod z))"
proof-
  have "0 < 1 + cmod z"
    by (smt norm_not_less_zero)
  hence "(1 + cmod z) powr r \<noteq> 0"
    by auto

  have "1 - (1 - cmod z) powr r / (1 + cmod z) powr r = 
        ((1 + cmod z) powr r - (1 - cmod z) powr r) / (1 + cmod z) powr r"
    by (smt \<open>(1 + cmod z) powr r \<noteq> 0\<close> add_divide_distrib divide_self)
  moreover
  have "1 + (1 - cmod z) powr r / (1 + cmod z) powr r =
       ((1 + cmod z) powr r + (1 - cmod z) powr r) / (1 + cmod z) powr r"
    by (smt add_divide_distrib calculation)
  moreover
  have "exp (- (r * ln ((1 + cmod z) / (1 - cmod z)))) =
         ((1 + cmod z) / (1 - cmod z)) powr (-r)" 
    using `0 < 1 + cmod z` ln_powr[symmetric, of "(1 + cmod z) / (1 - cmod z)" "-r"]
    using assms
    by (simp add: powr_def)

  ultimately
  show ?thesis
    using assms powr_divide[of "1 + cmod z" "1 - cmod z" r]
    using `0 < 1 + cmod z` `(1 + cmod z) powr r \<noteq> 0`
    unfolding otimes'_k_def tanh_real_altdef artanh_def
    by (simp add: powr_minus_divide)
qed

lemma cmod_otimes'_k: 
  assumes "cmod z < 1"
  shows "cmod (otimes'_k r z) < 1"
  by (smt assms divide_less_eq_1_pos divide_minus_left otimes'_k_def norm_of_real powr_gt_zero zero_less_norm_iff)

definition otimes' :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  "otimes' r z = (if z = 0 then 0 else cor (otimes'_k r z) * (z / cmod z))"

lemma cmod_otimes':
  assumes "cmod z < 1"
  shows "cmod (otimes' r z) = abs (otimes'_k r z)"
proof (cases "z = 0")
  case True
  thus ?thesis
    by (simp add: otimes'_def otimes'_k_def)
next
  case False
  hence "cmod (cor (otimes'_k r z)) = abs (otimes'_k r z)"
    by simp
  then show ?thesis
    using False
    unfolding otimes'_def
    by (simp add: norm_divide norm_mult)
qed




lemma otimes_distrib_lemma':
  fixes "ax" "bx" "ay" "by" :: real
  assumes "ax + bx \<noteq> 0" "ay + by \<noteq> 0"
  shows "(ax * ay - bx * by) / (ax * ay + bx * by) = 
         ((ax - bx)/(ax + bx) + (ay - by)/(ay + by)) / 
          (1 + ((ax - bx)/(ax + bx))*((ay - by)/(ay + by)))" (is "?lhs = ?rhs")
proof-
  have "(ax - bx)/(ax + bx) + (ay - by)/(ay + by) = ((ax - bx)*(ay + by) + (ay - by)*(ax + bx)) / ((ax + bx)*(ay + by))"
    by (simp add: \<open>ax + bx \<noteq> 0\<close> \<open>ay + by \<noteq> 0\<close> add_frac_eq)
  hence 1: "(ax - bx)/(ax + bx) + (ay - by)/(ay + by) = 2 * (ax * ay - bx * by) / ((ax + bx)*(ay + by))"
    by (simp add: field_simps)

  have "1 + ((ax - bx)/(ax + bx))*((ay - by)/(ay + by)) = 
        (((ax + bx)*(ay + by)) + (ax - bx)*(ay - by))/((ax + bx)*(ay + by))"
    by (simp add: \<open>ax + bx \<noteq> 0\<close> \<open>ay + by \<noteq> 0\<close> add_divide_distrib)
  hence 2: "1 + ((ax - bx)/(ax + bx))*((ay - by)/(ay + by)) = 2 * (ax * ay + bx * by) / ((ax + bx)*(ay + by))"
    by (simp add: field_simps)

  have "?rhs = 2 * (ax * ay - bx * by) / ((ax + bx) * (ay + by)) /
              (2 * (ax * ay + bx * by) / ((ax + bx) * (ay + by)))"
    by (subst 1, subst 2, simp)
  also have "\<dots> = (2 * (ax * ay - bx * by) * ((ax + bx) * (ay + by))) /
                  (2 * ((ax + bx) * (ay + by)) * (ax * ay + bx * by))"
    by auto
  also have "\<dots> = ((2 * ((ax + bx) * (ay + by))) * (ax * ay - bx * by)) / 
                  ((2 * ((ax + bx) * (ay + by))) * (ax * ay + bx * by))"
    by (simp add: field_simps)
  also have "\<dots> = (ax * ay - bx * by) / (ax * ay + bx * by)"
    using \<open>ax + bx \<noteq> 0\<close> \<open>ay + by \<noteq> 0\<close> by auto
  finally
  show ?thesis
    by simp                                                                                 
qed

lemma otimes_distrib_lemma:
  assumes "cmod a < 1"
  shows "otimes'_k (r1 + r2) a = oplus_m' (otimes'_k r1 a) (otimes'_k r2 a)"
  unfolding otimes'_k_def oplus_m'_def
  unfolding powr_add
  apply (subst otimes_distrib_lemma')
  apply (smt powr_gt_zero powr_non_neg)
  apply (smt powr_gt_zero powr_non_neg)
  apply simp
  done

lemma moebius_gyroauto:
  assumes "u\<in>{z. cmod z < 1}" "v\<in>{z. cmod z < 1}" "a\<in>{z. cmod z < 1}"
    "b\<in>{z. cmod z < 1}"
  shows "inner (gyr_m' u v a)  (gyr_m' u v b) = inner a b"
proof-
  have "inner (gyr_m' u v a) (gyr_m' u v b) = Re((cnj ( (gyr_m' u v a))) * ( (gyr_m' u v b)))"
    using inner_def2 by presburger

  moreover have "gyr_m' u v a = (1 + u * cnj v) / (1 + (cnj u) * v) *
    a"
    using gyr_m'_def by presburger
  moreover have "gyr_m' u v b = (1 +  u * cnj v) / (1 + (cnj u) * v) *
     b"
    using gyr_m'_def by blast
  moreover have "(cnj (gyr_m' u v a)) = cnj ((1 + u * cnj v) / (1 + (cnj u) * v)) *
    cnj a"
    using complex_cnj_mult gyr_m'_def by presburger
  moreover have " (cnj ((1 + u * cnj  v) / (1 +  v*cnj  u))*  ((1  + u* cnj v) / (1 +  v*(cnj  u)))) = 1"
    by (metis assms(1) assms(2) cmod_mix_cnj cnj_cmod_1 mem_Collect_eq mult.commute)

  moreover have "inner (gyr_m' u v a) ( gyr_m' u v b) = Re((cnj  a* b))"
    using calculation(1) calculation(3) calculation(4) calculation(5) by auto
  moreover have "inner a  b = Re((cnj  a)* b)"
    using inner_def2 by blast
  ultimately show ?thesis
    by presburger
qed




lemma otimes_oplus_m_distrib:
  assumes "a\<in>{z. cmod z < 1}"
  shows "otimes' (r1 + r2) a = oplus_m' (otimes' r1 a) (otimes' r2 a)" 
proof-
  have "a=0 \<or> a\<noteq>0"
    by blast
  moreover {
    assume "a=0"
    then have ?thesis
      by (simp add: otimes'_def oplus_m'_def)
  } moreover {
    assume "a\<noteq>0"
    let ?p = "1 + cmod a" and ?m = "1 - cmod a"
    have "cor (otimes'_k (r1 + r2) a) * a / cor (cmod a) = 
          oplus_m' (otimes'_k r1 a) (otimes'_k r2 a) * a / cor (cmod a)"
      using assms otimes_distrib_lemma by auto
    moreover
    have "cor (otimes'_k r1 a) * cnj a * (cor (otimes'_k r2 a) * a) / (cor (cmod a) * cor (cmod a)) = 
          cor (otimes'_k r1 a) * cor (otimes'_k r2 a)"
      by (smt (verit) \<open>a \<noteq> 0\<close> complex_cnj_complex_of_real complex_cnj_zero_iff complex_norm_square mult.commute nonzero_mult_div_cancel_right norm_ge_zero norm_of_real times_divide_times_eq)
    ultimately
    have ?thesis
      unfolding otimes'_def oplus_m'_def
      by (smt (verit, del_insts) \<open>a \<noteq> 0\<close> complex_cnj_complex_of_real complex_cnj_divide complex_cnj_mult distrib_right times_divide_eq_left times_divide_eq_right times_divide_times_eq)
  }
  ultimately show ?thesis 
    by fastforce
qed



lemma otimes_assoc:
  assumes "a\<in>{z. cmod z < 1}"
shows "otimes' (r1 * r2)  a = otimes' r1 (otimes' r2  a)"
proof-
  have "cmod a < 1"
    using assms by blast
  then show "otimes' (r1 * r2) a = otimes' r1 (otimes' r2 a)"
  proof (cases "a = 0")
    case True
    then show ?thesis
      by (simp add: otimes'_def)
  next
    case False
    show ?thesis
    proof (cases "r2 = 0")
      case True
      thus ?thesis
        using assms otimes'_def otimes'_k_tanh by force
    next
      case False
      let ?a2 = "otimes' r2 a"
      let ?k2 = "otimes'_k r2 a"
      have "cmod ?a2 = abs ?k2"
        using assms cmod_otimes' by blast
      hence "cmod ?a2 < 1"
        using assms cmod_otimes'_k by auto
      have "(1 + cmod a) / (1 - cmod a) > 1"
        using `a \<noteq> 0`
        using assms by auto
      hence "artanh (cmod a) > 0"
        by (simp add: artanh_def)
      hence "?k2 \<noteq> 0"
        using False assms otimes'_k_tanh by auto
      hence "?a2 \<noteq> 0"
        using `a \<noteq> 0`
        unfolding otimes'_def
        by simp
      have "sgn ?k2 = sgn r2"
        using otimes'_k_tanh[OF `cmod a < 1`, of r2]
        by (smt \<open>0 < artanh (cmod a)\<close> \<open>cmod ?a2 = \<bar>?k2\<bar>\<close> \<open>?a2 \<noteq> 0\<close> mult_nonneg_nonneg mult_nonpos_nonneg sgn_neg sgn_pos tanh_0 tanh_real_neg_iff zero_less_norm_iff)
      have "otimes' r1 (otimes' r2 a) = 
             cor (otimes'_k r1 (cor ?k2 * a / cor (cmod a))) *
             (cor ?k2 * a) / (cor (cmod a) * abs ?k2)"
        using False `?a2 \<noteq> 0`
        using \<open>cmod ?a2 = \<bar>?k2\<bar>\<close> 
        unfolding otimes'_def
        by auto
      also have "... = cor (tanh (r1 * \<bar>r2 * artanh (cmod a)\<bar>)) *  
                 (cor ?k2 * a) / (cor (cmod a) * abs ?k2)"
        using cmod_otimes'[of a r2] `cmod a < 1` `a \<noteq> 0`
        unfolding otimes'_def
        using \<open>cmod ?a2 < 1\<close> \<open>cmod ?a2 = \<bar>?k2\<bar>\<close> otimes'_k_tanh 
        using \<open>cmod a < 1\<close> otimes'_k_tanh[of a r2]
        by (simp add: artanh_abs_tanh)
      also have "... = cor (tanh (r1 * \<bar>r2\<bar> * artanh (cmod a))) *  
                 (cor ?k2 * a) / (cor (cmod a) * abs ?k2)"
        using `artanh (cmod a) > 0`
        by (smt ab_semigroup_mult_class.mult_ac(1) mult_minus_left mult_nonneg_nonneg)
      also have "... = cor (tanh (r1 * \<bar>r2\<bar> * artanh (cmod a))) * sgn ?k2 * (a / cor (cmod a))"
        by (simp add: mult.commute real_sgn_eq)
      also have "... = cor (tanh (r1 * \<bar>r2\<bar> * artanh (cmod a))) * sgn r2 * (a / cor (cmod a))"
        using `sgn ?k2 = sgn r2`
        by simp
      also have "... = cor (tanh (r1 * r2 * artanh (cmod a))) * (a / cor (cmod a))"
        by (cases "r2 \<ge> 0") auto
      finally show ?thesis
        by (simp add: \<open>cmod a < 1\<close> otimes'_def otimes'_k_tanh)
    qed
  qed
qed


lemma gamma_factor_eq1_lemma1:
  shows "cmod(1 + cnj a * b)*cmod(1 + cnj a * b) - cmod(a+b)*cmod(a+b) =
         (1 - cmod a * cmod a) * (1 - cmod b * cmod b)"
proof-
  have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) = (1+(cnj a)*b) * cnj(1+(cnj a)*b)"
    by (metis complex_norm_square power2_eq_square)
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) = (1+(cnj a)*b)*(1+(cnj(cnj a))* (cnj b))"
    using complex_cnj_add complex_cnj_mult complex_cnj_one by presburger
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b)= 1+a*(cnj b)+(cnj a)*b + (cnj a)*b*a*(cnj b)"
    by (simp add: field_simps)
  moreover 
  have "cmod(a+b)*cmod(a+b) = (a+b)*cnj(a+b)"
    by (metis complex_norm_square power2_eq_square)
  then have "cmod(a+b)*cmod(a+b) = a*(cnj a) + a*(cnj b) + b*(cnj a) + b*(cnj b)"
    by (simp add: field_simps)
  then have "cmod(a+b)*cmod(a+b) = cmod(a)*cmod(a) + a*(cnj b) + b*(cnj a) + cmod(b)*cmod(b)"
    by (metis complex_norm_square power2_eq_square)
  ultimately have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = 
    (1+a*(cnj b)+(cnj a)*b + (cnj a)*b*a*(cnj b))-( cmod(a)*cmod(a) + a*(cnj b) + b*(cnj a) + cmod(b)*cmod(b))"
    by auto
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cnj a)*a*(b*(cnj b)) - cmod(a)*cmod(a) - cmod(b)*cmod(b))"
    by fastforce
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cmod(a)*cmod(a))*(b*(cnj b))-cmod(a)*cmod(a) - cmod(b)*cmod(b))"
    by (metis (mono_tags, opaque_lifting) complex_norm_square mult.assoc mult.left_commute power2_eq_square)
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cmod(a)*cmod(a))*(cmod(b)*cmod(b))-cmod(a)*cmod(a) - cmod(b)*cmod(b))"
    by (smt (verit) Re_complex_of_real cmod_power2 complex_In_mult_cnj_zero complex_mod_cnj complex_mod_mult_cnj diff_add_cancel cnj_cmod norm_mult norm_zero of_real_1 plus_complex.sel(1) times_complex.sel(1))
  moreover
  have "(1-cmod(a)*cmod(a))*(1-cmod(b)*cmod(b)) = 1+(cmod(a)*cmod(a))*(cmod(b)*cmod(b))-cmod(a)*cmod(a)-cmod(b)*cmod(b)"
    by (simp add: field_simps)
  ultimately
  show ?thesis 
    by presburger
qed



lemma gyr_m_gyrospace:
  fixes r1::real 
  fixes r2::real
  assumes "v\<in>{z. cmod z < 1}"
  shows "\<forall>x\<in>{z. cmod z < 1}. gyr_m' (otimes' r1 v) (otimes' r2 v) x = x"
proof-
  have "\<forall>x\<in>{z. cmod z < 1}. gyr_m' (otimes' r1 v) (otimes' r2  v) x = x"
  proof
    fix x
    assume "x\<in>{z. cmod z < 1}"
    show " gyr_m' (otimes' r1 v) (otimes' r2  v) x = x"
    proof-
    let ?v = "v"
    let ?e1 = "?v * tanh (r1 * artanh (cmod ?v)) /cmod(v)"
    let ?e2 = "?v * tanh (r2 * artanh (cmod ?v)) /cmod(v)"

    have "otimes' r1  v = ?e1"
         "otimes' r2  v = ?e2"

    
      using assms otimes'_def otimes'_k_tanh by auto
    moreover

    have "cnj ?e1 = cnj ?v * cnj (tanh (r1 * artanh (cmod ?v))) / cmod ?v"
         "cnj ?e2 = cnj ?v * cnj (tanh (r2 * artanh (cmod ?v))) / cmod ?v"
        by auto

    moreover

    have "(1 + ?e1 * (cnj ?e2)) / (1 + ?e2 * (cnj ?e1)) = 1"
    proof-
      have "1 + ?e1 * (cnj ?e2) = 1 + ?e2 * (cnj ?e1)"
        by simp
      moreover
      have "1 + ?e2 * (cnj ?e1) \<noteq> 0"
        using \<open>otimes' r1  v = ?e1\<close> \<open>otimes' r2  v = ?e2\<close>
        by (smt (verit, ccfv_threshold) cmod_mix_cnj div_0 mult_eq_0_iff nonzero_mult_div_cancel_left norm_divide norm_ge_zero norm_of_real of_real_0 tanh_real_gt_neg1 tanh_real_lt_1)
      ultimately
      show ?thesis
        by simp
    qed

    ultimately show ?thesis 
      by (metis gyr_m'_def lambda_one mult.commute)
  qed
qed
  then show ?thesis  by blast
qed

   

lemma gyr_m_gyrospace2:
  assumes "u\<in>{z. cmod z <1 }" "v\<in>{z. cmod z <1 }" "a\<in>{z. cmod z <1 }"
  shows "gyr_m' u v (otimes' r a) = otimes' r  (gyr_m' u v a)"
proof-
  let ?u = "u" and ?v = "v" and ?a = "a"
  let ?e1 = "gyr_m' u v a"
  let ?e2 = "cmod ?e1"

  have "?e1 = (1 + ?u * cnj ?v) / (1 + cnj ?u *?v) * ?a"
    using gyr_m'_def by blast
  then have "?e2 = cmod ((1 + ?u * cnj ?v) / (1 + cnj ?u *?v)) * cmod ?a"
    by (metis norm_mult)
  then have "?e2 = cmod ?a"
    by (metis assms(1) assms(2) cmod_mix_cnj mem_Collect_eq mult.commute mult_cancel_right1)
  then have "otimes' r  ?e1 = (((1+cmod ?a) powr r - (1-cmod ?a) powr r) /
                                    ((1+cmod ?a) powr r + (1-cmod ?a) powr r) *  ?e1 / ?e2)"
    by (simp add: otimes'_def otimes'_k_def)
 
  then have "otimes' r ?e1 = ((otimes' r  a) * ((1 + ?u * cnj ?v) / (1 + cnj ?u * ?v)))"
    by (smt (verit) \<open>cmod (gyr_m' u v a) = cmod a\<close> \<open>gyr_m' u v a = (1 + u * cnj v) / (1 + cnj u * v) * a\<close> divide_divide_eq_right mult.commute mult_zero_right otimes'_def otimes'_k_def times_divide_eq_left)
  then show ?thesis 
    by (simp add: gyr_m'_def)
qed

interpretation Mobius_gyrolinear: gyrolinear_space "{z. cmod z < 1}" 0 oplus_m' ominus_m' gyr_m' otimes'
proof
  show "\<forall>r. \<forall>x\<in>{z. cmod z < 1}. otimes' r x \<in> {z. cmod z < 1}"
    using cmod_otimes' cmod_otimes'_k by auto
next
  show " \<forall>a\<in>{z. cmod z < 1}. otimes' 1 a = a"
  proof
    fix a
    assume "a\<in>{z. cmod z < 1}"
    show "otimes' 1 a = a"
    proof-
      have "a=0\<or> a\<noteq>0"
        by blast
      moreover {
        assume "a=0"
        then have ?thesis
          by (simp add: otimes'_def)
      } moreover {
        assume "a\<noteq>0"
        then have "otimes' 1 a = cor (((1 + cmod a) powr 1 - (1 - cmod a) powr 1) /
               ((1 + cmod a) powr 1 + (1 - cmod a) powr 1)) *
          (a / cor (cmod a))"       
          unfolding otimes'_def otimes'_k_def 
          by presburger
        moreover have "cor (((1 + cmod a) powr 1 - (1 - cmod a) powr 1) /
               ((1 + cmod a) powr 1 + (1 - cmod a) powr 1)) *
          (a / cor (cmod a)) = cor (1+cmod a - 1 + cmod a)/(1+cmod a + 1-cmod a) * (a / cor (cmod a))"
          using \<open>a \<in> {z. cmod z < 1}\<close> by auto
        moreover have " cor (1+cmod a - 1 + cmod a)/(1+cmod a + 1-cmod a) * (a / cor (cmod a)) = cor (cmod a) * (a/cor (cmod a))"
        proof-
          have "1+cmod a - 1 + cmod a = 2*cmod a"
            by argo
          moreover have "1+cmod a + 1-cmod a = 2"
            by argo
          moreover have "2*cmod a /2 = cmod a"
            by simp
          ultimately show ?thesis
            by auto
        qed
        ultimately have ?thesis 
          by auto
      }
      ultimately show ?thesis 
        by fastforce
    qed
  qed 
next
  show " \<forall>r1 r2.
       \<forall>a\<in>{z. cmod z < 1}.
          otimes' (r1 + r2) a = oplus_m' (otimes' r1 a) (otimes' r2 a)"
    using otimes_oplus_m_distrib by blast
next
  show "\<forall>r1 r2. \<forall>a\<in>{z. cmod z < 1}. otimes' (r1 * r2) a = otimes' r1 (otimes' r2 a)"
    using otimes_assoc by blast
next
  show "\<forall>u\<in>{z. cmod z < 1}.
       \<forall>v\<in>{z. cmod z < 1}.
          \<forall>r. \<forall>a\<in>{z. cmod z < 1}.
                 gyr_m' u v (otimes' r a) = otimes' r (gyr_m' u v a)"
    using gyr_m_gyrospace2 by blast
next
  show " \<forall>r1 r2.
       \<forall>v\<in>{z. cmod z < 1}.
          \<forall>x\<in>{z. cmod z < 1}. gyr_m' (otimes' r1 v) (otimes' r2 v) x = x"
    using gyr_m_gyrospace by blast
qed



(* --------------------------------------------------------- *)



(* --------------------------------------------------------- *)

lemma gamma_factor_eq1_lemma2:
  fixes x y::real
  assumes "y > 0"  
  shows "1 / sqrt(1 - (x*x)/(y*y)) = abs y / sqrt(y*y - x*x)"
proof-
  have "1 - ((x*x)/(y*y)) = (y*y-x*x) / (y*y)"
    using assms
    by (metis diff_divide_distrib div_0 divide_less_cancel divide_self no_zero_divisors)
  then have "sqrt (1 - (x*x)/(y*y)) = sqrt(y*y-x*x)/sqrt(y*y)"
    using real_sqrt_divide by presburger
  then have "sqrt(1 - (x*x)/(y*y)) = sqrt(y*y-x*x)/abs(y)"
    using real_sqrt_abs2 by presburger
  then show ?thesis
    by auto
qed

lemma gamma_factor_norm_oplus_m:
  assumes "a\<in>{z. cmod z < 1}" "b\<in>{z. cmod z < 1}"
  shows "\<gamma> (cmod (oplus_m' a  b)) = 
         \<gamma>  a *  
         \<gamma>  b * 
         cmod (1 + cnj  a * b)"
proof-
  let ?a = " a" and ?b = " b"
  have "norm (cmod (oplus_m' a  b)) < 1"
    using assms(1) assms(2) oplus_m'_in_disc by force
  then have *: "\<gamma> (cmod (oplus_m' a  b)) = 
                1 / sqrt(1 - cmod (?a+?b) / cmod (1 + cnj ?a *?b) * cmod (?a+?b) / cmod (1 + cnj ?a *?b))"
    by (simp add: gamma_factor_def norm_divide oplus_m'_def power2_eq_square)
  also have "\<dots> =  
           cmod(1 + cnj ?a * ?b) /
           sqrt(cmod (1 + cnj ?a * ?b) * cmod (1 + cnj ?a * ?b) -
                cmod (?a+?b) * cmod (?a+?b))"
  proof-
    let ?iz1 = "cmod (?a+?b) * cmod (?a+?b)"
    let ?iz2 = "cmod (1 + cnj ?a * ?b) * cmod (1 + cnj ?a * ?b)"
    have "?iz1 \<ge> 0"
      by force
    moreover
    have "?iz2 > 0"
      using assms(1) assms(2) den_not_zero by auto
    ultimately show ?thesis
      using zero_less_mult_iff
      by (smt (verit, best) divide_divide_eq_left gamma_factor_eq1_lemma2 norm_not_less_zero times_divide_eq_left)
  qed
  also have "\<dots> = cmod(1 + cnj ?a * ?b) / sqrt((1 - cmod ?a * cmod ?a) * (1 - cmod ?b * cmod ?b))"    
    using gamma_factor_eq1_lemma1
    by presburger
  also have "\<dots> =
         \<gamma>  a *  
         \<gamma>  b * 
         cmod (1 + cnj  a * b)"
  proof-
    have "cmod a < 1" "cmod  b < 1"
      using assms(1) apply force
      using assms(2) by blast
    then show ?thesis 
      by (simp add: gamma_factor_def power2_eq_square real_sqrt_mult)
   
  qed
  finally show ?thesis
    .
qed

lemma gamma_factor_oplus_m_triangle_lemma:
  fixes x y ::real
  assumes "x \<ge> 0" "x < 1" "y \<ge> 0" "y < 1"
  shows "1 / sqrt (1 - ((x+y)*(x+y))/((1+x*y)*(1+x*y))) = 
         (1+x*y) / (sqrt (1-x*x) * sqrt (1-y*y))"
proof-
  have "1 - ((x+y)*(x+y))/((1+x*y)*(1+x*y)) = ((1+x*y)*(1+x*y) - (x+y)*(x+y)) / ((1+x*y)*(1+x*y))"
    by (smt (verit, ccfv_threshold) add_divide_distrib assms div_self mult_eq_0_iff mult_nonneg_nonneg)
  then have "1 - ((x+y)*(x+y))/((1+x*y)*(1+x*y)) = ((1-x*x)*(1-y*y)) / ((1+x*y)*(1+x*y))"
    by (simp add: field_simps)
  then have "sqrt(1 - ((x+y)*(x+y))/((1+x*y)*(1+x*y))) = 
             (sqrt(1-x*x)*sqrt(1-y*y)) / (sqrt((1+x*y)*(1+x*y)))"
    using assms real_sqrt_divide real_sqrt_mult
    by presburger
  then show ?thesis
    using assms
    by simp
qed

lemma gamma_factor_oplus_m_triangle:
  assumes "a\<in>{z. cmod z <1 }" "b\<in>{z. cmod z <1}"
  shows "\<gamma> (cmod (oplus_m' a  b)) \<le> \<gamma> (oplus_m' (cmod a) (cmod b))"
proof-
  have " \<gamma> (oplus_m' (cmod a) (cmod b)) =
        \<gamma> (cmod a) * \<gamma> (cmod b) * (1 + cmod a * (cmod b))"
  proof-
    let ?expr1 =  "((cmod a) + (cmod b)) / (1 + (cmod a)*(cmod b))"
    let ?expr2 = "oplus_m' (cmod a) (cmod b)"
    have *: "?expr1 = ?expr2"
      by (simp add: oplus_m'_def)

    have **: "norm (cmod a) < 1" "norm (cmod b) < 1"
      using assms(1) apply auto[1]
      using assms(2) by force
    then have ***: "\<gamma> (cmod a) = 1 / sqrt(1 - (cmod a) * (cmod a))"
                   "\<gamma> (cmod b) = 1 / sqrt(1 - (cmod b) * (cmod b))"
      unfolding gamma_factor_def
      by (auto simp add: power2_eq_square) 

    have "\<gamma> ?expr1 = 1 / sqrt(1 - ((cmod (?expr1)) * cmod(?expr1)))"
      using * **
      unfolding gamma_factor_def power2_eq_square
      by (metis norm_of_real oplus_m'_in_disc real_norm_def)
    moreover
    have "cmod ?expr1 = ?expr1"
      by (smt (verit, ccfv_SIG) norm_divide norm_ge_zero norm_mult norm_of_real of_real_divide)
    ultimately
    have "\<gamma> ?expr1 = 1 / sqrt (1 - (Re ?expr1 * Re ?expr1))"
       by (metis Re_complex_of_real)
    then have "\<gamma> ?expr1 = (1 + (cmod a)*(cmod b)) / (sqrt (1-(cmod a)*(cmod a)) * sqrt (1-(cmod b)*(cmod b)))"
      using "**"(1) "**"(2) gamma_factor_oplus_m_triangle_lemma by force
     then have "\<gamma> (cor ?expr1) = (1 + (cmod a)*(cmod b)) / (sqrt (1-(cmod a)*(cmod a)) * sqrt (1-(cmod b)*(cmod b)))"
       unfolding gamma_factor_def
       by (metis norm_of_real real_norm_def)       
    then show ?thesis
      using \<open>?expr1 = ?expr2\<close>[symmetric]
      using  ***
      by simp
  qed

  moreover

  have "\<gamma> (cmod a) * \<gamma> (cmod b) * (1 + (cmod a)*(cmod b)) \<ge> 
        \<gamma> (a) * \<gamma> (b) * cmod (1  + cnj  a *  b)"
  proof-
    have *: "\<gamma> (cmod a) = \<gamma> ( a)"
            "\<gamma> (cmod b) = \<gamma> ( b)"
       apply (simp add: gamma_factor_def)
      by (simp add: gamma_factor_def)
     moreover have "cmod (1 + cnj  a *  b) \<le> 
           cmod 1 + cmod (cnj a * b)"
       using norm_triangle_ineq
       by blast
     moreover  have "cmod 1 + cmod (cnj a * b) = 1 + cmod (a) * cmod ( b)"
       by (simp add: norm_mult)
     moreover have "\<gamma> (cmod a) * \<gamma> (cmod b) * (1 + cmod a * cmod b) = \<gamma> ( a) * \<gamma> ( b) * (1 + cmod a * cmod b)"
       using calculation(1) calculation(2) by presburger
     moreover have "\<gamma> ( a) * \<gamma> ( b) * (1 + cmod a * cmod b) = \<gamma> ( a) * \<gamma> ( b) * (cmod 1 + cmod (cnj a * b))"
       using calculation(4) by presburger
    ultimately show ?thesis
      by (smt (verit, best) cnj_closed_for_unit_disc complex_mod_mult_cnj divide_eq_0_iff divide_pos_pos gamma_factor_def mult_closed_for_unit_disc mult_left_mono mult_nonneg_nonneg real_sqrt_ge_zero)
   qed

   ultimately show ?thesis 
     using assms(1) assms(2) gamma_factor_norm_oplus_m by presburger
qed

lemma mobius_triangle:
  assumes "a\<in>{z. cmod z < 1}" "b\<in>{z. cmod z < 1}"
  shows "cmod (oplus_m' a  b) \<le> Re (oplus_m' (cmod a) (cmod b))"
proof (cases " a = -  b")
  case True
  then have "cmod (oplus_m' a  b) = 0"
    by (simp add: oplus_m'_def)
  moreover have "Re (oplus_m' (cmod a) (cmod b)) = (oplus_m' (cmod a) (cmod b))"
    using oplus_m'_def by auto
  moreover have "Re (oplus_m' (cmod a) (cmod b)) \<ge>0"
  proof-
    have "(oplus_m' (cmod a) (cmod b)) = ((cmod a) + (cmod b))/(1+cmod a*(cmod b))"
      by (simp add: oplus_m'_def)
    moreover have "cmod a + (cmod b) \<ge>0"
      by auto
    moreover have "1+cmod a * (cmod b) > 0"
      by (simp add: add_pos_nonneg)
    ultimately show ?thesis 
      by simp
    qed
    ultimately show ?thesis
      by presburger
next
  case False
  let ?e1 = "(cmod (oplus_m' a  b))"
  let ?e2 = "cmod (oplus_m' (cmod a) (cmod b))"
  have "?e1 > 0"
    by (metis False Moebius_gyrogroup.gyro_left_cancel' add.inverse_inverse add.right_neutral assms(1) assms(2) div_by_1 mult_cancel_right1 ominus_m'_def oplus_m'_def zero_less_norm_iff)
   
  moreover
  have "?e2 > 0"
    using Re_complex_of_real assms(1) assms(2) calculation den_not_zero divide_eq_0_iff mem_Collect_eq norm_of_real oplus_m'_def plus_complex.sel(1) zero_less_norm_iff
    using complex_cnj_complex_of_real norm_minus_cancel norm_mult of_real_1 of_real_mult
    by (smt (verit, ccfv_threshold) norm_not_less_zero)
    moreover
  have "?e1 < 1" "?e2 < 1"
    using Moebius_gyrogroup.gyroplus_closed assms(1) assms(2) apply blast
    using assms(1) assms(2) oplus_m'_in_disc by auto
   moreover have **:"Re (oplus_m' (cmod a) (cmod b)) = (oplus_m' (cmod a) (cmod b))"
    using oplus_m'_def by auto
  moreover have " \<gamma> (cmod (oplus_m' (cor (cmod a)) (cor (cmod b)))) =  \<gamma> ( (oplus_m' (cor (cmod a)) (cor (cmod b))))"
    by (simp add: gamma_factor_def)
  moreover have  "\<gamma> (cmod (oplus_m' a  b)) \<le> \<gamma> (oplus_m' (cmod a) (cmod b))"
    using assms(1) assms(2) gamma_factor_oplus_m_triangle by blast
  ultimately
  show ?thesis
    using gamma_factor_increase_reverse_2[of ?e2 ?e1]
    by (smt (verit, del_insts) False Im_complex_of_real Re_complex_of_real Re_divide_Reals complex_cnj_complex_of_real complex_is_Real_iff divide_pos_pos eq_neg_iff_add_eq_0 mult_nonneg_nonneg norm_ge_zero norm_of_real norm_triangle_ineq of_real_1 of_real_add of_real_mult oplus_m'_def zero_less_norm_iff)
qed


interpretation Mobius_gyrolinear: normed_gyrolinear_space "{z. cmod z < 1}" 0 oplus_m' ominus_m' gyr_m' otimes' cmod artanh
proof
  show "\<forall>a\<in>{z. cmod z < 1}. 0 \<le> cmod a"
    using norm_ge_zero by blast
next
  show " \<forall>y. y \<in> cmod ` {z. cmod z < 1} \<longrightarrow> 0 \<le> artanh y"
    using artanh_nonneg by force
next
  show "bij_betw artanh (cmod ` {z. cmod z < 1}) {x::real. 0 \<le> x}"
  proof-
    have "(cmod ` {z. cmod z < 1}) = {z. 0\<le> z  \<and> z< 1}"
    proof
      show "cmod ` {z. cmod z < 1} \<subseteq> {z. 0 \<le> z \<and> z < 1}"
        by force
    next
      show " {z. 0 \<le> z \<and> z < 1} \<subseteq> cmod ` {z. cmod z < 1}"
        by (smt (verit, del_insts) image_iff mem_Collect_eq norm_of_real subsetI)
    qed
    moreover have "inj_on artanh (cmod ` {z. cmod z < 1})"
      by (smt (verit, ccfv_SIG) calculation inj_on_def mem_Collect_eq tanh_artanh)
    moreover have "artanh ` {z. 0\<le> z \<and> z<1} = {x::real. x\<ge>0}"
    proof
      show "artanh ` {z. 0 \<le> z \<and> z < 1} \<subseteq> {x::real. 0 \<le> x}"
      proof-
        have "\<forall>x::real. 0\<le>x \<and> x<1 \<longrightarrow> artanh x \<ge> 0"
          using artanh_nonneg by blast
        moreover have " \<And>x. x \<in> artanh ` {z. 0 \<le> z \<and> z < 1} \<Longrightarrow> x \<in> {x::real. 0 \<le> x} "
          using calculation by blast
        ultimately show ?thesis
          by blast
      qed
    next
      show "{x::real. 0 \<le> x} \<subseteq> artanh ` {z. 0 \<le> z \<and> z < 1}"
      proof
        show " \<And>x. x \<in> {x::real. 0 \<le> x} \<Longrightarrow> x \<in> artanh ` {z. 0 \<le> z \<and> z < 1}"
        proof-
          fix x
          assume "x\<in>{x::real. 0\<le>x}"
          show "x \<in> artanh ` {z. 0 \<le> z \<and> z < 1}"
            by (metis \<open>x \<in> {x. 0 \<le> x}\<close> artanh_tanh_real mem_Collect_eq rev_image_eqI tanh_real_lt_1 tanh_real_nonneg_iff)
        qed
      qed
    qed
    ultimately show ?thesis
      by (simp add: bij_betw_def)
  qed
next
  show " \<forall>y z. y \<in> cmod ` {z. cmod z < 1} \<and> z \<in> cmod ` {z. cmod z < 1} \<and> z < y \<longrightarrow>
          artanh z < artanh y"
    by (smt (verit, del_insts) image_iff mem_Collect_eq norm_ge_zero tanh_artanh tanh_real_less_iff)
next
  show "\<forall>x\<in>{z. cmod z < 1}.
       \<forall>y\<in>{z. cmod z < 1}.
          artanh (cmod (oplus_m' x y)) \<le> artanh (cmod x) + artanh (cmod y)"
  proof
    fix x 
    assume "x\<in>{z. cmod z < 1}"
    show " \<forall>y\<in>{z. cmod z < 1}.
          artanh (cmod (oplus_m' x y)) \<le> artanh (cmod x) + artanh (cmod y)"
    proof

      fix y
      assume "y\<in>{z. cmod z < 1}"
      show "artanh (cmod (oplus_m' x y)) \<le> artanh (cmod x) + artanh (cmod y)"
        using oplus_m'_def
      proof-
        have "tanh(artanh(cmod x)+artanh(cmod y)) = (cmod x  + cmod y)/ (1+cmod x * (cmod y))"
          by (smt (verit) \<open>x \<in> {z. cmod z < 1}\<close> \<open>y \<in> {z. cmod z < 1}\<close> cosh_real_nonzero mem_Collect_eq norm_not_less_zero tanh_add tanh_artanh)
        moreover have "(cmod x  + cmod y)/ (1+cmod x * (cmod y)) = oplus_m' (cmod x) (cmod y)"
        proof-
          have "cmod (cmod x) = cmod x"
            by simp
          moreover have "cnj (cmod x) = cmod x"
            by simp
          ultimately show ?thesis using oplus_m'_def
            by force
        qed
        moreover have " Im (oplus_m' (cmod x) (cmod y)) =0"
          by (metis Im_complex_of_real calculation(2))
        moreover have "oplus_m' (cmod x) (cmod y) = Re(oplus_m' (cmod x) (cmod y))"
          by (metis Re_complex_of_real calculation(2))
        moreover have "(cmod (oplus_m' x y)) \<le> tanh(artanh(cmod x)+artanh(cmod y))"
          by (metis Re_complex_of_real \<open>x \<in> {z. cmod z < 1}\<close> \<open>y \<in> {z. cmod z < 1}\<close> calculation(1) calculation(2) mobius_triangle)
        ultimately show ?thesis
          by (metis (mono_tags, opaque_lifting) artanh_monotone artanh_tanh_real linorder_not_less norm_ge_zero order_trans tanh_real_lt_1)
      qed
    qed
  qed
next 
  show "\<forall>r. \<forall>x\<in>{z. cmod z < 1}. artanh (cmod (otimes' r x)) = \<bar>r\<bar> * artanh (cmod x)"
  proof
    fix r
    show " \<forall>x\<in>{z. cmod z < 1}. artanh (cmod (otimes' r x)) = \<bar>r\<bar> * artanh (cmod x)"
    proof
      fix x 
      assume "x\<in>{z. cmod z < 1}"
      show " artanh (cmod (otimes' r x)) = \<bar>r\<bar> * artanh (cmod x)"
      proof-
        have "artanh (cmod (otimes' r x)) = artanh (abs (tanh (r * artanh (cmod x))))"
          using \<open>x \<in> {z. cmod z < 1}\<close> cmod_otimes' otimes'_k_tanh by auto
        then show ?thesis
          by (metis \<open>x \<in> {z. cmod z < 1}\<close> abs_mult abs_of_nonneg artanh_abs_tanh artanh_nonneg mem_Collect_eq norm_ge_zero)
      qed
    qed
  qed
 
next
  show "\<forall>u\<in>{z. cmod z < 1}.
       \<forall>v\<in>{z. cmod z < 1}. \<forall>x\<in>{z. cmod z < 1}. cmod (gyr_m' u v x) = cmod x"
    by (metis cmod_mix_cnj gyr_m'_def mem_Collect_eq mult.commute mult_cancel_right1 norm_mult)
next
  show "\<forall>x\<in>{z. cmod z < 1}. (cmod x = 0) = (x = 0)"
    by force
qed


definition m_norms::"real set" where
  "m_norms = cmod`{z. cmod z < 1} \<union> (\<lambda>x. (x*-1)) `cmod`{z. cmod z < 1}"

lemma m_norms_simp:
  shows "m_norms = {z::real. -1<z \<and> z<1}"
proof
  show " m_norms \<subseteq> {z. - 1 < z \<and> z < 1}"
  proof
    show  "\<And>x. x \<in> m_norms \<Longrightarrow> x \<in> {z. - 1 < z \<and> z < 1}"
    proof-
      fix x
      assume "x\<in>m_norms"
      show "x \<in> {z. - 1 < z \<and> z < 1}"
      proof-
        have "x\<in>cmod`{z. cmod z < 1} \<or> x\<in> (\<lambda>x. (x*-1)) `cmod`{z. cmod z < 1}"
          using \<open>x \<in> m_norms\<close> m_norms_def by auto
        moreover {
          assume "x\<in>cmod`{z. cmod z < 1}"
          then have ?thesis 
            by (smt (verit, del_insts) image_iff mem_Collect_eq norm_ge_zero)
        } moreover {
          assume "x\<in> (\<lambda>x. (x*-1)) `cmod`{z. cmod z < 1}"
          then have ?thesis
            by (smt (verit) f_inv_into_f inv_into_into mem_Collect_eq norm_ge_zero)
        }
        ultimately show ?thesis
          by argo
      qed  
    qed
  qed
next
  show " {z. - 1 < z \<and> z < 1} \<subseteq> m_norms"
  proof
    show "\<And>x. x \<in> {z. - 1 < z \<and> z < 1} \<Longrightarrow> x \<in> m_norms"
      by (smt (verit, del_insts) Un_iff imageI m_norms_def mem_Collect_eq norm_of_real)
  qed
qed

definition cmod_norms_all::"real set" where
  "cmod_norms_all = cmod`{z. cmod z<1} \<union> ( (\<lambda>x. - 1 * cmod x)`{z. cmod z<1})"


lemma m_norms_cmod_norms:
  shows "m_norms = cmod_norms_all"
  by (simp add: cmod_norms_all_def image_image m_norms_def)

(*

  shows "normed_gyrolinear_space' dom gyrozero gyroplus gyroinv gyr scale norm' 
(\<lambda>x. (if x \<in> (norm'`dom) then (f x) else
 (if x\<in> ( (\<lambda>x. - 1 * norm' x)`dom) then (-f (-x)) else undefined)))" 
*)

interpretation Mobius_gyrolinear_1: normed_gyrolinear_space' "{z. cmod z < 1}" 0 oplus_m' ominus_m' gyr_m' otimes' cmod 
"(\<lambda>x. (if x \<in> (cmod`{z. cmod z <1}) then (artanh x) else 
(if x\<in> ( (\<lambda>x. - 1 * cmod x)`{z. cmod z<1}) then (- artanh (-x)) else undefined)))"
  using Mobius_gyrolinear.is_normed_gyrolinear_space' by blast

(*  shows "normed_gyrolinear_space'' dom gyrozero gyroplus gyroinv gyr scale norm' 
(\<lambda>x y. (if x\<in>norms_all \<and> y\<in>norms_all then (inv_into norms_all f') ((f' x)+(f' y)) else undefined))
(\<lambda>r a. (if a\<in>norms_all  then (inv_into norms_all f') (r*(f' a)) else undefined))"*)


definition artanh'::"(real\<Rightarrow>real)" where
 "artanh'= (\<lambda>x. (if x \<in> (cmod`{z. cmod z <1}) then (artanh x) else 
(if x\<in> ( (\<lambda>x. - 1 * cmod x)`{z. cmod z<1}) then (- artanh (-x)) else undefined)))"

definition mobius_oplus'::"real\<Rightarrow>real\<Rightarrow>real" where 
  "mobius_oplus' a b = (if a\<in>cmod_norms_all \<and> b\<in>cmod_norms_all then
 (inv_into cmod_norms_all artanh') ((artanh' a) + (artanh' b)) else undefined)"

definition mobius_otimes'::"real\<Rightarrow>real\<Rightarrow>real" where 
  "mobius_otimes' r a = (if a\<in>cmod_norms_all  then 
(inv_into cmod_norms_all artanh') (r*(artanh' a)) else undefined)"


lemma norms_same:
  shows "Mobius_gyrolinear_1.norms_all = cmod_norms_all"
  using Mobius_gyrolinear_1.norms_all_def Mobius_gyrolinear_1.norms_def Mobius_gyrolinear_1.norms_neg_def cmod_norms_all_def by argo


lemma Mobius_gyrolin_2:
  shows "normed_gyrolinear_space'' {z. cmod z <1} 0 oplus_m' ominus_m' gyr_m' otimes' cmod
 (\<lambda>x y. (if x\<in>cmod_norms_all \<and> y\<in>cmod_norms_all then (inv_into cmod_norms_all artanh') ((artanh' x)+(artanh' y)) else undefined))
(\<lambda>r a. (if a\<in>cmod_norms_all  then (inv_into cmod_norms_all artanh') (r*(artanh' a)) else undefined))"
 using Mobius_gyrolinear_1.is_normed_gyrolinear_space'' norms_same
 unfolding artanh'_def
proof-
  show "normed_gyrolinear_space'' {c. cmod c < 1} 0 oplus_m' ominus_m' gyr_m' otimes' cmod (\<lambda>r ra. if r \<in> cmod_norms_all \<and> ra \<in> cmod_norms_all then inv_into cmod_norms_all (\<lambda>r. if r \<in> cmod ` {c. cmod c < 1} then artanh r else if r \<in> (\<lambda>c. - 1 * cmod c) ` {c. cmod c < 1} then - artanh (- r) else undefined) ((if r \<in> cmod ` {c. cmod c < 1} then artanh r else if r \<in> (\<lambda>c. - 1 * cmod c) ` {c. cmod c < 1} then - artanh (- r) else undefined) + (if ra \<in> cmod ` {c. cmod c < 1} then artanh ra else if ra \<in> (\<lambda>c. - 1 * cmod c) ` {c. cmod c < 1} then - artanh (- ra) else undefined)) else undefined) (\<lambda>r ra. if ra \<in> cmod_norms_all then inv_into cmod_norms_all (\<lambda>r. if r \<in> cmod ` {c. cmod c < 1} then artanh r else if r \<in> (\<lambda>c. - 1 * cmod c) ` {c. cmod c < 1} then - artanh (- r) else undefined) (r * (if ra \<in> cmod ` {c. cmod c < 1} then artanh ra else if ra \<in> (\<lambda>c. - 1 * cmod c) ` {c. cmod c < 1} then - artanh (- ra) else undefined)) else undefined)"
     unfolding artanh'_def
    by (metis (no_types) Mobius_gyrolinear_1.is_normed_gyrolinear_space'' norms_same)
qed

interpretation Mobius_gyrolinear_2 : normed_gyrolinear_space'' "{z. cmod z <1}" 0 oplus_m' ominus_m' gyr_m' otimes' cmod
 "(\<lambda>x y. (if x\<in>cmod_norms_all \<and> y\<in>cmod_norms_all then (inv_into cmod_norms_all artanh') ((artanh' x)+(artanh' y)) else undefined))"
"(\<lambda>r a. (if a\<in>cmod_norms_all  then (inv_into cmod_norms_all artanh') (r*(artanh' a)) else undefined))"
  using Mobius_gyrolin_2 by blast
  
 
lemma otimes_homogenity:
  assumes "a\<in>{z. cmod z < 1}"
  shows "cmod (otimes' r a) = cmod ((otimes' \<bar>r\<bar>  (cmod a)))"
proof (cases "a = 0")
  case True
  then show ?thesis
    by (simp add: otimes'_def)
next
  case False
  have "(cmod (otimes' r a)) = \<bar>tanh (r * artanh (cmod a))\<bar>"
    using assms cmod_otimes' otimes'_k_tanh by auto
  moreover
  have " (otimes' \<bar>r\<bar> (cmod a )) = tanh (\<bar>r\<bar> * artanh (cmod a))"
    using assms otimes'_def otimes'_k_tanh by auto
  moreover 
  have "\<bar>tanh(r * artanh (cmod a)) / (cmod a)\<bar> = 
         tanh (\<bar>r\<bar> * artanh (cmod  a)) / (cmod a)"
    by (metis abs_divide abs_mult_pos abs_norm_cancel artanh_nonneg assms mem_Collect_eq norm_ge_zero tanh_real_abs)
  ultimately 
  show ?thesis
    by (smt (verit, best) norm_of_real real_compex_cmod tanh_real_abs)
qed

lemma otimes_scale_prop:
  fixes r :: real
  assumes "a\<in>{z. cmod z< 1}" "r \<noteq>0" "a\<noteq>0"
  shows "(otimes' \<bar>r\<bar>  a)  /\<^sub>R cmod (otimes' r  a)  =  a  /\<^sub>R (cmod a)"
proof-
  let ?f = "\<lambda> r a. tanh (r * artanh (cmod  a))"

  have *: "(otimes' \<bar>r\<bar>  a) = ?f \<bar>r\<bar> a * ( a  /\<^sub>R (cmod a))"
    using assms(1) complex_sgn_def otimes'_def otimes'_k_tanh sgn_eq by auto
  then have "cmod (otimes'  \<bar>r\<bar>  a) = cmod (?f  r a * ( a  /\<^sub>R (cmod a)))"
    by (smt (verit, del_insts) norm_mult norm_of_real of_real_mult tanh_real_abs)
    
  then have "cmod (otimes'  r  a) = \<bar>?f r a / cmod a \<bar> * (cmod a)"
    using assms(1) cmod_otimes' otimes'_k_tanh by force
    
  have "?f \<bar>r\<bar> a = tanh(\<bar>r\<bar> * \<bar>artanh (cmod  a)\<bar>)"
    using artanh_nonneg assms(1) by force
  
  then have "?f \<bar>r\<bar> a = \<bar>?f r a\<bar>"
    by (metis abs_mult tanh_real_abs)

  have "\<bar>?f r a / (cmod a)\<bar> = ?f \<bar>r\<bar> a / (cmod a)"
    by (simp add: \<open>tanh (\<bar>r\<bar> * artanh (cmod a)) = \<bar>tanh (r * artanh (cmod a))\<bar>\<close>)
 
  then have **:"?f \<bar>r\<bar> a / (cmod a) = \<bar>?f r a / (cmod a)\<bar>"
    by presburger

  show ?thesis
  proof (cases " a = 0")
    case True
    then show ?thesis
      using assms
      by meson

  next
    case False
    then have "\<bar>?f r a / (cmod a)\<bar> \<noteq>0"
      using assms
      by (simp add: artanh_not_0)
    
    then show ?thesis
      by (smt (verit, ccfv_threshold) "*" "**" \<open>cmod (otimes' r a) = \<bar>tanh (r * artanh (cmod a)) / cmod a\<bar> * cmod a\<close> divide_eq_eq divide_inverse_commute mult_cancel_right1 mult_scaleR_left of_real_1 of_real_mult scaleR_conv_of_real)
    
  qed
qed

lemma same_norm_mobius:
  shows "Mobius_gyrolinear_1.norms_all = ({x.\<exists>a\<in> {z. cmod z < 1}. x = cmod a \<or> x = - cmod  a})"
proof-
  have "{x. x\<in>cmod ` {z. cmod z < 1}\<or> x\<in> (\<lambda>x. - 1 * cmod x) ` {z. cmod z < 1}} = {x.\<exists>a\<in> {z. cmod z < 1}. x = cmod a \<or> x = - cmod  a}"
    by auto
 then show  "Mobius_gyrolinear_1.norms_all = ({x.\<exists>a\<in> {z. cmod z < 1}. x = cmod a \<or> x = - cmod  a})"
    using Mobius_gyrolinear_1.norms_all_def
         Mobius_gyrolinear_1.norms_def
         Mobius_gyrolinear_1.norms_neg_def
    by auto
qed

lemma same_norm_mobius_2:
  shows " Mobius_gyrolinear_1.norms_all = cmod_norms_all"
  by (simp add: norms_same)

lemma norm_oplus_f_mobius_oplus':
  shows "Mobius_gyrolinear_1.norm_oplus_f =  mobius_oplus'"
    using Mobius_gyrolinear_1.norm_oplus_f_def
    using mobius_oplus'_def 
      using same_norm_mobius
      unfolding artanh'_def  same_norm_mobius_2 by fastforce

lemma norm_otimes_f_mobius_otimes':
  shows "Mobius_gyrolinear_1.norm_otimes_f = mobius_otimes'"
   using Mobius_gyrolinear_1.norm_otimes_f_def
    using mobius_otimes'_def 
      using same_norm_mobius
      unfolding artanh'_def  same_norm_mobius_2 by fastforce

lemma mobius_norms_one_dim_vector_space_with_domain:
  shows "one_dim_vector_space_with_domain ({x.\<exists>a\<in> {z. cmod z < 1}. x = cmod a \<or> x = - cmod  a}) mobius_oplus' 0 mobius_otimes'"
  using Mobius_gyrolinear_1.one_dim_vs
  using norm_oplus_f_mobius_oplus' norm_otimes_f_mobius_otimes' same_norm_mobius by argo

lemma mobius_norms_one_dim_vector_space_with_domain2:
  shows "one_dim_vector_space_with_domain ({x.\<exists>a\<in> {z. cmod z < 1}. x = cmod ((\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined)a) \<or> 
x = - cmod  ((\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined)a)}) mobius_oplus' 0 mobius_otimes'"
  using mobius_norms_one_dim_vector_space_with_domain by force

lemma Mobius_gyrospace_ax1:
  shows "inj_on (\<lambda>x. if x \<in> {z. cmod z < 1} then x else undefined) {z. cmod z < 1}"
  by (simp add: inj_on_def)

lemma Mobius_gyrospace_ax2:
  shows  "(if 0 \<in> {z. cmod z < 1} then 0 else undefined) = 0"
  by force
lemma Mobius_gyrospace_ax3:
  shows  "\<forall>r. \<forall>x\<in>{z. cmod z < 1}. otimes' r x \<in> {z. cmod z < 1}"
  using Mobius_gyrolinear.scale_closed by blast
lemma Mobius_gyrospace_ax4:
  shows " \<forall>a\<in>{z. cmod z < 1}. otimes' 1 a = a"
  using Mobius_gyrolinear.scale_1 by force
lemma Mobius_gyrospace_ax5:
  shows  " \<And>r1 r2.
       \<forall>a\<in>{z. cmod z < 1}.
          otimes' (r1 + r2) a = oplus_m' (otimes' r1 a) (otimes' r2 a)"
  using otimes_oplus_m_distrib by blast
lemma Mobius_gyrospace_ax6:
  shows "\<And>r1 r2. \<forall>a\<in>{z. cmod z < 1}. otimes' (r1 * r2) a = otimes' r1 (otimes' r2 a)"
  using Mobius_gyrolinear.scale_assoc by blast

lemma Mobius_gyrospace_ax7:
  shows "\<forall>a\<in>{z. cmod z < 1}.
       \<forall>r. a \<noteq> 0 \<and> r \<noteq> 0 \<longrightarrow>
           (if otimes' \<bar>r\<bar> a \<in> {z. cmod z < 1} then otimes' \<bar>r\<bar> a
            else undefined) /\<^sub>R
           cmod
            (if otimes' r a \<in> {z. cmod z < 1} then otimes' r a else undefined) =
           (if a \<in> {z. cmod z < 1} then a else undefined) /\<^sub>R
           cmod (if a \<in> {z. cmod z < 1} then a else undefined)"
  using Mobius_gyrolinear.scale_closed otimes_scale_prop by auto

lemma Mobius_gyrospace_ax8:
  shows "\<forall>r. \<forall>u\<in>{z. cmod z < 1}.
           \<forall>v\<in>{z. cmod z < 1}.
              \<forall>a\<in>{z. cmod z < 1}.
                 gyr_m' u v (otimes' r a) = otimes' r (gyr_m' u v a)"
  using gyr_m_gyrospace2 by blast

lemma Mobius_gyrospace_ax9:
  shows "\<forall>r1 r2.
       \<forall>v\<in>{z. cmod z < 1}.
          \<forall>x\<in>{z. cmod z < 1}. gyr_m' (otimes' r1 v) (otimes' r2 v) x = x"
  using gyr_m_gyrospace by blast

lemma Mobius_gyrospace_ax11:
  shows "\<forall>r::real.\<forall>a\<in>{z. cmod z <1}. cmod (((\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined))
 (otimes' r a)) = mobius_otimes' \<bar>r\<bar> (cmod (((\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined)) a))"
  using Mobius_gyrolinear_1.r3 Mobius_gyrospace_ax3 norm_otimes_f_mobius_otimes' by auto

lemma Mobius_gyrospace_ax12:
  shows  "\<forall>a\<in>{z. cmod z<1}. \<forall>b\<in>{z. cmod z<1}.
 cmod (((\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined)) (oplus_m' a b))
 \<le> mobius_oplus' (cmod (((\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined)) a))
 (cmod (((\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined)) b))"
  using Mobius_gyrolinear_1.r2 Moebius_gyrogroup.gyroplus_closed norm_oplus_f_mobius_oplus' by auto

lemma Mobius_gyrospace_ax13:
  shows "\<forall>u\<in>{z. cmod z < 1}.\<forall>v\<in>{z. cmod z < 1}.\<forall>a\<in>{z. cmod z < 1}.\<forall>b\<in>{z. cmod z < 1}.
 inner ((\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined)(gyr_m' u v a))
  ((\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined)(gyr_m' u v b)) = inner ((\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined) a) 
((\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined) b)"
  by (simp add: gyr_m_closed moebius_gyroauto)


(*

  fixes dom::"'a::real_inner set"
  fixes gyrozero :: "'a" ("0\<^sub>g")
  fixes gyroplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 100)
  fixes gyroinv :: "'a \<Rightarrow> 'a" ("\<ominus>")
  fixes gyr :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes scale ::"real \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 105) 
  fixes plus'::"real \<Rightarrow> real \<Rightarrow> real"
  fixes smult'::"real \<Rightarrow> real \<Rightarrow> real"
  fixes plus'_zero::"real"
*)
lemma Mobius_is_gyrospace:
   shows "gyrovector_space {z. cmod z < 1} 0 oplus_m' ominus_m' gyr_m' otimes'
mobius_oplus' mobius_otimes' 0 " 
proof
  show " 0 \<in> {z. cmod z < 1}"
    using Moebius_gyrogroup.zero_in_dom by blast
next
  show "\<And>a b. a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1} \<longrightarrow> oplus_m' a b \<in> {z. cmod z < 1}"
    using Moebius_gyrogroup.gyroplus_closed by blast
next
  show "\<exists>a. a \<in> {z. cmod z < 1} \<and> a \<noteq> 0"
    using Moebius_gyrogroup.non_trivial_dom by blast
next
  show "\<And>a. a \<in> {z. cmod z < 1} \<longrightarrow> ominus_m' a \<in> {z. cmod z < 1}"
    using Moebius_gyrogroup.ax1 by blast
next
  show " \<And>a b c.
       a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1} \<and> c \<in> {z. cmod z < 1} \<longrightarrow>
       gyr_m' a b c \<in> {z. cmod z < 1}"
    using Moebius_gyrogroup.gyr_def_closed by presburger
next
  show "\<And>a. a \<in> {z. cmod z < 1} \<longrightarrow> oplus_m' 0 a = a"
    using m_left_id by blast
next
  show "\<And>a. a \<in> {z. cmod z < 1} \<longrightarrow> oplus_m' (ominus_m' a) a = 0"
    by simp
next
  show " \<And>a b z.
       a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1} \<and> z \<in> {z. cmod z < 1} \<longrightarrow>
       oplus_m' a (oplus_m' b z) = oplus_m' (oplus_m' a b) (gyr_m' a b z)"
    using gyr_m_left_assoc by presburger
next
  show " \<And>a b. a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1} \<longrightarrow>
           (\<forall>x\<in>{z. cmod z < 1}. gyr_m' a b x = gyr_m' (oplus_m' a b) b x)"
    using gyr_m_left_loop by presburger
next
  show "\<And>x y. x \<in> {z. cmod z < 1} \<and> y \<in> {z. cmod z < 1} \<longrightarrow>
           (\<forall>a\<in>{z. cmod z < 1}.
               \<forall>b\<in>{z. cmod z < 1}.
                  gyr_m' x y (oplus_m' a b) = oplus_m' (gyr_m' x y a) (gyr_m' x y b)) \<and>
           bij_betw (gyr_m' x y) {z. cmod z < 1} {z. cmod z < 1}"
    using gyr_m_bij by auto
next
  show " \<forall>a\<in>{z. cmod z < 1}. \<forall>b\<in>{z. cmod z < 1}. oplus_m' a b = gyr_m' a b (oplus_m' b a)"
    using gyr_m_commute by blast
next
  show "\<forall>r. \<forall>x\<in>{z. cmod z < 1}. otimes' r x \<in> {z. cmod z < 1}"
    using Mobius_gyrospace_ax3 by force
next
  show " \<forall>a\<in>{z. cmod z < 1}. otimes' 1 a = a"
    using Mobius_gyrospace_ax4 by force
next
  show "\<forall>r1 r2.
       \<forall>a\<in>{z. cmod z < 1}. otimes' (r1 + r2) a = oplus_m' (otimes' r1 a) (otimes' r2 a)"
    using Mobius_gyrolinear.scale_distrib by fastforce
next
  show "\<forall>r1 r2. \<forall>a\<in>{z. cmod z < 1}. otimes' (r1 * r2) a = otimes' r1 (otimes' r2 a)"
    using Mobius_gyrolinear.scale_assoc by fastforce
next
  show " \<And>x y. x \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
           y \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
           mobius_oplus' x y \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a}"
    by (smt (z3) mobius_norms_one_dim_vector_space_with_domain
        one_dim_vector_space_with_domain_def vector_space_with_domain_def)
next
  show "0 \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a}"
    by force
next
  show "\<And>x y z.
       x \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
       y \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
       z \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
       mobius_oplus' (mobius_oplus' x y) z = mobius_oplus' x (mobius_oplus' y z)"
    by (smt (z3) mobius_norms_one_dim_vector_space_with_domain
        one_dim_vector_space_with_domain_def vector_space_with_domain_def)
next
  show "\<And>x y. x \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
           y \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
           mobius_oplus' x y = mobius_oplus' y x"
    by (simp add: add.commute mobius_oplus'_def)
next
  show " \<And>x. x \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
         mobius_oplus' x 0 = x"
    by (smt (z3) mobius_norms_one_dim_vector_space_with_domain
        one_dim_vector_space_with_domain_def vector_space_with_domain_def)

next
  show "\<And>x. x \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
         \<exists>y\<in>{x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a}. mobius_oplus' x y = 0"
    by (smt (z3) mobius_norms_one_dim_vector_space_with_domain
        one_dim_vector_space_with_domain_def vector_space_with_domain_def)
next
  show " \<And>x a. x \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
           mobius_otimes' a x \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a}"

    by (smt (z3) mobius_norms_one_dim_vector_space_with_domain
        one_dim_vector_space_with_domain_def vector_space_with_domain_def)
next
  show " \<And>x a b.
       x \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
       mobius_otimes' (a + b) x = mobius_oplus' (mobius_otimes' a x) (mobius_otimes' b x)"
  by (smt (z3) mobius_norms_one_dim_vector_space_with_domain
        one_dim_vector_space_with_domain_def vector_space_with_domain_def)
next
  show "\<And>x a b.
       x \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
       mobius_otimes' a (mobius_otimes' b x) = mobius_otimes' (a * b) x"
  by (smt (z3) mobius_norms_one_dim_vector_space_with_domain
        one_dim_vector_space_with_domain_def vector_space_with_domain_def)
next
  show " \<And>x. x \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
         mobius_otimes' 1 x = x"
   by (smt (z3) mobius_norms_one_dim_vector_space_with_domain
        one_dim_vector_space_with_domain_def vector_space_with_domain_def)
next
  show "\<And>x y a.
       x \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
       y \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<Longrightarrow>
       mobius_otimes' a (mobius_oplus' x y) =
       mobius_oplus' (mobius_otimes' a x) (mobius_otimes' a y)"
   by (smt (z3) mobius_norms_one_dim_vector_space_with_domain
        one_dim_vector_space_with_domain_def vector_space_with_domain_def)
next
  show "\<forall>y x. y \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<and>
          x \<in> {x. \<exists>a\<in>{z. cmod z < 1}. x = cmod a \<or> x = - cmod a} \<and> x \<noteq> 0 \<longrightarrow>
          (\<exists>!r. y = mobius_otimes' r x)"
    using  mobius_norms_one_dim_vector_space_with_domain2
 mobius_norms_one_dim_vector_space_with_domain
        one_dim_vector_space_with_domain_def
    by (metis (no_types, lifting) one_dim_vector_space_with_domain_axioms_def)
next
  show " \<forall>r. \<forall>a\<in>{z. cmod z < 1}. cmod (otimes' r a) = mobius_otimes' \<bar>r\<bar> (cmod a)"
    using Mobius_gyrospace_ax11 Mobius_gyrospace_ax3 by force
next
  show "\<forall>a\<in>{z. cmod z < 1}.
       \<forall>r. a \<noteq> 0 \<and> r \<noteq> 0 \<longrightarrow> otimes' \<bar>r\<bar> a /\<^sub>R cmod (otimes' r a) = a /\<^sub>R cmod a"
    using otimes_scale_prop by blast
next
  show "\<forall>r. \<forall>u\<in>{z. cmod z < 1}.
           \<forall>v\<in>{z. cmod z < 1}.
              \<forall>a\<in>{z. cmod z < 1}. gyr_m' u v (otimes' r a) = otimes' r (gyr_m' u v a)"
    using Mobius_gyrolinear.gyroauto_property by blast
next
  show "\<forall>r1 r2.
       \<forall>v\<in>{z. cmod z < 1}.
          \<forall>x\<in>{z. cmod z < 1}. gyr_m' (otimes' r1 v) (otimes' r2 v) x = x"
    using Mobius_gyrospace_ax9 by blast
next
  show "\<forall>a\<in>{z. cmod z < 1}.
       \<forall>b\<in>{z. cmod z < 1}. cmod (oplus_m' a b) \<le> mobius_oplus' (cmod a) (cmod b)"
    using Mobius_gyrospace_ax12 Moebius_gyrogroup.gyroplus_closed by force
next
  show "\<forall>u\<in>{z. cmod z < 1}.
       \<forall>v\<in>{z. cmod z < 1}.
          \<forall>a\<in>{z. cmod z < 1}.
             \<forall>b\<in>{z. cmod z < 1}. inner (gyr_m' u v a) (gyr_m' u v b) = inner a b"
    using moebius_gyroauto by blast
qed
(*
interpretation Mobius_gyrospace: gyrovector_space "{z. cmod z < 1}" 0 oplus_m' ominus_m' gyr_m' otimes'
mobius_oplus' mobius_otimes' 0 
  using Mobius_is_gyrospace by blast
 *)
  
lemma mobius_gyroauto_norm:
  assumes "a\<in>{z. cmod z < 1}" "b\<in>{z. cmod z < 1}"
    "v\<in>{z. cmod z < 1}"
  shows "cmod (gyr_m' a b v) = (cmod v)"
  using Mobius_gyrolinear_2.norm_gyr assms(1) assms(2) assms(3) by blast

lemma norm_scale_tanh: 
  assumes "z\<in>{z. cmod z<1}"
  shows "cmod (otimes' r  z) = \<bar>tanh (r * artanh (cmod z))\<bar>"
  using assms cmod_otimes' otimes'_k_tanh by auto

lemma ominus_m_scale:
  assumes "u\<in>{z. cmod z <1}"
  shows "otimes' k  (ominus_m'  u) = ominus_m' (otimes' k  u)"
  by (metis (lifting) Mobius_gyrolinear.scale_minus1_inv Mobius_gyrospace_ax3
      Mobius_gyrospace_ax6 assms mult.commute)
  
lemma otimes_2_oplus_m: 
  assumes "u\<in>{z. cmod z < 1}"
  shows "otimes' 2  u = oplus_m' u  u"
  by (metis Mobius_gyrolinear.scale_distrib Mobius_gyrospace_ax4 assms
      one_add_one)


definition half' :: "complex \<Rightarrow> complex" where
  "half' v = (if v\<in>{z. cmod z < 1} then (\<gamma> v / (1 + \<gamma> v)) *\<^sub>R v else undefined)"

lemma half_is_in_domain:
  assumes "v\<in>{z. cmod z < 1}"
  shows "half' v \<in> {z. cmod z < 1}"
proof-
   let ?k = "\<gamma> v / (1 + \<gamma> v)"
   have "abs ?k < 1"
     by (smt (verit, best) divide_less_eq_1_pos divide_nonneg_nonneg gamma_factor_def gamma_factor_positive)

   then have "cmod (?k *\<^sub>R v) < 1"
     by (metis divide_eq_0_iff gamma_factor_def mult_closed_for_unit_disc norm_of_real scaleR_conv_of_real scaleR_eq_0_iff)
    
   then show ?thesis 
     using assms half'_def by auto
qed

lemma otimes_2_half:
  assumes "v\<in>{z. cmod z < 1}"
  shows "otimes' 2 (half' v) = v"
proof-
  have "otimes' 2  (half' v) = oplus_m' (half' v)  (half' v)"
    using otimes_2_oplus_m
    using assms half_is_in_domain by blast
  also have "\<dots> = v"
  proof-
    have *: "\<gamma> v \<noteq> 0" "1 + \<gamma> v \<noteq> 0"
      using assms gamma_factor_positive 
      by fastforce+
    let ?k = "\<gamma> v / (1 + \<gamma> v)"
    have "1 + cnj (?k * v) * (?k * v) = 1 + ?k^2 * (cmod v)\<^sup>2"
      by (simp add: cnj_cmod mult.commute power2_eq_square)
    also have "\<dots> = 1 + (\<gamma> v)\<^sup>2 / (1 + \<gamma> v)\<^sup>2 * (1 - 1 / (\<gamma> v)\<^sup>2)"
      by (metis "*"(1) gamma_factor_def norm_square_gamma_factor power_divide)
     
    also have "\<dots> = 1 + ((\<gamma> v)\<^sup>2 * ((\<gamma> v)\<^sup>2 - 1)) / ((\<gamma> v)\<^sup>2 * (1 + \<gamma> v)\<^sup>2)"
      using *
      by (simp add: field_simps)
    also have "\<dots> = 1 + ((\<gamma> v)\<^sup>2 - 1) / (1 + \<gamma> v)\<^sup>2"
      using *
      by simp
    also have "\<dots> = 1 + ((\<gamma> v - 1) * (\<gamma> v + 1)) / ((\<gamma> v + 1) * (\<gamma> v + 1))"
      by (simp add: power2_eq_square field_simps)
    also have "\<dots> = 1 + (\<gamma> v - 1) / (\<gamma> v + 1)"
      using *
      by simp
    also have "\<dots> = 2 * ?k"
      using *
      by (simp add: field_simps)
    finally show  "oplus_m' (half' v) (half' v) = v"
      unfolding oplus_m'_def half'_def
      using * \<open>1 + cnj (?k * v) * (?k * v) = 1 + ?k\<^sup>2 * (cmod v)\<^sup>2\<close>
      using add.right_neutral assms mult_1 mult_scaleR_left mult_scaleR_right nonzero_mult_div_cancel_left of_real_def scaleR_2 scaleR_half_double scaleR_scaleR scaleR_zero_left  
      by (smt (verit, del_insts) of_real_add of_real_eq_0_iff)
    
    qed
  finally show ?thesis
    .
qed




lemma half:
  assumes "v\<in>{z. cmod z < 1}"
  shows "half' v = otimes' (1/2)  v"
  by (smt (verit, ccfv_SIG) Mobius_gyrolinear.scale_1 Mobius_gyrospace_ax6 assms divide_inverse_commute divide_nonneg_nonneg divide_self_if half_is_in_domain otimes_2_half power_divide real_sqrt_one real_sqrt_pow2)
 
lemma half':
  assumes "cmod u < 1"
  shows "otimes' (1/2) u = half' u"
  by (simp add: assms half)

lemma half_gamma':
  assumes "u\<in>{z. cmod z < 1}"
  shows "otimes' (1 / 2)  u = 
         ((\<gamma> u) / (1 + \<gamma> u)) *  u"
  by (smt (verit, best) assms gamma_factor_def half half'_def norm_of_real of_real_def real_norm_def scaleR_scaleR)
  

definition double' :: "complex \<Rightarrow> complex" where
  "double' v = (if v \<in> {z. cmod z < 1} then (2 * (\<gamma> v)\<^sup>2 / (2 * (\<gamma> v)\<^sup>2 - 1)) *\<^sub>R v else undefined)"

lemma double'_cmod:
  assumes "cmod v < 1"
  shows "2 * (\<gamma> v)\<^sup>2 / (2 * (\<gamma> v)\<^sup>2 - 1) = 2 / (1 + (cmod v)\<^sup>2)" (is "?lhs = ?rhs")
proof-
  have **: "1 - (cmod v)\<^sup>2 > 0"
    using assms
    using real_sqrt_lt_1_iff by fastforce

  have "?lhs = 2 * (1 / (1 - (cmod v)\<^sup>2)) / (2 * (1 / (1 - (cmod v)\<^sup>2)) - 1)"
    using gamma_factor_square_norm[OF assms]
    by simp
  also have "\<dots> = 2 / (1 + (cmod v)\<^sup>2)"
  proof-
    have "2 * (1 / (1 - (cmod v)\<^sup>2)) = 2 / (1 - (cmod v)\<^sup>2)"
      by simp
    moreover
    have "2 * (1 / (1 - (cmod v)\<^sup>2)) - 1 = 2 / (1 - (cmod v)\<^sup>2) -  (1 - (cmod v)\<^sup>2) / (1 - (cmod v)\<^sup>2)"
      using **
      by simp
    then have "2 * (1 / (1 - (cmod v)\<^sup>2)) - 1 = (1 + (cmod v)\<^sup>2) / (1 - (cmod v)\<^sup>2)"
      using **
      by (simp add: field_simps)
    ultimately
    show ?thesis
      using **
      by (smt (verit, del_insts) divide_divide_eq_left nonzero_mult_div_cancel_left power2_eq_square times_divide_eq_right)
  qed
  finally show ?thesis
    .
qed

lemma cmod_double':
  assumes "cmod v < 1"
  shows "cmod (double' v) = 2*cmod v / (1 + (cmod v)\<^sup>2)"
proof-
  have "cmod (double' v) = 
        abs(2 * (\<gamma> v)\<^sup>2 / (2 * (\<gamma> v)\<^sup>2 - 1)) * cmod v"
    unfolding double'_def
    by (simp add: assms)
  also have "\<dots> = abs (2 / (1 + (cmod v)\<^sup>2)) * cmod v"
    using assms double'_cmod 
    by presburger
  also have "\<dots> = 2*cmod v / (1 + (cmod v)\<^sup>2)"
  proof-
    have "2 / (1 + (cmod v)\<^sup>2) > 0"
      by (metis half_gt_zero_iff power_one sum_power2_gt_zero_iff zero_less_divide_iff zero_neq_one)
    then show ?thesis
      by simp
  qed
  finally show ?thesis
    .
qed


lemma double_is_in_domain:
  assumes "v\<in>{z. cmod z < 1}"
  shows "(double' v)\<in>{z. cmod z < 1}"
proof-
  have "cmod (double' v) = 2 * cmod v / (1 + (cmod v)\<^sup>2)"
    using assms cmod_double' by blast
  also have "\<dots> < 1"
  proof-
    have "(1 - cmod v)\<^sup>2 > 0"
      using assms by fastforce
    then have "1 - 2* cmod v + (cmod v)\<^sup>2 > 0"
      by (simp add: field_simps power2_eq_square)
    then have "2*cmod v < 1 + (cmod v)\<^sup>2"
      by simp
    moreover
    have "1 + (cmod v)\<^sup>2 > 0"
      by (smt (verit) not_sum_power2_lt_zero)
    ultimately
    show ?thesis
      using divide_less_eq_1 by blast
  qed
  finally
  show ?thesis
    by simp
qed

lemma double'_otimes'_2:
  assumes "cmod v < 1"
  shows "double' v = otimes' 2 v"
proof-
  have "v * 2 / (1 + cor (cmod v) * cor (cmod v)) =
        v * 4 / (2 + 2 * (cor (cmod v) * cor (cmod v)))"

    by (metis (no_types, lifting) distrib_left_numeral mult_2 nonzero_mult_divide_mult_cancel_left numeral_Bit0 one_add_one times_divide_eq_right zero_neq_numeral)

  then show ?thesis
    using assms
    unfolding double'_def otimes'_def otimes'_k_def double'_cmod[OF assms] scaleR_conv_of_real
    by (auto simp add: field_simps power2_eq_square)
qed

lemma double: 
  assumes "u\<in>{z. cmod z < 1}"
  shows "double' u = otimes' 2  u"
  using assms double'_otimes'_2 by blast


(* ---------------------------------------------------------------------------- *)

interpretation Mobius_iso2: 
  fi_iso2 "{z. cmod z < 1}" 0 oplus_m' ominus_m' gyr_m' otimes' 
"(\<lambda>x. if x \<in>{z. cmod z < 1} then x else undefined)" cmod artanh
  by (smt (verit, ccfv_threshold) Mobius_gyrolinear.gyrolinear_space_axioms Mobius_gyrolinear.normed_gyrolinear_space_axioms Mobius_gyrospace_ax1 fi_iso.intro fi_iso2.intro fi_iso_axioms_def)

definition two_plus::"complex \<Rightarrow> complex \<Rightarrow> complex" where
  "two_plus a b =  (if (a\<in>{z. cmod z<1} \<and> b\<in>{z. cmod z < 1}) then otimes'  (1/(1/2)) (oplus_m' (otimes' (1/2) a) (otimes' (1/2) b))
    else undefined)"

lemma two_plus_help:
  shows " \<forall>a b. two_plus a b =
          (if a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1}
           then otimes' (1/(1/2)) (oplus_m' (otimes' (1/2) a) (otimes' (1/2) b))
           else undefined)"
  using two_plus_def by argo

lemma Einstein_normed:
  shows "normed_gyrolinear_space {z. cmod z < 1} 0 two_plus (\<lambda>x. (if x \<in>{z. cmod z < 1} then ominus_m' x else undefined))
 (\<lambda> a b c. (if ((a\<in>{z. cmod z < 1}) \<and> (b\<in>{z. cmod z < 1})\<and> (c\<in>{z. cmod z < 1})) 
then  otimes' (1/(1/2))  (gyr_m'  (otimes' (1/2)  a) ( otimes' (1/2)  b) (otimes' (1/2)  c)) 
else undefined)
 )  (\<lambda>r a. if a \<in> {z. cmod z < 1} then otimes' r a else undefined)
(\<lambda>x. if x \<in> {z. cmod z < 1} then cmod x
          else undefined) 
(\<lambda>x. if x \<in> cmod ` {z. cmod z < 1} then \<bar>(1/2)\<bar> * artanh x else undefined)"
proof-
  have *:"((1/2)::real) \<noteq> 0"
    by auto
  moreover have "normed_gyrolinear_space {z. cmod z < 1} 0 oplus_m' ominus_m' gyr_m' otimes' cmod artanh"
    using Mobius_gyrolinear.normed_gyrolinear_space_axioms by blast
 
  ultimately show ?thesis
  
    using Mobius_gyrolinear.proposition_3_11[OF `((1/2)::real) \<noteq> 0` two_plus_help]
    by fastforce
qed

lemma Einstein_normed_ok:
  shows " normed_gyrolinear_space {z. cmod z < 1} 0 two_plus
  (\<lambda>x. if x \<in> {z. cmod z < 1} then ominus_m' x else undefined)
  (\<lambda>a b c.
      if a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1} \<and> c \<in> {z. cmod z < 1}
      then otimes' 2
            (gyr_m' (otimes' (1 / 2) a) (otimes' (1 / 2) b) (otimes' (1 / 2) c))
      else undefined)
  (\<lambda>r a. if a \<in> {z. cmod z < 1} then otimes' r a else undefined)
  (\<lambda>x. if x \<in> {z. cmod z < 1} then cmod x else undefined)
  (\<lambda>x. if x \<in> cmod ` {z. cmod z < 1} then \<bar>1 / 2\<bar> * artanh x else undefined)"
proof -
  have f1: "\<And>r ra. (1::real) / (r / ra) = ra / r"
    by simp
  have "\<And>r. (r::real) / 1 = r"
    by simp
  then show ?thesis
    using f1 Einstein_normed by presburger
qed

lemma two_plus_help2:
  shows " \<forall>a b. two_plus a b =
          (if a \<in> {z. cmod z < 1} \<and> b \<in> {z. cmod z < 1}
           then otimes' 2 (oplus_m' (otimes' (1/2) a) (otimes' (1/2) b))
           else undefined)"
  using two_plus_def 
proof -
  have f1: "\<And>r ra. (1::real) / (r / ra) = ra / r"
    by simp
  have "\<And>r. (r::real) / 1 = r"
    by simp
  then show ?thesis
    using f1 two_plus_help by presburger
qed


end