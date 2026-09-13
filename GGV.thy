theory GGV
  imports Main GyroGroup VectorSpace "HOL-Analysis.Inner_Product" HOL.Real_Vector_Spaces
begin

locale ggv_intro = 
  gyrocommutative_gyrogroup +
  fixes scale ::"real \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 105) 
  fixes plus'::"real \<Rightarrow> real \<Rightarrow> real"
  fixes smult'::"real \<Rightarrow> real \<Rightarrow> real"
  fixes fi:: "'a \<Rightarrow> 'b::Real_Vector_Spaces.real_normed_vector"
  fixes plus'_zero::"real"
  assumes fi_inj: "inj_on fi dom"
  assumes scale_closed_ggv: "\<forall>r::real. (\<forall>x\<in>dom. ((scale r x) \<in> dom))"
  assumes scale_1_ggv:"\<forall>a\<in>dom. scale 1 a = a"
  assumes  scale_distrib_ggv: "\<forall>r1::real. \<forall>r2::real. \<forall>a\<in>dom. scale (r1+r2) a = (scale r1 a) \<oplus> (scale r2 a)"
  assumes  scale_assoc_ggv:"\<forall>r1::real. \<forall>r2::real. \<forall>a\<in>dom. scale (r1*r2) a = scale r1 (scale r2 a)"
  assumes one_dim_vs_ggv:"one_dim_vector_space_with_domain {x.\<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} plus' plus'_zero smult'"
  assumes norm_smult'_ggv:"\<forall>r::real.\<forall>a\<in>dom. norm (fi (scale r a)) = smult' \<bar>r\<bar> (norm (fi a))"
begin

definition gyronorm :: "'a \<Rightarrow> real" ("\<llangle>_\<rrangle>" [100] 100) where
  "\<llangle>a\<rrangle> = (if (a\<in>dom) then (norm  (fi a)) else undefined)"

(*definition gyroinner :: "'a \<Rightarrow> 'a \<Rightarrow> real" (infixl "\<cdot>" 100) where
  "a \<cdot> b = (if (a\<in>dom \<and> b\<in>dom) then inner (fi a) (fi b) else undefined)"

lemma norm_inner: 
  assumes "a\<in>dom"
  shows "\<llangle>a\<rrangle> = sqrt (a \<cdot> a)"
  by (simp add: assms gyroinner_def gyronorm_def norm_eq_sqrt_inner)
*)

lemma fi_zero[simp]:
  shows "norm (fi gyrozero) = plus'_zero"
proof-
  have "norm (fi gyrozero) = plus'_zero"
  proof-
    have "norm (fi gyrozero) = norm (fi (scale 0 gyrozero))"
      by (smt (verit, ccfv_threshold) ggv_intro.scale_distrib_ggv ggv_intro_axioms
          gyro_equation_right gyro_left_inv scale_closed_ggv zero_in_dom)
      
    moreover have "norm (fi (scale 0 gyrozero)) = smult' 0 (norm (fi (gyrozero)))"
      by (simp add: norm_smult'_ggv zero_in_dom)
    moreover have "norm (fi gyrozero) =  smult' 0 (norm (fi (gyrozero)))"
      using calculation(1,2) by presburger
    have *:" vector_space_with_domain {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}
     plus' plus'_zero smult'"
      by (simp add: one_dim_vector_space_with_domain.axioms(1) one_dim_vs_ggv)
    ultimately show ?thesis
using mem_Collect_eq one_dim_vector_space_with_domain_def one_dim_vs_ggv
          vector_space_with_domain_def[of "{x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}"
plus' "plus'_zero" smult'] vector_space_with_domain.zero_smult
  by (smt (verit, del_insts) zero_in_dom)

  qed
  then show ?thesis 
    by auto
qed

lemma scale_minus2: 
  assumes "a\<in>dom"
  shows "(scale (-1) a) = gyroinv a"
  using add.right_inverse add_cancel_right_left
  gyrocommutative_gyrogroup.gyro_left_right_cancel
  gyrogroup.gyro_right_id scale_1_ggv scale_distrib_ggv
  by (smt (verit, ccfv_threshold) assms ax1 gyro_right_id oplus_ominus_cancel scale_closed_ggv zero_in_dom)


lemma prop_2_1_vi_a:
  shows "\<forall>a\<in>dom. a\<noteq>gyrozero \<longrightarrow> norm (fi a) \<noteq> 0"
proof(rule ccontr)
  assume "\<not>(\<forall>a\<in>dom. a\<noteq>gyrozero \<longrightarrow> norm (fi a) \<noteq> 0)"
  then have "\<exists>a\<in>dom. a\<noteq>gyrozero \<and> norm (fi a) = 0"
    by blast
  moreover obtain "a" where "a\<in>dom \<and>  a\<noteq>gyrozero \<and> norm (fi a) = 0"
    using \<open>\<not> (\<forall>a\<in>dom. a \<noteq> 0\<^sub>g \<longrightarrow> norm (fi a) \<noteq> 0)\<close> by blast
  moreover  have "norm (fi (\<ominus> a)) = norm (fi (scale (-1) a))"
    using scale_minus2
    using calculation(2) by presburger
      moreover have " norm (fi (scale (-1) a)) = smult' (abs(-1)) (norm (fi a))"
        using  norm_smult'_ggv 
        using calculation(2) by blast
      moreover have "smult' (abs(-1)) (norm (fi a)) = norm (fi a)"
        by (metis abs_minus_cancel calculation(2) norm_smult'_ggv scale_1_ggv)
      moreover have "norm (fi a) = 0"
        by (simp add: calculation(2))
      moreover have "norm (fi (scale (-1) a)) = norm (fi a)"
    
        using calculation(4,5) by presburger
      moreover have "fi a = fi (\<ominus>a)"
        using calculation(3,6,7) by force
      moreover have "a = \<ominus>a"
        by (meson ax1 calculation(2,8) fi_inj inj_on_def)
      moreover have "a = gyrozero"
      proof-
        have "a = scale 1 a"
         
          by (simp add: calculation(2) scale_1_ggv)
        moreover have "scale 1 a = scale (1/2) (scale 2 a) "
          by (metis \<open>a \<in> dom \<and> a \<noteq> 0\<^sub>g \<and> norm (fi a) = 0\<close> eq_divide_eq_numeral1(1) scale_assoc_ggv
              zero_neq_numeral)
        moreover have " scale (1/2) (scale 2 a) = scale (1/2) (scale (1+1) a)"
          by force
        moreover have "scale (1/2) (scale (1+1) a) = scale (1/2) ((\<ominus>a) \<oplus> a)"
          by (metis \<open>a = \<ominus> a\<close> \<open>a \<in> dom \<and> a \<noteq> 0\<^sub>g \<and> norm (fi a) = 0\<close> calculation(1)
              scale_distrib_ggv)
        moreover have "scale (1/2) ((\<ominus>a) \<oplus> a) = scale (1/2) (gyrozero)"
          by (simp add: \<open>a \<in> dom \<and> a \<noteq> 0\<^sub>g \<and> norm (fi a) = 0\<close>)
        ultimately show ?thesis
          by (metis \<open>a \<in> dom \<and> a \<noteq> 0\<^sub>g \<and> norm (fi a) = 0\<close> gyro_inv_id gyro_left_inv
              mult.commute scale_assoc_ggv scale_distrib_ggv scale_minus2 zero_in_dom)
      qed
      ultimately show False 
        by meson
qed

lemma prop_2_1_vi_b:
  shows "\<forall>r::real. \<forall>a\<in>dom. ((r\<noteq>0 \<and> a\<noteq>gyrozero) \<longrightarrow> norm (fi (scale r a)) \<noteq> 0)"
  by (metis gyro_rigth_inv left_inverse mult_zero_right prop_2_1_vi_a scale_1_ggv scale_assoc_ggv
      scale_closed_ggv scale_distrib_ggv scale_minus2)


lemma norm_zero:
  shows "\<llangle>gyrozero\<rrangle> = plus'_zero"
  using gyronorm_def zero_in_dom by force
 
lemma norm_zero_iff:
  assumes "a\<in>dom" "\<llangle>a\<rrangle> = 0"
  shows "a = gyrozero"
  using assms
  using gyronorm_def prop_2_1_vi_a by fastforce

definition norms::"real set"
  where "norms =  gyronorm ` dom \<union> (\<lambda>x. -1 * gyronorm x) ` dom"

end



locale ggv_space =
ggv_intro +   
(*gyrocommutative_gyrogroup +
  fixes scale ::"real \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 105) 
  fixes plus'::"real \<Rightarrow> real \<Rightarrow> real"
  fixes smult'::"real \<Rightarrow> real \<Rightarrow> real"
  fixes fi:: "'a \<Rightarrow> 'b::real_inner" 
  assumes fi_inj: "inj_on fi dom"*)
  assumes scale_prop1_ggv:"\<forall>a\<in>dom. \<forall>r::real. ((a\<noteq>gyrozero \<and> r\<noteq>0)\<longrightarrow> (fi (scale \<bar>r\<bar> a)) /\<^sub>R (norm (fi (scale r a))) = (fi a) /\<^sub>R (norm (fi a)))"
  assumes scale_gyr1_ggv:"\<forall>r::real. \<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>a\<in>dom. gyr u v (scale r a) = scale r (gyr u v a)"
  assumes scale_gyr_id_ggv: "\<forall>r1::real. \<forall>r2::real. \<forall>v\<in>dom. \<forall>x\<in>dom. (gyr (scale r1 v) (scale r2 v) x = x)"

  assumes norm_triangle_ineq_ggv: "\<forall>a\<in>dom. \<forall>b\<in>dom. norm (fi (a \<oplus> b)) \<le> plus' (norm (fi a)) (norm (fi b))"
assumes ax_norm_ggv: "\<forall>u\<in>dom.\<forall>v\<in>dom.\<forall>a\<in>dom. norm (fi(gyr u v a))  = norm (fi a)"
begin
(*
lemma ax_norm_ggv:
  shows "\<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>a\<in>dom. norm (fi (gyr u v a)) = norm (fi a)"
  using inner_gyroauto_invariant norm_eq by blast


definition gyronorm :: "'a \<Rightarrow> real" ("\<llangle>_\<rrangle>" [100] 100) where
  "\<llangle>a\<rrangle> = (if (a\<in>dom) then (norm  (fi a)) else undefined)"
definition gyroinner :: "'a \<Rightarrow> 'a \<Rightarrow> real" (infixl "\<cdot>" 100) where
  "a \<cdot> b = (if (a\<in>dom \<and> b\<in>dom) then inner (fi a) (fi b) else undefined)"

lemma norm_inner: 
  assumes "a\<in>dom"
  shows "\<llangle>a\<rrangle> = sqrt (a \<cdot> a)"
  by (simp add: assms gyroinner_def gyronorm_def norm_eq_sqrt_inner)


lemma to_carrier_zero_iff:
  assumes "a\<in>dom" "fi a = 0"
  shows "a = gyrozero"
proof-
  have "gyrozero \<in> dom"
    by (smt (z3) gyrocommutative_gyrogroup_def gyrogroup_def gyrogroupoid.zero_in_dom gyrovector_space_axioms gyrovector_space_def)
  then show ?thesis using assms fi_zero fi_inj
    by (simp add: inj_onD)
qed


lemma norm_zero:
  shows "\<llangle>gyrozero\<rrangle> = 0"
  using gyronorm_def zero_in_dom by force
 
lemma norm_zero_iff:
  assumes "a\<in>dom" "\<llangle>a\<rrangle> = 0"
  shows "a = gyrozero"
  using assms
  by (simp add: gyronorm_def to_carrier_zero_iff)

definition norms::"real set"
  where "norms =  gyronorm ` dom \<union> (\<lambda>x. -1 * gyronorm x) ` dom"

*)
lemma scale_minus1: 
  assumes "a\<in>dom"
  shows "(scale (-1) a) = gyroinv a"
  using add.right_inverse add_cancel_right_left
  gyrocommutative_gyrogroup.gyro_left_right_cancel
  gyrogroup.gyro_right_id scale_1_ggv scale_distrib_ggv
  by (smt (verit, ccfv_threshold) assms ax1 gyro_right_id oplus_ominus_cancel scale_closed_ggv zero_in_dom)


lemma minus_norm: 
  assumes "a\<in>dom"
  shows "\<llangle>\<ominus>a\<rrangle> = \<llangle>a\<rrangle>"
proof-
  have *:"-1\<noteq>(0::int)"
    by simp
  moreover have " a=  0\<^sub>g \<or> a\<noteq> 0\<^sub>g"
    by blast
  moreover {
    assume "a= 0\<^sub>g"
    then have ?thesis 
      by auto
  }
  moreover {
    assume "a\<noteq> 0\<^sub>g"
    have "scale (-1) a \<in> dom"
      using scale_closed_ggv
      using assms by blast
    let ?minus1 = "-1"
    have " (fi ((scale (abs (-1)) a)) /\<^sub>R \<llangle>(scale (-1) a)\<rrangle>) = ((fi a) /\<^sub>R \<llangle>a\<rrangle>)"
      using scale_prop1_ggv *
      `scale (-1) a \<in> dom` assms
      by (metis \<open>a \<noteq> 0\<^sub>g\<close> gyronorm_def zero_neq_neg_one)
    then have ?thesis 
      using assms prop_2_1_vi_a scale_1_ggv scale_minus1 by fastforce
    }
    ultimately show ?thesis 
      by blast
qed

text \<open>(6.3)\<close>
lemma scale_minus:
  assumes "a\<in>dom"
  shows "scale (-r) a = gyroinv (scale r a)"
  by (metis assms comm_monoid_mult_class.mult_1 minus_mult_commute scale_assoc_ggv
      scale_closed_ggv scale_minus1)
 
lemma scale_minus':
  assumes "a\<in>dom"
  shows "scale k (gyroinv a) = gyroinv (scale k a)"
  using mult.commute scale_assoc_ggv 
  by (metis assms scale_closed_ggv scale_minus1)


lemma zero_otimes [simp]: 
  assumes "x\<in>dom"
  shows "scale 0 x = gyrozero"
  using add.right_inverse gyro_rigth_inv scale_distrib_ggv scale_minus
  by (metis assms scale_1_ggv)


lemma times_zero [simp]: 
  shows "scale t 0\<^sub>g = 0\<^sub>g"
  by (metis mult_cancel_right1 scale_assoc_ggv zero_in_dom zero_otimes)

text \<open>Theorem 6.4 (6.4)\<close>
lemma monodistributive:
  assumes "a\<in>dom"
  shows "scale r ((scale r1  a) \<oplus> (scale r2 a)) =
      (scale r (scale r1  a)) \<oplus> (scale r  (scale r2  a))"
  by (metis assms distrib_left scale_assoc_ggv scale_distrib_ggv)

lemma times2:
  assumes "a\<in>dom"
  shows "scale 2  a = a \<oplus> a"
  using assms mult_2_right scale_1_ggv scale_assoc_ggv scale_distrib_ggv
  by (smt (verit, best))


text "T6.7"
lemma twosum:
  assumes "a\<in>dom" "b\<in>dom"
  shows "scale 2  (a \<oplus> b) = a \<oplus> ((scale 2  b) \<oplus> a)"
proof-
  have "a \<oplus> ((scale 2  b) \<oplus> a) = a \<oplus> ((b \<oplus> b) \<oplus> a)"
    using assms(2) times2 by presburger
  also have "... = a \<oplus> (b \<oplus> (b \<oplus> gyr b b a))"
    using assms(1) assms(2) gyro_right_assoc by auto
  also have "... = a \<oplus> (b \<oplus> (b \<oplus> a))"
    by (simp add: assms(1) assms(2))
  also have "... = (a \<oplus> b) \<oplus> gyr a b (b \<oplus> a)"
    by (meson assms(1) assms(2) gyro_left_assoc gyroplus_closed)
  also have "... = (a \<oplus> b) \<oplus> (a \<oplus> b)"
    using assms(1) assms(2) gyro_commute by fastforce

  finally show ?thesis
    by (simp add: assms(1) assms(2) gyroplus_closed times2)
qed

lemma prop_3_2a:
  assumes "a\<in>dom"
  shows "norm (fi a) = plus'_zero \<longleftrightarrow> a = gyrozero"
proof
  show "norm (fi a) = plus'_zero \<Longrightarrow> a = 0\<^sub>g"
  proof-
    assume "norm (fi a) = plus'_zero"
    show "a= gyrozero"
    proof (rule ccontr)
      assume "a\<noteq>gyrozero"
      then have "(fi (scale \<bar>2\<bar> a)) /\<^sub>R (norm (fi (scale 2 a))) = (fi a) /\<^sub>R (norm (fi a))"
        by (metis assms scale_prop1_ggv zero_neq_numeral)
      moreover have "(norm (fi (scale 2 a))) = norm (fi a)"
        by (metis \<open>norm (fi a) = plus'_zero\<close> assms fi_zero norm_smult'_ggv times_zero
            zero_in_dom)
      moreover have "fi (scale 2 a) = fi a"
        using calculation(1,2) by auto
      moreover have "a\<oplus>a = scale 2 a"
        using assms times2 by auto
      moreover have "a\<oplus>a = a"
        by (metis assms calculation(3,4) fi_inj gyroplus_closed inj_on_def)
      ultimately show False
        by (simp add: \<open>a \<noteq> 0\<^sub>g\<close> assms gyro_equation_right)
      qed
  qed
next
  show "a = 0\<^sub>g \<Longrightarrow> norm (fi a) = plus'_zero"
    using fi_zero by blast
qed

lemma prop_3_2b:
  fixes r::real
  fixes s::real
  assumes "a\<in>dom" "s\<ge>0" "r\<ge>0"
  shows "smult' r (norm (fi a)) = smult' s (norm (fi a)) \<longleftrightarrow> (a = gyrozero \<or> r=s)"
proof
  show "smult' r (norm (fi a)) = smult' s (norm (fi a)) \<Longrightarrow> a = 0\<^sub>g \<or> r = s"
  proof-
    assume "smult' r (norm (fi a)) = smult' s (norm (fi a))"
    show " a = 0\<^sub>g \<or> r = s"
    proof-
    have "smult' r (norm (fi a))  = norm (fi (scale r a))"
      using assms(1,3) norm_smult'_ggv by force
    moreover have "smult' s (norm (fi a))  = norm (fi (scale s a))"
      using assms(1,2) norm_smult'_ggv by force
    moreover have "r=s \<or> a= gyrozero"
    proof(rule ccontr)
      assume "\<not>(r=s \<or> a = gyrozero)"
      then have "r\<noteq>s \<and> a\<noteq>gyrozero"
        by blast
      moreover have "scale r a \<noteq> scale s a"
        by (metis \<open>\<not> (r = s \<or> a = 0\<^sub>g)\<close> assms(1) nonzero_eq_divide_eq real_add_minus_iff
            scale_1_ggv scale_assoc_ggv scale_distrib_ggv times_zero zero_otimes)
      moreover have "fi (scale r a ) \<noteq> fi (scale s a)"
        by (meson assms(1) calculation(2) fi_inj inj_on_eq_iff scale_closed_ggv)
      moreover have "norm (fi (scale r a)) \<noteq> norm (fi (scale s a))"
        by (smt (verit) \<open>\<not> (r = s \<or> a = 0\<^sub>g)\<close> assms(1,2,3) calculation(3)
            inverse_nonzero_iff_nonzero prop_2_1_vi_a prop_3_2a scaleR_cancel_left scale_closed_ggv
            scale_prop1_ggv zero_otimes)
      ultimately show False
        using \<open>smult' r (norm (fi a)) = norm (fi (r \<otimes> a))\<close>
          \<open>smult' r (norm (fi a)) = smult' s (norm (fi a))\<close>
          \<open>smult' s (norm (fi a)) = norm (fi (s \<otimes> a))\<close> by argo
    qed
    ultimately show ?thesis 
      by fastforce
  qed
qed
next
  show "a = 0\<^sub>g \<or> r = s \<Longrightarrow> smult' r (norm (fi a)) = smult' s (norm (fi a))"
    by (metis abs_of_nonneg assms(2,3) norm_smult'_ggv times_zero zero_in_dom)
qed

lemma norm_set_equality:
  shows "{x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} =  gyronorm ` dom \<union> (\<lambda>x. - 1 * \<llangle>x\<rrangle>) ` dom"
proof
  show " {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}
    \<subseteq> gyronorm ` dom \<union> (\<lambda>x. - 1 * \<llangle>x\<rrangle>) ` dom"
    using gyronorm_def by auto
next
  show " gyronorm ` dom \<union> (\<lambda>x. - 1 * \<llangle>x\<rrangle>) ` dom
    \<subseteq> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}"
    using gyronorm_def by auto
qed





definition gyrodistance :: "'a \<Rightarrow> 'a \<Rightarrow> real" ("d\<^sub>\<oplus>") where 
  "d\<^sub>\<oplus> a b = (if (a\<in>dom \<and> b\<in>dom) then \<llangle>\<ominus> a \<oplus> b\<rrangle> else undefined)"

lemma gyrodist1:
  assumes "a\<in>dom" "b\<in>dom"
  shows "d\<^sub>\<oplus> a b = \<llangle>b \<ominus>\<^sub>b a\<rrangle>"
  using gyrodistance_def  gyro_commute ax_norm_ggv assms
  by (metis ax1 gyrominus_def gyronorm_def gyroplus_closed)
  
lemma gyrodistance_metric_nonneg: 
  assumes "a\<in>dom" "b\<in>dom"
  shows "d\<^sub>\<oplus> a b \<ge> 0"
  using gyrodistance_def gyronorm_def
  by (simp add: assms(1) assms(2) ax1 gyroplus_closed)


(*
lemma gyrodistance_metric_zero_iff:
  assumes "a\<in>dom" "b\<in>dom"
  shows "d\<^sub>\<oplus> a b = 0 \<longleftrightarrow> a = b"
  unfolding gyrodistance_def gyronorm_def
  using gyronorm_def norm_zero_iff  fi_zero
  sledgehammer
  by (metis assms(1,2) ax1 gyro_left_inv gyroplus_closed is_normed_gyrolinear''
      normed_gyrolinear_space''.norm_zero oplus_ominus_cancel)
*)  
lemma gyrodistance_metric_sym:
  assumes "a\<in>dom" "b\<in>dom"
  shows "d\<^sub>\<oplus> a b = d\<^sub>\<oplus> b a"
  using gyrodistance_def gyrogroup.gyro_inv_idem gyrogroup.gyrominus_def gyrogroup.gyroplus_inv minus_norm ax_norm_ggv
  by (smt (verit, best) ax1 gyro_inv_idem gyroautomorphic_inverse gyrodist1 gyroplus_closed)
  
lemma gyrodistance_gyrotriangle:
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom"
  shows "d\<^sub>\<oplus> a c \<le> plus' ( d\<^sub>\<oplus> a b)  ( d\<^sub>\<oplus> b c)"
proof-
  have "\<llangle>\<ominus>a \<oplus> c\<rrangle> = \<llangle>(\<ominus>a \<oplus> b) \<oplus> gyr (\<ominus>a) b (\<ominus>b \<oplus> c)\<rrangle>"
    using gyro_polygonal_addition_lemma[of a b c]
    using assms(1) assms(2) assms(3) by presburger
  moreover have "\<llangle>(\<ominus>a \<oplus> b) \<oplus> gyr (\<ominus>a) b (\<ominus>b \<oplus> c)\<rrangle> \<le>  plus' (\<llangle>\<ominus>a \<oplus> b\<rrangle>)  (\<llangle>gyr (\<ominus>a) b (\<ominus>b \<oplus> c)\<rrangle>)"
    by (metis assms(1) assms(2) assms(3) ax1 gyro_translation_1 gyronorm_def gyroplus_closed local.norm_triangle_ineq_ggv)
 
  finally show ?thesis
    unfolding gyrodistance_def ax_norm_ggv
    by (smt (verit, del_insts) assms(1) assms(2) assms(3) ax1 ax_norm_ggv gyro_translation_1 gyronorm_def gyroplus_closed)
qed

text "T6.15"
lemma equation_solving:
  assumes "x\<in>dom" "y\<in>dom" "a\<in>dom" "b\<in>dom"
  assumes "x \<oplus> y = a" "\<ominus> x \<oplus> y = b"
  shows "x =  (1/2)\<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<and> y =(1/2) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<oplus> b"
proof-
  have "y = x \<oplus> b"
    using assms(2) gyro_equation_right 
    using assms(1) assms(6) by force
  then have "a = x \<oplus> (x \<oplus> b)"
    using assms(1) 
    using assms(5) by force
  then have "a = (scale 2 x) \<oplus> b"
    by (metis assms(1) assms(3) assms(4) gyr_commute_misc_3 gyr_id times2)

  then have "x = scale (1/2) (a \<ominus>\<^sub>c\<^sub>b b)"

    by (metis assms(1) assms(4) field_sum_of_halves gyro_equation_left gyroplus_closed mult_2_right scale_1_ggv scale_assoc_ggv scale_closed_ggv)

  then show ?thesis
    using \<open>y = x \<oplus> b\<close>
    by simp
qed

lemma double_plus: 
  assumes "a\<in>dom" "b\<in>dom"
  shows "(scale 2 a) \<oplus> b = a \<oplus> (a \<oplus> b)"
  using assms(1) assms(2) gyro_left_assoc times2 by force


lemma I6_33:
  assumes "a\<in>dom" "b\<in>dom"
  shows "(1/2) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) = (-1/2)\<otimes> (b \<ominus>\<^sub>c\<^sub>b a)"
proof-
  have "scale (-1/2)  (b \<ominus>\<^sub>c\<^sub>b a) = scale (1/2) (scale (-1)  (b \<ominus>\<^sub>c\<^sub>b a))" 
    by (metis assms(1) assms(2) cogyrominus_closed minus_divide_left mult_minus1_right scale_assoc_ggv)
  moreover have "a \<ominus>\<^sub>c\<^sub>b b \<in> dom"
    unfolding cogyrominus_def cogyroplus_def
    by (simp add: assms(1) assms(2) ax1 gyr_inv_3 gyr_misc_3 gyroplus_closed)
  moreover have "gyroinv (a \<ominus>\<^sub>c\<^sub>b b) = b \<ominus>\<^sub>c\<^sub>b a"
    by (metis assms(1) assms(2) ax1 calculation(2) gyro_equation_left gyro_inv_idem oplus_ominus_cancel)
  ultimately show ?thesis
    using scale_minus1
    by (metis gyro_inv_idem scale_minus')
qed

lemma I6_34:
  assumes "a\<in>dom" "b\<in>dom"
  shows "(1/2) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<oplus> b = (1/2)\<otimes> (b \<ominus>\<^sub>c\<^sub>b a) \<oplus> a"

proof-
  have "(a \<ominus>\<^sub>c\<^sub>b b) \<in> dom"
    by (simp add: assms(1) assms(2) ax1 cogyro_plus_def cogyrominus_def gyroplus_closed)
  moreover  have "(b \<ominus>\<^sub>c\<^sub>b a) \<in> dom"
    by (simp add: assms(1) assms(2) ax1 cogyro_plus_def cogyrominus_def gyroplus_closed)
  moreover have "(1/2) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b)   \<in> dom"
    using calculation(1) scale_closed_ggv by blast
    moreover have "(1/2) \<otimes> (b \<ominus>\<^sub>c\<^sub>b a)   \<in> dom"
    using calculation(2) scale_closed_ggv by blast
  moreover have "(1/2) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<oplus> b  \<in> dom"
    using assms(2) calculation(1) gyroplus_closed scale_closed_ggv by blast
    moreover have "(1/2) \<otimes> (b \<ominus>\<^sub>c\<^sub>b a) \<oplus> a  \<in> dom"
      using assms(1) calculation(2) gyroplus_closed scale_closed_ggv by blast
    ultimately show ?thesis 
      by (smt (verit, del_insts) I6_33 assms(1) assms(2) cogyro_right_cancel' double_plus field_sum_of_halves gyro_left_cancel' scale_1_ggv scale_distrib_ggv scale_minus)
  qed


definition collinear :: "'a => 'a => 'a => bool" where
  "collinear x y z \<longleftrightarrow> (if x\<in>dom \<and> y\<in>dom \<and> z\<in> dom then (y = z \<or> (\<exists>t::real. (x = y \<oplus> t \<otimes> (\<ominus> y \<oplus> z))))
else False)"

lemma collinear_aab:
  assumes "a\<in>dom" "b\<in>dom"
  shows "collinear a a b"
  by (metis assms(1,2) ax1 collinear_def gyro_right_id gyroplus_closed
      zero_otimes)

lemma collinear_bab:
  assumes "a\<in>dom" "b\<in>dom"
  shows "collinear b a b"
  by (metis assms(1,2) ax1 collinear_def gyroplus_closed oplus_ominus_cancel
      scale_1_ggv)
 
lemma T6_20:
assumes 
"a\<in>dom" "b\<in>dom" "p1\<in>dom" "p2\<in>dom"
"collinear p1 a b" "collinear p2 a b" "a \<noteq> b" "p1 \<noteq> p2"
  shows "\<forall>x\<in>dom. (collinear x p1 p2 \<longrightarrow> collinear x a b)"
proof safe
  obtain t1 where t1: "p1 = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)"
    using \<open>collinear p1 a b\<close> \<open>a \<noteq> b\<close> collinear_def 
    by meson
  obtain t2 where t2: "p2 = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)"
    using \<open>collinear p2 a b\<close> \<open>a \<noteq> b\<close> collinear_def
    by meson

  fix x
  assume "collinear x p1 p2"
  show "collinear x a b"
  proof-
    obtain t where t: "x = p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2)"
      using \<open>collinear x p1 p2\<close> \<open>p1 \<noteq> p2\<close> collinear_def 
      by meson
    have "x = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> t \<otimes> (\<ominus> (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> (a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)))"
      using t1 t2 t
      by simp
    then have "x = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> t \<otimes> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) ((-t1 + t2) \<otimes> (\<ominus> a \<oplus> b))"
      by (smt (verit, del_insts) assms(1,2) ax1 gyr_def_closed gyro_inv_idem gyro_left_assoc
          gyroplus_closed oplus_ominus_cancel scale_closed_ggv scale_distrib_ggv)
    then have "x = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) ((t*(-t1 + t2)) \<otimes> (\<ominus> a \<oplus> b))"
     
      by (simp add: assms(1,2) ax1 gyroplus_closed scale_assoc_ggv scale_closed_ggv
          scale_gyr1_ggv)
    then have "x = a \<oplus> (t1 \<otimes> (\<ominus> a \<oplus> b) \<oplus> ((t*(-t1 + t2)) \<otimes> (\<ominus> a \<oplus> b)))"
      
      by (simp add: assms(1,2) ax1 gyro_left_assoc gyroplus_closed scale_closed_ggv)
    then  have "x = a \<oplus> (t1 + t*(-t1 + t2)) \<otimes> (\<ominus> a \<oplus> b)"
      
      by (simp add: assms(1,2) ax1 gyroplus_closed scale_distrib_ggv)
    then show ?thesis  
      using collinear_def 
      using assms(1,2) ax1 gyroplus_closed scale_closed_ggv by auto
  qed
qed


lemma T6_20_1:

assumes 
"a\<in>dom" "b\<in>dom" "p1\<in>dom" "p2\<in>dom"
"collinear p1 a b" "collinear p2 a b" "p1 \<noteq> p2" "a \<noteq> b"
  shows "\<forall>x\<in>dom. (collinear x a b \<longrightarrow> collinear x p1 p2)"
proof safe
  obtain t1 where t1: "p1 = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)"
    using \<open>collinear p1 a b\<close> \<open>a \<noteq> b\<close> collinear_def 
    by meson
  obtain t3 where t3: "p2 = a \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b)"
    using \<open>collinear p2 a b\<close> \<open>a \<noteq> b\<close> collinear_def
    by meson

  fix x
  assume "collinear x a b"
  show "collinear x p1 p2" 
  proof-
    obtain t2 where "x = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)"
      using \<open>collinear x a b\<close> \<open>a \<noteq> b\<close> collinear_def
      by meson
    show ?thesis
    proof (cases "t1 = t3")
      case True
      then show ?thesis
        using t1 t3 \<open>p1 \<noteq> p2\<close>
        by blast
    next
      case False
      then obtain t where t: "t = (t2-t1)/(t3-t1)" 
        by simp
      have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> t \<otimes> (\<ominus> (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> ( a \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b)))"
        using t1 t3 by blast
      then have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> t \<otimes> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) (t1 \<otimes> (\<ominus>  (\<ominus> a \<oplus> b)) \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b))"
       
        by (simp add: assms(1,2) ax1 gyro_translation_2a gyroplus_closed scale_closed_ggv
            scale_minus')
      then have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) (((-t1+t3)*t) \<otimes> (\<ominus> a \<oplus> b) )"
      proof-
        have " (t1 \<otimes> (\<ominus>  (\<ominus> a \<oplus> b))) =  ((-t1) \<otimes> ((\<ominus> a \<oplus> b)))"
          
          by (simp add: assms(1,2) ax1 gyroplus_closed scale_minus scale_minus')
        moreover have " (t1 \<otimes> (\<ominus>  (\<ominus> a \<oplus> b)) \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b)) =  (((-t1+t3)) \<otimes> (\<ominus> a \<oplus> b) )"
         
          by (metis assms(1,2) ax1 calculation gyroplus_closed scale_distrib_ggv)
        ultimately show ?thesis 
          by (simp add:
              \<open>p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b) \<oplus> t \<otimes> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) (t1 \<otimes> \<ominus> (\<ominus> a \<oplus> b) \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b))\<close>
              assms(1,2) ax1 gyroplus_closed mult.commute scale_assoc_ggv scale_closed_ggv
              scale_gyr1_ggv)
      qed
         then have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = a \<oplus> (t1 \<otimes> (\<ominus> a \<oplus> b) \<oplus> ((-t1+t3)*t) \<otimes> (\<ominus> a \<oplus> b)) "
        using gyro_left_assoc 
        using assms(1,2) ax1 gyroplus_closed scale_closed_ggv by force
      then have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = a \<oplus> (t1 + (-t1+t3)*t) \<otimes> ((\<ominus> a \<oplus> b))"
        using scale_distrib_ggv
        by (simp add: assms(1,2) ax1 gyroplus_closed)
      moreover have "t1 + (-t1+t3)*t = t2"
        using \<open>t1 \<noteq> t3\<close> t
        by simp
      ultimately
      have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)"
        by blast
      then show ?thesis
        using \<open>x = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)\<close> 
        unfolding collinear_def
        by (metis \<open>collinear x a b\<close> assms(3,4) collinear_def)
    qed
  qed
qed

lemma collinear_sym1:
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom"
   "collinear a b c"
  shows "collinear b a c"
  using T6_20_1 assms collinear_aab collinear_bab collinear_def 
  by metis

lemma collinear_sym2:
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom" "collinear a b c"
  shows "collinear a c b"
  by (metis T6_20 assms collinear_aab collinear_bab)

lemma collinear_transitive:
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom" "d\<in>dom" "collinear a b c" "collinear d b c" "b \<noteq> c"
  shows "collinear a d b" 
  by (metis T6_20 assms collinear_bab collinear_sym1 collinear_sym2)

lemma collinear_translate':
  fixes t::real
  assumes "u\<in>dom" "v\<in>dom" "a\<in>dom" "x\<in> dom"
  shows "x = u \<oplus> t \<otimes> (\<ominus> u \<oplus> v) \<longleftrightarrow>
        (\<ominus> a \<oplus> x) = (\<ominus> a \<oplus> u) \<oplus> t \<otimes> (\<ominus> (\<ominus> a \<oplus> u) \<oplus> (\<ominus> a \<oplus> v))"
  thm gyro_translation_2a
  gyr_misc_2 gyro_right_assoc gyro_translation_2a oplus_ominus_cancel
  by (smt (z3) assms(1,2,3,4) ax1 gyro_left_assoc gyro_translation_2a gyroplus_closed
      oplus_ominus_cancel scale_closed_ggv scale_gyr1_ggv)

definition translate where
  "translate a x = (if a\<in>dom \<and> x\<in>dom then \<ominus> a \<oplus> x else undefined)"

lemma collinear_translate:
  assumes "u\<in>dom" "v\<in>dom" "w\<in>dom" "a\<in>dom"
  shows "collinear u v w \<longleftrightarrow> collinear (translate a u) (translate a v) (translate a w)"
  unfolding collinear_def translate_def
   collinear_translate' gyro_left_cancel'
  by (smt (z3) assms(1,2,3,4) ax1 collinear_translate' gyroplus_closed
      oplus_ominus_cancel)

definition gyroline :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "gyroline a b = {x. collinear x a b}"

definition between :: "'a => 'a => 'a => bool" where
  "between x y z \<longleftrightarrow> (if x\<in>dom\<and>y\<in>dom\<and>z\<in>dom then (\<exists>t::real. 0 \<le> t \<and> t \<le> 1 \<and> y = x \<oplus> t \<otimes> (\<ominus> x \<oplus> z))else False)"


lemma between_xxy [simp]:
  assumes "x\<in>dom" "y\<in>dom"
shows "between x x y"
  unfolding between_def
  using assms(1,2) ax1 gyroplus_closed by auto



lemma between_xyy [simp]:
  assumes "x\<in>dom" "y\<in>dom"
  shows "between x y y"
  unfolding between_def
 using assms(1,2) ax1 gyroplus_closed 
  by (metis dual_order.refl gyro_equation_right
      linordered_nonzero_semiring_class.zero_le_one scale_1_ggv)

lemma between_xyx:
  assumes "x\<in>dom" "y\<in>dom" "between x y x"
  shows "y = x"
  using assms
  unfolding between_def
  by auto

lemma between_translate:
  assumes "u\<in>dom" "v\<in>dom" "w\<in>dom" "a\<in>dom"
  shows "between u v w \<longleftrightarrow> between (translate a u) (translate a v) (translate a w)"
  unfolding between_def translate_def
  using collinear_translate' 
  using assms(1,2,3,4) ax1 gyroplus_closed by presburger

definition distance where
  "distance u v = (if u\<in>dom\<and>v\<in>dom then \<llangle>\<ominus> u \<oplus> v\<rrangle> else undefined)"

lemma distance_translate:
  assumes "u\<in>dom" "v\<in>dom" "a\<in>dom"
  shows "distance u v = distance (translate a u) (translate a v)"
  unfolding distance_def translate_def
  using gyro_translation_2a  
  by (smt (verit, del_insts) assms(1,2,3) ax1 ax_norm_ggv gyronorm_def
      gyroplus_closed)


(*
lemma GGGV_F1:
  shows "\<exists>f. bij_betw f norms UNIV \<and> (\<forall>a\<in>norms. \<forall>b\<in>norms. f(oplus' a b) = (f a) + (f b)) \<and>
(\<forall>r::real. \<forall>a\<in>norms. f (smult' r a) = r*(f a))"
proof-
   let ?g = "\<lambda>y. (THE r. y = smult' r x)"
  have "bij_betw ?g norms UNIV"
  proof-
    have "inj_on ?g norms"
      by (smt (verit, best) \<open>\<forall>y. y \<in> norms \<longrightarrow> (\<exists>!r. y = smult' r x)\<close> inj_on_def the_equality)
    moreover have "\<forall>r::real. \<exists>y. (y\<in> norms_all \<and> y = otimes' r x)"
      by (metis \<open>x \<in> norms_all\<close> ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed)
    moreover have "\<forall>r::real.\<exists>y\<in>norms_all. ?g y = r"
      using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> calculation(2) by blast
    ultimately show ?thesis 
      by (smt (verit, ccfv_threshold) UNIV_eq_I bij_betw_apply inj_on_imp_bij_betw)
  qed
qed*)

lemma GGGV_F1:
  shows "\<exists>f. bij_betw f norms UNIV \<and> (\<forall>a\<in>norms. \<forall>b\<in>norms. f(plus' a b) = (f a) + (f b)) \<and>
(\<forall>r::real. \<forall>a\<in>norms. f (smult' r a) = r*(f a))"
proof-
  obtain "x" where "x\<in>norms \<and> x\<noteq>plus'_zero"
    using gyronorm_def non_trivial_dom norms_def prop_3_2a by auto

  moreover have "x\<in> norms"
    using calculation by blast
  moreover have "x\<noteq>plus'_zero"
    using calculation by blast
  have "\<forall>y. (y\<in>norms \<longrightarrow> (\<exists>!r.(y = smult' r x)))"
  proof
    fix y
    show "(y\<in>norms \<longrightarrow> (\<exists>!r.(y = smult' r x)))"
    proof
    assume "y\<in>norms"
    show "(\<exists>!r.(y = smult' r x))"
    proof-
      have " y \<in> norms \<and> x \<in> norms \<and> x \<noteq> plus'_zero"
     
        using \<open>x \<noteq> plus'_zero\<close> \<open>y \<in> norms\<close> calculation(2) by blast
      moreover have "one_dim_vector_space_with_domain {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}
     plus' plus'_zero smult'"
     
        using one_dim_vs_ggv by force
      moreover have " \<forall>y x. y \<in> norms \<and> x \<in> norms \<and> x \<noteq> plus'_zero \<longrightarrow> (\<exists>!r. y = smult' r x)"
          using one_dim_vector_space_with_domain_axioms_def[of norms plus'_zero smult']
        `one_dim_vector_space_with_domain {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}
     plus' plus'_zero smult'`
     
          by (simp add: norm_set_equality norms_def one_dim_vector_space_with_domain_def)
        ultimately show ?thesis 
          by presburger
      qed
    qed
  qed


  
  let ?g = "\<lambda>y. (THE r. y = smult' r x)"
  have "bij_betw ?g norms UNIV"
  proof-
    have "inj_on ?g norms"
      by (smt (verit, best) \<open>\<forall>y. y \<in> norms \<longrightarrow> (\<exists>!r. y = smult' r x)\<close> inj_on_def the_equality)
    moreover have "\<forall>r::real. \<exists>y. (y\<in> norms \<and> y = smult' r x)"
      using \<open>x \<in> norms\<close>   norms_def  one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed
      by (metis norm_set_equality one_dim_vs_ggv)
    moreover have "\<forall>r::real.\<exists>y\<in>norms. ?g y = r"
      using \<open>\<forall>y. y \<in> norms \<longrightarrow> (\<exists>!r. y = smult' r x)\<close> calculation(2) by blast
    ultimately show ?thesis 
      by (smt (verit, ccfv_threshold) UNIV_eq_I bij_betw_apply inj_on_imp_bij_betw)
  qed
  (*moreover have "?g plus'_zero = 0"
  proof-
    obtain "r" where "plus'_zero = smult' r x"
     
      by (metis Un_upper1 \<open>\<forall>y. y \<in> norms \<longrightarrow> (\<exists>!r. y =smult' r x)\<close> image_subset_iff
          local.norm_zero  norms_def zero_in_dom)
      
    moreover obtain "xx" where "xx \<in> dom \<and> x=norm (fi xx) "
      
      using norms_def 
      using \<open>x \<in> norms \<and> x \<noteq> plus'_zero\<close> 
      sledgehammer
(*(norm' (scale r x)) = otimes' \<bar>r\<bar> (norm' x)*)
    moreover  have "otimes' 0 (norm' xx) = norm' (0 \<otimes> xx)"
      using norm_zero
      by (simp add: calculation(2) norm_scale)
     
    moreover have "otimes' 0 x = 0"
      
      by (smt (verit, del_insts) calculation(2,3) gyro_left_inv local.norm_zero scale_1_ggv
          scale_distrib_ggv scale_minus1_inv zero_in_dom)
   
    ultimately show ?thesis 

      by (smt (verit, del_insts) Un_iff \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close>
          imageI local.norm_zero norms_all_def norms_def the_equality zero_in_dom)
    
  qed*)
  moreover have "\<forall>u.\<forall>v. (u\<in>norms \<and> v\<in>norms \<longrightarrow> ?g (plus' u v) = (?g u) + (?g v))"
  proof
    fix u
    show "\<forall>v. (u\<in>norms \<and> v\<in>norms \<longrightarrow> ?g (plus' u v) = (?g u) + (?g v))"
    proof
      fix v
      show "u\<in>norms \<and> v\<in>norms \<longrightarrow> ?g (plus' u v) = (?g u) + (?g v)"
      proof
        assume "u\<in>norms \<and> v\<in>norms"
        show " ?g (plus' u v) = (?g u) + (?g v)"
        proof-
          obtain "a" where "u = smult' a x"
            using \<open>\<forall>y. y \<in> norms \<longrightarrow> (\<exists>!r. y = smult' r x)\<close> \<open>u \<in> norms \<and> v \<in> norms\<close> by blast
          moreover obtain "b" where "v = smult' b x"
            using \<open>\<forall>y. y \<in> norms \<longrightarrow> (\<exists>!r. y = smult' r x)\<close> \<open>u \<in> norms \<and> v \<in> norms\<close> by blast
          
          moreover have *:"plus' u v = smult' (a+b) x"
          proof-
      have "one_dim_vector_space_with_domain {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}
     plus' plus'_zero smult'"
     
        using one_dim_vs_ggv by force
      then show ?thesis
            using \<open>x \<in> norms\<close>  calculation(1) calculation(2) norms_def norms_def  one_dim_vector_space_with_domain_def vector_space_with_domain.smult_distr_sadd
               using one_dim_vector_space_with_domain_axioms_def[of norms plus'_zero smult']
        `one_dim_vector_space_with_domain {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}
     plus' plus'_zero smult'`
             
               by (metis (lifting) norm_set_equality)
               
           qed
             moreover have "plus' u v \<in> norms"
             
               by (metis "*" \<open>x \<in> norms\<close> norm_set_equality norms_def
                   one_dim_vector_space_with_domain_def one_dim_vs_ggv
                   vector_space_with_domain.smult_closed)
             
         
          moreover have "?g (plus' u v) = (a+b)"
            
            using \<open>\<forall>y. y \<in> norms \<longrightarrow> (\<exists>!r. y = smult' r x)\<close> 
            
          
            using "*" calculation(4) by auto
          
          ultimately show ?thesis 
            by (smt (verit, del_insts) \<open>\<forall>y. y \<in> norms \<longrightarrow> (\<exists>!r. y = smult' r x)\<close> \<open>u \<in> norms \<and> v \<in> norms\<close> the1_equality)
        qed
      qed
    qed
  qed
  moreover have "(\<forall>u.\<forall>r::real. (u\<in>norms \<longrightarrow> ?g (smult' r u) = r*(?g u)))"
  proof
    fix u
    show "\<forall>r::real. (u\<in>norms \<longrightarrow> ?g (smult' r u) = r*(?g u))"
    proof
      fix r
      show "u\<in>norms \<longrightarrow> ?g (smult' r u) = r*(?g u)"
      proof
        assume "u\<in>norms"
        show "?g (smult' r u) = r*(?g u)"
        proof-
          obtain "a" where "u = smult' a x"
            using \<open>\<forall>y. y \<in> norms \<longrightarrow> (\<exists>!r. y = smult' r x)\<close> \<open>u \<in> norms\<close> by blast
          moreover have "smult' r u = smult' (r*a) x"
         
            by (smt (z3) \<open>x \<in> norms\<close> calculation norm_set_equality norms_def
                one_dim_vector_space_with_domain_def one_dim_vs_ggv
                vector_space_with_domain_def)
            
          moreover have "smult' r u \<in> norms"
            
            by (metis \<open>u \<in> norms\<close> norm_set_equality norms_def one_dim_vector_space_with_domain_def
                one_dim_vs_ggv vector_space_with_domain.smult_closed)
           
          moreover have "?g (smult' r u) = (r*a)"
            using \<open>\<forall>y. y \<in> norms \<longrightarrow> (\<exists>!r. y = smult' r x)\<close> calculation(2) calculation(3) by auto
          ultimately show ?thesis 
            by (smt (verit, ccfv_threshold) \<open>\<forall>y. y \<in> norms \<longrightarrow> (\<exists>!r. y = smult' r x)\<close> \<open>u \<in> norms\<close> theI')
        qed
      qed
    qed
  qed
 
  ultimately show ?thesis 
    by blast
qed


definition g_iso::"(real\<Rightarrow>real)\<Rightarrow>bool" where
  "g_iso g \<longleftrightarrow> (bij_betw g norms UNIV  \<and>
  (\<forall>u.\<forall>v. (u\<in>norms \<and> v\<in>norms \<longrightarrow> g (plus' u v) = (g u) + (g v)))
 \<and> (\<forall>u.\<forall>r::real. (u\<in>norms \<longrightarrow> g (smult' r u) = r*(g u))))"

lemma iso_neg_with_real:
  assumes "\<exists>x. (x\<in>norms \<and> x\<noteq>plus'_zero)" (* not trivial domain *)
  shows "g_iso g \<longrightarrow> g_iso (\<lambda>x. -1 * (g x))" 
proof
  assume "g_iso g"
  show " g_iso (\<lambda>x. -1 * (g x))"
  proof-
    have "bij_betw (\<lambda>x. -1 * (g x)) norms UNIV"
    proof-
      have "inj_on (\<lambda>x. -1 * (g x)) norms"
        using  \<open>g_iso g\<close> bij_betw_imp_inj_on g_iso_def inj_on_def
        by (smt (verit))
      
      moreover have "\<forall>r::real.\<exists>y\<in>norms. ((\<lambda>x. -1 * (g x)) y = r)"
        using \<open>g_iso g\<close> bij_betw_iff_bijections g_iso_def minus_equation_iff mult_cancel_right2 mult_minus_left
        by (metis (no_types, opaque_lifting) iso_tuple_UNIV_I)
      ultimately show ?thesis 
        by (metis (mono_tags, lifting) UNIV_eq_I bij_betwE bij_betw_imageI)
    qed
  (*  moreover have " (\<lambda>x. -1 * (g x)) 0 = 0"
      using \<open>g_iso g\<close> g_iso_def by force*)
    moreover have "(\<forall>u.\<forall>v. (u\<in>norms \<and> v\<in>norms \<longrightarrow>  (\<lambda>x. -1 * (g x)) (plus' u v)
 = ( (\<lambda>x. -1 * (g x)) u) + ( (\<lambda>x. -1 * (g x)) v)))"
     
      using \<open>g_iso g\<close> g_iso_def by force
   
    moreover have "(\<forall>u.\<forall>r::real. (u\<in>norms \<longrightarrow>  (\<lambda>x. -1 * (g x)) (smult' r u) = r*( (\<lambda>x. -1 * (g x)) u)))"
      using \<open>g_iso g\<close> g_iso_def by auto
    ultimately show ?thesis 
      using g_iso_def by presburger
  qed
qed


lemma smult'_monotone:
  shows  "\<forall>\<alpha>::real. \<forall>\<beta>::real. \<forall>x\<in>dom. ((0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>) \<longrightarrow> ((smult' \<alpha>  (norm (fi x))) \<le> (smult' \<beta>  (norm (fi x)))))"
  proof
    fix \<alpha> 
    show " \<forall>\<beta>::real. \<forall>x\<in>dom.((0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>) \<longrightarrow> ((smult' \<alpha>  (norm (fi x))) \<le> (smult' \<beta>  (norm (fi x)))))"
    proof
      fix \<beta>
      show " \<forall>x\<in>dom.((0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>) \<longrightarrow> ((smult' \<alpha>  (norm (fi x))) \<le> (smult' \<beta>  (norm (fi x)))))"
      proof
        fix x 
        assume "x\<in>dom"
        show "((0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>) \<longrightarrow>((smult' \<alpha>  (norm (fi x))) \<le> (smult' \<beta>  (norm (fi x)))))"
        proof
          assume "0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>"
          show "((smult' \<alpha>  (norm (fi x))) \<le> (smult' \<beta>  (norm (fi x))))"
          proof-
            have "smult' \<alpha>  (norm (fi x)) = norm (fi (\<alpha> \<otimes> x))"
             
              by (simp add: \<open>0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>\<close> \<open>x \<in> dom\<close> norm_smult'_ggv)
              
            moreover have " norm (fi (\<alpha> \<otimes> x)) = norm (fi (((\<beta>+\<alpha>)/2 - (\<beta>-\<alpha>)/2)\<otimes> x))"
              by (simp add: add_divide_distrib diff_divide_distrib)
            moreover have "norm (fi (((\<beta>+\<alpha>)/2 - (\<beta>-\<alpha>)/2)\<otimes> x)) = 
            norm (fi (((\<beta>+\<alpha>)/2) \<otimes> x \<oplus>  (- (\<beta>-\<alpha>)/2) \<otimes> x ))"
              by (metis \<open>x \<in> dom\<close> divide_minus_left minus_real_def scale_distrib_ggv)
              
            moreover have " norm (fi (((\<beta>+\<alpha>)/2) \<otimes> x \<oplus>  (- (\<beta>-\<alpha>)/2) \<otimes> x ))
        \<le>  plus' (norm (fi (((\<beta>+\<alpha>)/2)\<otimes> x))) (norm (fi ((-(\<beta>-\<alpha>)/2)  \<otimes> x)))"
            
              by (simp add: \<open>x \<in> dom\<close> local.norm_triangle_ineq_ggv scale_closed_ggv)
            moreover have "-(\<beta>-\<alpha>)/2 \<le>0"
              by (simp add: \<open>0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>\<close>)
            moreover have "(\<beta>+\<alpha>)/2 \<ge>0"
              using \<open>0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>\<close> by auto
            moreover have *:"(norm (fi (((\<beta>+\<alpha>)/2)\<otimes> x))) =(smult' ((\<beta>+\<alpha>)/2) (norm (fi x)))"
              
              using \<open>x \<in> dom\<close> calculation(6) norm_smult'_ggv by fastforce
            moreover have " \<bar>-(\<beta>-\<alpha>)/2\<bar> = (\<beta>-\<alpha>)/2 "
              using calculation(5) by force
            moreover have **:"(norm (fi ((-(\<beta>-\<alpha>)/2)\<otimes> x))) =(smult' ((\<beta>-\<alpha>)/2) (norm (fi x)))"
              
              using \<open>x \<in> dom\<close> calculation(8) norm_smult'_ggv by auto
            moreover have "  plus' (norm (fi (((\<beta>+\<alpha>)/2)\<otimes> x))) (norm (fi ((-(\<beta>-\<alpha>)/2)  \<otimes> x))) =
       plus' (smult' ((\<beta>+\<alpha>)/2) (norm (fi x))) (smult' ( (\<beta>-\<alpha>)/2) (norm (fi x))) "
              using * **
              by presburger
            moreover have "plus' (smult' ((\<beta>+\<alpha>)/2) (norm (fi x))) (smult' ( (\<beta>-\<alpha>)/2) (norm (fi x)))
      = smult' ((\<beta>+\<alpha>)/2 + ((\<beta>-\<alpha>)/2)) (norm (fi x))"
              using   one_dim_vector_space_with_domain_def
              vector_space_with_domain.smult_distr_sadd[of norms plus' plus'_zero smult']
              
              using \<open>x \<in> dom\<close> one_dim_vs_ggv vector_space_with_domain.smult_distr_sadd
              by fastforce
            
            moreover have " smult' ((\<beta>+\<alpha>)/2 + ((\<beta>-\<alpha>)/2)) (norm (fi x)) = smult' \<beta> (norm (fi x))"
              by argo
            ultimately show ?thesis 
              by linarith
          qed
        qed
      qed
    qed
  qed

lemma smult'_monotone_stronger:
  shows  "\<forall>\<alpha>::real. \<forall>\<beta>::real. \<forall>x\<in>dom. ((0 \<le> \<alpha> \<and> \<alpha> < \<beta> \<and> x\<noteq>gyrozero) \<longrightarrow> ((smult' \<alpha>  (norm (fi x))) < (smult' \<beta>  (norm (fi x)))))"
proof
 fix \<alpha> 
    show " \<forall>\<beta>::real. \<forall>x\<in>dom.((0 \<le> \<alpha> \<and> \<alpha> < \<beta> \<and> x\<noteq>gyrozero) \<longrightarrow> ((smult' \<alpha>  (norm (fi x))) < (smult' \<beta>  (norm (fi x)))))"
    proof
      fix \<beta>
      show " \<forall>x\<in>dom.((0 \<le> \<alpha> \<and> \<alpha> < \<beta> \<and>  x\<noteq>gyrozero) \<longrightarrow> ((smult' \<alpha>  (norm (fi x))) < (smult' \<beta>  (norm (fi x)))))"
      proof
        fix x 
        assume "x\<in>dom"
        show "((0 \<le> \<alpha> \<and> \<alpha> < \<beta> \<and>  x\<noteq>gyrozero) \<longrightarrow>((smult' \<alpha>  (norm (fi x))) < (smult' \<beta>  (norm (fi x)))))"
        proof
          assume "0 \<le> \<alpha> \<and> \<alpha> < \<beta> \<and>  x\<noteq>gyrozero"
          show "((smult' \<alpha>  (norm (fi x))) < (smult' \<beta>  (norm (fi x))))"
           
            by (smt (verit, del_insts) \<open>0 \<le> \<alpha> \<and> \<alpha> < \<beta> \<and> x \<noteq> 0\<^sub>g\<close> \<open>x \<in> dom\<close> prop_3_2b
                smult'_monotone)
        qed
      qed
    qed
  qed
lemma smult'_monotone_stronger_zero:
  shows  "\<forall>\<alpha>::real.  \<forall>x\<in>dom. ((0 \<le> \<alpha>  \<and> x\<noteq>gyrozero) \<longrightarrow> (0\<le>(smult' \<alpha>  (norm (fi x)))))"
  by (metis abs_of_nonneg norm_ge_zero norm_smult'_ggv)



lemma proof_prop_5_1_implies_plus'_zero_eq_0:
  assumes "x0\<in>dom" "a\<in>norms" "a\<ge>0"
  " bij_betw f norms UNIV \<and> (\<forall>x\<in>norms. \<forall>y\<in>norms. f(plus' x y) = (f x) + (f y)) \<and>
(\<forall>r::real. \<forall>x\<in>norms. f (smult' r x) = r*(f x))" 
"(f a) / f(norm (fi x0)) <0"  " f (norm (fi x0)) > 0"
shows    " smult' (-1) ( norm (fi (scale (-(f (a) / f(norm (fi x0)))) x0))) =
  (-1) * ( norm (fi (scale (-((f a) / f(norm (fi x0)))) x0)))\<longrightarrow> plus'_zero = 0"
proof-
  let ?X = "norm (fi x0)"
  let ?ra = "(f a) / f(norm (fi x0))"
 have "smult' ?ra ?X = smult' ?ra (norm (fi x0))"
   by blast
  moreover have "smult' ?ra ?X = smult' (-1 * (-?ra)) ?X"
    by simp
  moreover have " smult' (-1 * (-?ra)) ?X = smult' (-1) (smult' (-?ra) ?X)"
    by (metis (mono_tags, lifting) assms(1) mem_Collect_eq
        one_dim_vector_space_with_domain_def one_dim_vs_ggv
        vector_space_with_domain.smult_assoc)
  moreover have " smult' (-1) (smult' (-?ra) ?X) = smult' (-1) ((norm (fi (scale (-?ra) x0))))"
    by (metis abs_of_pos assms(1,5) neg_0_less_iff_less norm_smult'_ggv)
 moreover   have "one_dim_vector_space_with_domain {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}
     plus' plus'_zero smult'"
     
        using one_dim_vs_ggv by force
      moreover have *:"vector_space_with_domain {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}
     plus' plus'_zero smult'"
        
        by (simp add: one_dim_vector_space_with_domain.axioms(1) one_dim_vs_ggv)
  ultimately show ?thesis 
    by (smt (verit, ccfv_threshold) Un_upper1 assms(1,2,3,4,5,6)
        bij_betw_iff_bijections gyronorm_def image_subset_iff nonzero_eq_divide_eq
        norm_not_less_zero norm_set_equality norm_smult'_ggv norms_def
        vector_space_with_domain.smult_closed)
  qed



(*
lemma GGV_F1_F2:
  shows "\<exists>f1. bij_betw f1 norms UNIV \<and> (\<forall>a\<in>norms. \<forall>b\<in>norms. f1(plus' a b) = (f1 a) + (f1 b)) \<and>
(\<forall>r::real. \<forall>a\<in>norms. f1 (smult' r a) = r*(f1 a) \<and> (\<forall>a\<in>norms. \<forall>b\<in>norms. (a\<ge>0 \<and> b\<ge>0 \<longrightarrow> 
((0\<le> a \<and> a<b)\<longleftrightarrow> (0\<le> (f1 a) \<and> (f1 a)< (f1 b))))))"
proof-
  obtain "f" where " bij_betw f norms UNIV \<and> (\<forall>a\<in>norms. \<forall>b\<in>norms. f(plus' a b) = (f a) + (f b)) \<and>
(\<forall>r::real. \<forall>a\<in>norms. f (smult' r a) = r*(f a))"
    using GGGV_F1 by blast
  have "g_iso f"
    by (simp add:
        \<open>bij_betw f norms UNIV \<and> (\<forall>a\<in>norms. \<forall>b\<in>norms. f (plus' a b) = f a + f b) \<and> (\<forall>r. \<forall>a\<in>norms. f (smult' r a) = r * f a)\<close>
        g_iso_def)
  have "\<exists>x. x \<in> norms \<and> x \<noteq> plus'_zero"
    using gyronorm_def non_trivial_dom norms_def prop_3_2a by auto
  let ?f_m = "\<lambda>x. -1 * (f x)"
   have *:"bij_betw ?f_m norms UNIV \<and> (\<forall>a\<in>norms. \<forall>b\<in>norms. ?f_m (plus' a b) = (?f_m a) + (?f_m b)) \<and>
(\<forall>r::real. \<forall>a\<in>norms. ?f_m (smult' r a) = r*(?f_m a))"
     using iso_neg_with_real[OF `\<exists>x. x \<in> norms \<and> x \<noteq> plus'_zero`]
  `g_iso f` g_iso_def
     by auto
   moreover obtain "x0" where "x0\<in>dom \<and> f (norm (fi x0)) \<noteq> 0"
     using non_trivial_dom 
     by (smt (verit) Un_upper1 \<open>g_iso f\<close> bij_betw_iff_bijections g_iso_def gyronorm_def
         image_subset_iff norms_def prop_3_2a zero_in_dom)
   
   moreover have "\<exists>f1. bij_betw f1 norms UNIV \<and> (\<forall>a\<in>norms. \<forall>b\<in>norms. f1(plus' a b) = (f1 a) + (f1 b)) \<and>
(\<forall>r::real. \<forall>a\<in>norms. f1 (smult' r a) = r*(f1 a)) \<and> (f1 (norm( fi x0)))>0"

   proof-
     have " (f (norm( fi x0)))>0 \<or>  (f (norm( fi x0)))<0"
       using calculation(2) by force
     moreover {
       assume "(f (norm( fi x0)))>0"
       then have ?thesis
         using
           \<open>bij_betw f norms UNIV \<and> (\<forall>a\<in>norms. \<forall>b\<in>norms. f (plus' a b) = f a + f b) \<and> (\<forall>r. \<forall>a\<in>norms. f (smult' r a) = r * f a)\<close>
         by blast
     } moreover {
       assume " (f (norm( fi x0)))<0"
       then have "(\<lambda>x. -1 * (f x)) (norm (fi x0)) > 0"
         by force
       then have "?thesis" using * 
      
         by blast
     }
     ultimately show ?thesis 
       by blast
     qed
     moreover obtain "f_fin" where "bij_betw f_fin norms UNIV \<and> (\<forall>a\<in>norms. \<forall>b\<in>norms. f_fin(plus' a b) =
 (f_fin a) + (f_fin b)) \<and>
(\<forall>r::real. \<forall>a\<in>norms. f_fin (smult' r a) = r*(f_fin a)) \<and> (f_fin (norm( fi x0)))>0"
     using calculation(3) by presburger

 moreover have "\<forall>\<alpha>::real. \<forall>\<beta>::real. \<forall>x\<in>dom. ((0 < \<alpha> \<and> \<alpha> < \<beta> \<and> x\<noteq>gyrozero) \<longrightarrow> ((smult' \<alpha>  (norm (fi x))) < (smult' \<beta>  (norm (fi x)))))"
   by (simp add: smult'_monotone_stronger)



moreover have "(\<forall>a\<in>norms. \<forall>b\<in>norms. (a\<ge>0 \<and> b\<ge>0 \<longrightarrow>
((0\<le> a \<and> a<b)\<longleftrightarrow> (0\<le> (f_fin a) \<and> (f_fin a)< (f_fin b)))))"
   proof
     fix a
     assume "a\<in>norms"
     show "\<forall>b\<in>norms. (a\<ge>0 \<and> b\<ge>0 \<longrightarrow> 
((0\<le> a \<and> a<b)\<longleftrightarrow> (0\<le> (f_fin a) \<and> (f_fin a)< (f_fin b))))"
     proof
       fix b
       assume "b\<in>norms"
       show "(a\<ge>0 \<and> b\<ge>0 \<longrightarrow> 
((0\<le> a \<and> a<b)\<longleftrightarrow> (0\<le> (f_fin a) \<and> (f_fin a)< (f_fin b))))"
       proof
         assume "a\<ge>0 \<and> b\<ge>0"
         show "((0\<le> a \<and> a<b)\<longleftrightarrow> (0\<le> (f_fin a) \<and> (f_fin a)< (f_fin b)))"
         proof
           let ?X = "norm (fi x0)"
           let ?ra = "(f_fin a) / (f_fin ?X)"
           let ?rb = "(f_fin b) / (f_fin ?X)"
           have "f_fin (smult' ?ra ?X) = ?ra * (f_fin ?X)"
             by (metis (mono_tags, lifting) calculation(2,4) mem_Collect_eq norm_set_equality
                 norms_def)
           moreover have " ?ra * (f_fin ?X) = (f_fin a)"
            
             using
               \<open>bij_betw f_fin norms UNIV \<and> (\<forall>a\<in>norms. \<forall>b\<in>norms. f_fin (plus' a b) = f_fin a + f_fin b) \<and> (\<forall>r. \<forall>a\<in>norms. f_fin (smult' r a) = r * f_fin a) \<and> 0 < f_fin (norm (fi x0))\<close>
             by auto
           moreover have "inj_on f_fin norms"
         
             using
               \<open>bij_betw f_fin norms UNIV \<and> (\<forall>a\<in>norms. \<forall>b\<in>norms. f_fin (plus' a b) = f_fin a + f_fin b) \<and> (\<forall>r. \<forall>a\<in>norms. f_fin (smult' r a) = r * f_fin a) \<and> 0 < f_fin (norm (fi x0))\<close>
               bij_betw_imp_inj_on by blast
           moreover have "f_fin (smult' ?ra ?X) = f_fin a"
             using calculation(1,2) by presburger
           moreover have "(smult' ?ra ?X)\<in> norms"
             
             by (metis (no_types, lifting) Un_upper1 \<open>x0 \<in> dom \<and> f (norm (fi x0)) \<noteq> 0\<close> gyronorm_def
                 image_subset_iff norm_set_equality norms_def one_dim_vector_space_with_domain_def
                 one_dim_vs_ggv vector_space_with_domain.smult_closed)
           moreover have "smult' ?ra ?X = a"
             
             by (meson \<open>a \<in> norms\<close> calculation(3,4,5) inj_onD)
           moreover have "?ra \<ge> 0"
           proof (rule ccontr)
             assume "\<not>(?ra \<ge> 0)"
             then have "?ra < 0"
               by linarith
             moreover have "smult' ?ra ?X = smult' ?ra (norm (fi x0))"
               by blast
             moreover have "smult' (-?ra) ?X  = norm (fi (scale (-?ra) x0))"
               using norm_smult'_ggv
            
               by (smt (verit, del_insts) \<open>\<not> 0 \<le> f_fin a / f_fin (norm (fi x0))\<close>
                   \<open>x0 \<in> dom \<and> f (norm (fi x0)) \<noteq> 0\<close>)
             moreover   have "one_dim_vector_space_with_domain {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}
     plus' plus'_zero smult'"
     
        using one_dim_vs_ggv by force
      moreover have *:"vector_space_with_domain {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}
     plus' plus'_zero smult'"
      
        by (simp add: one_dim_vector_space_with_domain.axioms(1) one_dim_vs_ggv)
      moreover have "smult' ?ra ?X  = smult' (-1) ( norm (fi (scale (-?ra) x0)))"
              using *
        vector_space_with_domain_def[of norms plus' plus'_zero smult']
    
        by (smt (verit, ccfv_threshold) Un_upper1 \<open>x0 \<in> dom \<and> f (norm (fi x0)) \<noteq> 0\<close>
            calculation(3) gyronorm_def image_subset_iff mult_minus_left mult_minus_right
            norm_set_equality norms_def)
      moreover have " smult' (-1) ( norm (fi (scale (-?ra) x0))) =  (-1) * ( norm (fi (scale (-?ra) x0)))\<longrightarrow> plus'_zero = 0"
       
        by (smt (verit, del_insts) \<open>0 \<le> a \<and> 0 \<le> b\<close>
            \<open>smult' (f_fin a / f_fin (norm (fi x0))) (norm (fi x0)) = a\<close>
            \<open>x0 \<in> dom \<and> f (norm (fi x0)) \<noteq> 0\<close> calculation(6) fi_zero norm_eq_zero
            norm_le_zero_iff prop_2_1_vi_a scale_closed_ggv)
      moreover have False
        sorry
    (*     moreover have "smult' ?ra ?X = -1 *smult' (-?ra) ?X  "
               
               using *
        vector_space_with_domain_def
               *)
           qed

     qed
   
    
qed*)


end



end
