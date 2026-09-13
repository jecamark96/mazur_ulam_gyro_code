theory NGL
  imports GyroGroup "HOL-Analysis.Inner_Product" HOL.Real_Vector_Spaces 
 "HOL-Library.Extended_Real" "HOL.Complete_Lattices" Complex_Main VectorSpace
  GGV GV
HOL.Power

begin



locale gyrolinear_space = 
  gyrocommutative_gyrogroup +
  fixes scale :: "real \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 105) 
  assumes scale_closed: "\<forall>r::real. (\<forall>x\<in>dom. ((scale r x) \<in> dom))"
  assumes scale_1: "\<forall>a ::'a\<in>dom. 1 \<otimes> a = a"
  assumes scale_distrib: "\<forall>r1::real.\<forall>r2::real.\<forall>a\<in>dom. (r1 + r2) \<otimes> a = r1 \<otimes> a \<oplus> r2 \<otimes> a"
  assumes scale_assoc: "\<forall>r1::real.\<forall>r2::real.\<forall>a\<in>dom. (r1 * r2) \<otimes> a = r1 \<otimes> (r2 \<otimes> a)"
  assumes gyroauto_property: "\<forall>u\<in>dom.\<forall>v\<in>dom.\<forall>r::real. \<forall>a\<in>dom. gyr u v (r \<otimes> a) = r \<otimes> (gyr u v a)"
  assumes gyroauto_id: "\<forall>r1::real.\<forall>r2::real.\<forall>v\<in>dom. \<forall>x\<in>dom. gyr (r1 \<otimes> v) (r2 \<otimes> v) x = x"
  
begin

lemma scale_minus1_inv:
  assumes "x\<in>dom"
  shows "(-1) \<otimes> x = \<ominus>x"
proof-
  have "(-1 + 1) \<otimes> x = (-1) \<otimes> x \<oplus> 1 \<otimes> x"
    using assms scale_distrib by blast
  moreover have "0\<^sub>g = ((-1) \<otimes> x) \<oplus>  x"
    by (metis add_cancel_left_left assms diff_0 diff_minus_eq_add gyro_left_cancel
        gyro_right_id real_add_minus_iff scale_1 scale_closed scale_distrib
        zero_in_dom)
  ultimately show ?thesis
    by (metis assms ax1 gyro_equation_right gyro_right_id scale_closed zero_in_dom)
qed

lemma two_sum:
  assumes "a\<in>dom" "b\<in>dom"
  shows "2\<otimes>(a\<oplus>b) = a \<oplus> (2\<otimes> b\<oplus> a)"
  by (smt (verit, ccfv_threshold) assms(1,2) gyro_commute gyro_left_assoc gyroauto_id
      gyroplus_closed scale_1 scale_distrib)

lemma two_sum2:
  assumes "a\<in>dom" "b\<in>dom"
  shows "2\<otimes>(a\<oplus>b) = a \<oplus>\<^sub>c (a\<oplus> 2\<otimes> b)"
  by (simp add: assms(1,2) cogyro_commute_misc1 scale_closed two_sum)


end

locale normed_gyrolinear_space = 
  gyrolinear_space + 
  fixes norm'::"'a \<Rightarrow> real"
  fixes f::"real \<Rightarrow> real"
  assumes norm_pos:"\<forall>a\<in>dom. (norm' a \<ge> 0)"
  assumes f_pos:"\<forall>y::real. (y\<in> (norm' ` dom) \<longrightarrow> (f y) \<ge> 0)"
  assumes f_bij: "bij_betw f (norm' ` dom) {x::real. x\<ge>0}"
  assumes f_mon:"\<forall>y::real. \<forall>z::real. (( y\<in> norm' ` dom \<and>
z\<in> norm' ` dom \<and> y>z)\<longrightarrow> (f y) > (f z))"

  assumes "\<forall>x::'a\<in>dom. \<forall>y::'a\<in>dom. f(norm' (gyroplus x y)) \<le> (f (norm' x)) + (f (norm' y))"
  assumes "\<forall>r::real.\<forall>x\<in>dom. f (norm' (scale r x)) = \<bar>r\<bar> * (f (norm' x))"
  assumes "\<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>x\<in>dom. norm' (gyr u v x) = norm' x"
  assumes "\<forall>x::'a\<in>dom. ((norm' x) = 0 \<longleftrightarrow> x = gyrozero)"
begin
  
definition norms::"real set" where 
  "norms = norm' ` dom"

definition norms_neg::"real set" where 
  "norms_neg = (\<lambda>x. -1 * norm' x) ` dom"

definition norms_all::"real set" where 
  "norms_all = norms \<union> norms_neg"

lemma norms_neq_not_empty:
  shows "norms_neg \<noteq> {}"
proof-
  have " \<exists>x.(x\<in>dom \<and> x\<noteq>gyrozero)"
    using non_trivial_dom by force
  then show ?thesis 
    using norms_neg_def by force
qed

  


lemma zero_only_norms_norms_neg:
  assumes "x\<in>norms" "x\<in>norms_neg"
  shows "x=0"
proof-
  have "x\<ge>0"
    using norms_def norm_pos
    using assms(1) by auto
  moreover have "x\<le>0"
     using norms_neg_def norm_pos
     using assms(2) by auto
   ultimately show ?thesis 
     by argo
 qed

lemma order_dom1:
  assumes "x=0" "y\<in>norms_all"
   "x\<ge>y"
 shows "y\<in> norms_neg"
  by (smt (verit, ccfv_threshold) UnE assms(1) assms(2) assms(3) image_iff norm_pos norms_all_def norms_def norms_neg_def)


lemma order_dom1_strict:
  assumes "x=0" "y\<in>norms_all"
   "x>y"
 shows "y\<in> norms_neg"
  by (smt (verit, ccfv_threshold) UnE assms(1) assms(2) assms(3) image_iff norm_pos norms_all_def norms_def norms_neg_def)

lemma order_dom2:
  assumes "x=0" "y\<in>norms_all"
   "y\<ge>0"
 shows "y\<in> norms"
  by (smt (verit, ccfv_threshold) UnE assms(2) assms(3) image_iff norm_pos norms_all_def norms_def norms_neg_def)

lemma a1_a2:
  shows "\<exists>f':: real \<Rightarrow> real. ((\<forall>x::real. \<forall>y::real. ( x\<in>norms_all \<and> y \<in>norms_all \<and> x>y)\<longrightarrow> (f' x) > (f' y))
 \<and> (f' 0) = 0 \<and> bij_betw f' norms_all UNIV)"  
proof-
  let ?f' = "\<lambda>x. if x=0 then 0 else if (x \<in> norms) then (f x) else if (x\<in> norms_neg) then - (f (-x)) else undefined" 
  have fact3: "?f' 0 = 0"
    by auto
  moreover have fact1: "(\<forall>x::real. \<forall>y::real. ( x\<in>norms_all \<and> y \<in>norms_all \<and> x>y)\<longrightarrow> (?f' x) > (?f' y))"
  proof-
    {fix x y 
    assume "x\<in>norms_all \<and> y \<in>norms_all \<and> x>y"
    have "(?f' x) > (?f' y)"
    proof-
      have "x=0 \<or> x\<noteq>0" by blast
      moreover {
        assume "x=0"
        then have "?f' y =  - (f (-y))"
          using \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> order_dom1_strict zero_only_norms_norms_neg by auto
        moreover have "?f' x = 0"
          by (simp add: \<open>x = 0\<close>)
        moreover have "-y\<in>norms"
          by (smt (verit, del_insts) \<open>x = 0\<close> \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> image_iff norms_def norms_neg_def order_dom1_strict)
        moreover have *:"f (-y) \<ge> 0"
          using norms_def f_pos
          using calculation(3) by blast
        moreover have "- f (-y) < 0"
           using *
           by (smt (verit, ccfv_threshold) \<open>x = 0\<close> \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> calculation(3) imageI normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def normed_gyrolinear_space_def norms_def zero_in_dom)
         ultimately have ?thesis 
           by presburger
       }
      moreover {
        assume "x\<noteq>0"
        have "x\<in>norms \<or> x\<in>norms_neg"
          using \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> norms_all_def by force
        moreover {
          assume "x\<in>norms"
          then have "y=0\<or> y\<noteq>0"
            by blast
          moreover {
            assume "y=0"
            then have ?thesis 

              by (smt (verit, best) \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> f_mon f_pos norms_def order_dom2)
              
            }
            moreover {
            assume "y\<noteq>0"
            have "y\<in>norms \<or> y\<in>norms_neg"
              using \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> norms_all_def by auto
            moreover {
              assume "y\<in>norms"
              then have ?thesis 
                using `x\<in>norms` f_mon
                norms_def
                by (simp add: \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close>)
            } moreover {
              assume "y\<in>norms_neg"
              then have "?f' y = - (f (-y))"
                using \<open>y \<noteq> 0\<close> zero_only_norms_norms_neg by fastforce
              moreover have "-y \<in> norms"
                using \<open>y \<in> norms_neg\<close> norms_def norms_neg_def by force
              moreover have "?f' y \<le> 0"
                using calculation(1) calculation(2) f_pos norms_def by force
                
              moreover have "?f' y \<noteq>0"
              proof(rule ccontr)
                assume "\<not>(?f' y \<noteq> 0)"
                then show False 
                  by (smt (verit, best) \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> \<open>y \<noteq> 0\<close> calculation(1) calculation(2) imageI normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def normed_gyrolinear_space_def norms_def order_dom2 zero_in_dom)

              qed
              ultimately have ?thesis 
                by (smt (verit, best) \<open>x \<in> norms\<close> f_pos norms_def)
            }
            ultimately have ?thesis by blast
            }
            ultimately have ?thesis by blast
          } moreover {
            assume "x\<in>norms_neg"
            then have ?thesis 
              by (smt (verit, ccfv_SIG) \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> calculation(2) f_mon image_iff norms_neg_def order_dom1_strict order_dom2 zero_only_norms_norms_neg)

        }
        ultimately have ?thesis by blast
      } ultimately show ?thesis by blast
    qed
  }
  then show ?thesis by blast
qed
  moreover have fact2: " bij_betw ?f' norms_all UNIV"
  proof-
    have *:"\<forall>x. \<forall>y. (x\<in>norms_all \<and> y\<in>norms_all \<and> (?f' x) = (?f' y)) \<longrightarrow> x = y"
      by (smt (verit, ccfv_threshold) calculation(2))
    moreover have **:"\<forall>x::real. \<exists>y. (y\<in> norms_all \<and> ?f' y = x)"
    proof-
      have "\<forall>x::real. (x\<ge>0 \<longrightarrow> (\<exists>y. (y \<in> norms \<and> f y = x )))"
        using norms_def f_bij 
        by (metis bij_betw_iff_bijections mem_Collect_eq)
      
      moreover have "\<forall>x::real. (x<0 \<longrightarrow> (\<exists>y. (y \<in> norms \<and> (f y) =  -x)))"
        by (simp add: calculation)
      moreover have  "\<forall>x::real. (x\<ge>0 \<longrightarrow> (\<exists>y. (y \<in> norms \<and> ?f' y = x )))"
             using norms_def f_bij calculation(1)
        by (smt (verit, best) f_mon image_iff norm_pos)

      moreover have  "\<forall>x::real. (x<0 \<longrightarrow> (\<exists>y. (y \<in> norms_neg \<and> (f (-y)) =  -x)))"
        using calculation(2) norms_def norms_neg_def by auto
      moreover have    "\<forall>x::real. (x<0 \<longrightarrow> (\<exists>y. (y \<in> norms_neg \<and> (?f' (-y)) =  -x)))"
           using norms_def f_bij calculation(1) calculation(4)
      f_mon image_iff norm_pos
           by (smt (verit, ccfv_SIG) norms_neg_def)

      moreover have "\<forall>x::real. (x\<ge> 0 \<or> x<0)"
        by (simp add: linorder_le_less_linear)
      ultimately show ?thesis
      proof -
        { fix rr :: real
          have ff1: "\<forall>r. (r::real) < 0 \<or> 0 \<le> r"
            by (smt (z3))
          have ff2: "\<forall>r ra. sup (ra::real) r = sup r ra"
            by (smt (z3) inf_sup_aci(5))
          have ff3: "\<forall>R Ra. (Ra::real set) \<union> R = R \<union> Ra"
            by (smt (z3) Un_commute)
          have ff4: "\<forall>r ra. (r::real) \<le> sup r ra"
            by simp
          have ff5: "\<forall>R Ra. (R::real set) \<subseteq> Ra \<union> R"
            by (smt (z3) inf_sup_ord(4))
          have ff6: "\<forall>r. (r::real) \<le> r"
            by (smt (z3))
          have ff7: "\<forall>r R Ra. (r::real) \<notin> R \<or> r \<in> Ra \<or> \<not> R \<subseteq> Ra"
            by blast
          have ff8: "\<forall>r. - (- (r::real)) = r"
            using verit_minus_simplify(4) by blast
          have ff9: "- (0::real) = 0"
            by (smt (z3))
          have "\<forall>r ra. r \<notin> norms_all \<or> (if r = 0 then 0 else if r \<in> norms then f r else if r \<in> norms_neg then - f (- r) else undefined) \<noteq> (if ra = 0 then 0 else if ra \<in> norms then f ra else if ra \<in> norms_neg then - f (- ra) else undefined) \<or> ra \<notin> norms_all \<or> r = ra"
            using \<open>\<forall>x y. x \<in> norms_all \<and> y \<in> norms_all \<and> (if x = 0 then 0 else if x \<in> norms then f x else if x \<in> norms_neg then - f (- x) else undefined) = (if y = 0 then 0 else if y \<in> norms then f y else if y \<in> norms_neg then - f (- y) else undefined) \<longrightarrow> x = y\<close> by blast
          then have "\<forall>r. (if r = 0 then 0 else if r \<in> norms then f r else if r \<in> norms_neg then - f (- r) else undefined) \<noteq> (if True then 0 else if 0 \<in> norms then f 0 else if 0 \<in> norms_neg then - f 0 else undefined) \<or> r = 0 \<or> 0 \<notin> norms_all \<or> r \<notin> norms_all"
            using ff9 by (smt (z3))
          then have "(\<exists>r. (if r = 0 then 0 else if r \<in> norms then f r else if r \<in> norms_neg then - f (- r) else undefined) = rr \<and> r \<in> norms_all) \<or> (\<exists>r. (if r = 0 then 0 else if r \<in> norms then f r else if r \<in> norms_neg then - f (- r) else undefined) = rr \<and> r \<in> norms_all)"
            using ff9 ff8 ff7 ff6 ff5 ff4 ff3 ff2 ff1 \<open>\<forall>x<0. \<exists>y. y \<in> norms_neg \<and> f (- y) = - x\<close> \<open>\<forall>x\<ge>0. \<exists>y. y \<in> norms \<and> (if y = 0 then 0 else if y \<in> norms then f y else if y \<in> norms_neg then - f (- y) else undefined) = x\<close> \<open>\<forall>x\<ge>0. \<exists>y. y \<in> norms \<and> f y = x\<close> if_True norms_all_def zero_only_norms_norms_neg by moura }
        then show ?thesis
          by blast
      qed
      
    qed
    moreover have "inj_on ?f' norms_all"
      using "*" inj_on_def by blast
    moreover have ***:"\<forall>x::real. \<exists>y\<in>norms_all. (?f' y = x)"
      using "**" by blast
    moreover have "?f' ` norms_all = UNIV"
    proof-
      have "?f' ` norms_all \<subseteq> UNIV"
        by blast
      moreover have "UNIV \<subseteq> ?f' ` norms_all"
      proof-
        fix x::real
        have "\<exists>y\<in>norms_all. (?f' y = x)"
          using "**" by blast
        then have "x \<in> (?f' ` norms_all)"
          by blast
        then have "\<forall>x::real. (x \<in> (?f' ` norms_all))"
          by (smt (verit, del_insts) "**" image_iff)
        then show ?thesis 
          by blast
      qed
      ultimately show ?thesis
        by force
    qed
    ultimately show " bij_betw ?f' norms_all UNIV" 
      using bij_betw_def by blast
  qed
 
  moreover have fact_fin: " ((\<forall>x::real. \<forall>y::real. ( x\<in>norms_all \<and> y \<in>norms_all \<and> x>y)\<longrightarrow> (?f' x) > (?f' y))
 \<and> (?f' 0) = 0 \<and> bij_betw ?f' norms_all UNIV)"
    using fact1 fact2 by argo
  
  ultimately show ?thesis
    using fact_fin
    by (smt (verit, del_insts))
qed


end

locale normed_gyrolinear_space' = 
  gyrolinear_space + 
  fixes norm'::"'a \<Rightarrow> real"
  fixes f'::"real \<Rightarrow> real"
  assumes norm_pos:"\<forall>a\<in>dom. (norm' a \<ge> 0)"
  assumes f'_bij:"bij_betw f' ((norm' ` dom) \<union> ((\<lambda>x. -1 * norm' x) ` dom)) UNIV"
  assumes f'_mon: "\<forall>y::real. \<forall>z::real. (( y\<in>  ((norm' ` dom) \<union> ((\<lambda>x. -1 * norm' x) ` dom)) \<and>
z\<in>  ((norm' ` dom) \<union> ((\<lambda>x. -1 * norm' x) ` dom)) \<and> y>z)\<longrightarrow> (f' y) > (f' z))"
  assumes "f' 0 = 0"
  assumes f'_r2: "\<forall>x::'a\<in>dom. \<forall>y::'a\<in>dom. f'(norm' (gyroplus x y)) \<le> (f' (norm' x)) + (f' (norm' y))"
  assumes f'_r3:"\<forall>r::real. \<forall>x\<in>dom. f' (norm' (scale r x)) = \<bar>r\<bar> * (f' (norm' x))"
  assumes norm_gyr:"\<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>x\<in>dom. norm' (gyr u v x) = norm' x"
  assumes norm_zero:"\<forall>x::'a\<in>dom. ((norm' x) = 0 \<longleftrightarrow> x = gyrozero)"
begin

definition norms::"real set" where 
  "norms = norm' ` dom"

definition norms_neg::"real set" where 
  "norms_neg = (\<lambda>x. -1 * norm' x) ` dom"

definition norms_all::"real set" where 
  "norms_all = norms \<union> norms_neg"

lemma norms_neq_not_empty:
  shows "norms_neg \<noteq> {}"
proof-
  have " \<exists>x.(x\<in>dom \<and> x\<noteq>gyrozero)"
    using non_trivial_dom by force
  then show ?thesis 
    using norms_neg_def by force
qed

  


lemma zero_only_norms_norms_neg:
  assumes "x\<in>norms" "x\<in>norms_neg"
  shows "x=0"
proof-
  have "x\<ge>0"
    using norms_def norm_pos
    using assms(1) by auto
  moreover have "x\<le>0"
     using norms_neg_def norm_pos
     using assms(2) by auto
   ultimately show ?thesis 
     by argo
 qed

lemma order_dom1:
  assumes "x=0" "y\<in>norms_all"
   "x\<ge>y"
 shows "y\<in> norms_neg"
  by (smt (verit, ccfv_threshold) UnE assms(1) assms(2) assms(3) image_iff norm_pos norms_all_def norms_def norms_neg_def)


lemma order_dom1_strict:
  assumes "x=0" "y\<in>norms_all"
   "x>y"
 shows "y\<in> norms_neg"
  by (smt (verit, ccfv_threshold) UnE assms(1) assms(2) assms(3) image_iff norm_pos norms_all_def norms_def norms_neg_def)

lemma order_dom2:
  assumes "x=0" "y\<in>norms_all"
   "y\<ge>0"
 shows "y\<in> norms"
  by (smt (verit, ccfv_threshold) UnE assms(2) assms(3) image_iff norm_pos norms_all_def norms_def norms_neg_def)


definition norm_oplus_f::"real \<Rightarrow> real \<Rightarrow> real" (infixl " \<oplus>\<^sub>f" 105)
  where "a \<oplus>\<^sub>f b = (if (a\<in>norms_all \<and> b\<in>norms_all) then (inv_into norms_all f') ((f' a) + (f' b))
else undefined)"


definition norm_otimes_f::"real \<Rightarrow> real \<Rightarrow> real" (infixl "\<otimes>\<^sub>f" 105)
  where "r \<otimes>\<^sub>f a = (if (a\<in>norms_all) then (inv_into norms_all f') (r * (f' a))
else undefined)"

lemma vector_space_of_norms:
  shows "vector_space_with_domain norms_all norm_oplus_f 0 norm_otimes_f"
proof
  fix x y
  show "x \<in> norms_all \<Longrightarrow> y \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y \<in> norms_all"
  proof-
    assume "x\<in>norms_all"
    show "y \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y \<in> norms_all"
    proof-
      assume "y\<in>norms_all"
      show "x  \<oplus>\<^sub>f y \<in> norms_all"
              by (metis UNIV_I \<open>x \<in> norms_all\<close> \<open>y \<in> norms_all\<close> bij_betw_imp_surj_on f'_bij inv_into_into norm_oplus_f_def norms_all_def norms_def norms_neg_def)

    qed
  qed
next
  show "0 \<in> norms_all"

    using local.norm_zero norms_all_def norms_def zero_in_dom by fastforce
 
next 
  fix x y z
  show " x \<in> norms_all \<Longrightarrow>
       y \<in> norms_all \<Longrightarrow> z \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z)"
  proof-
    assume "x\<in>norms_all"
    show " y \<in> norms_all \<Longrightarrow> z \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z)"
    proof-
      assume "y \<in> norms_all"
      show "z \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z)"
      proof-
        assume "z \<in> norms_all"
        show " x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z)"
        proof-
          have " x  \<oplus>\<^sub>f y = (inv_into norms_all f') ((f' x) + (f' y))"
            by (simp add: \<open>x \<in> norms_all\<close> \<open>y \<in> norms_all\<close> norm_oplus_f_def)
          moreover have "x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = (inv_into norms_all f') ((
        f' ( (inv_into norms_all f') ((f' x) + (f' y)))) + (f' z))"
            by (metis \<open>z \<in> norms_all\<close> bij_betw_def calculation f'_bij inv_into_into iso_tuple_UNIV_I norm_oplus_f_def norms_all_def norms_def norms_neg_def)
            
          moreover have "x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = (inv_into norms_all f') (((f' x)+ (f' y))+(f' z))"
            by (metis bij_betw_def calculation(2) f'_bij f_inv_into_f iso_tuple_UNIV_I norms_all_def norms_def norms_neg_def)
          
          moreover have " (y  \<oplus>\<^sub>f z) =  (inv_into norms_all f') ((f' y) + (f' z))"
            by (simp add: \<open>y \<in> norms_all\<close> \<open>z \<in> norms_all\<close> norm_oplus_f_def)
          moreover have " x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z) = (inv_into norms_all f') ((f' x) + 
        (f' ((inv_into norms_all f') ((f' y) + (f' z)))))"
            by (metis UNIV_I \<open>x \<in> norms_all\<close> bij_betw_imp_surj_on calculation(4) f'_bij inv_into_into norm_oplus_f_def norms_all_def norms_def norms_neg_def)
            
          moreover have " x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z) = (inv_into norms_all f') ((f' x) + 
          ((f' y) + (f' z)))"
            using bij_betw_inv_into_right calculation(5) f'_bij norms_all_def norms_def norms_neg_def by fastforce
          ultimately show ?thesis 
            by argo
        qed
      qed
    qed
  qed
next
  fix x y
  show "x \<in> norms_all \<Longrightarrow> y \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y = y  \<oplus>\<^sub>f x"
  proof-
    assume "x\<in> norms_all"
    show "y \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y = y  \<oplus>\<^sub>f x"
    proof-
      assume "y \<in> norms_all"
      show " x \<oplus>\<^sub>f y = y \<oplus>\<^sub>f x"
        by (simp add: add.commute norm_oplus_f_def)
    qed
  qed
next 
  fix x
  show " x \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f 0 = x"
  proof-
    assume "x\<in>norms_all"
    show "x  \<oplus>\<^sub>f 0 = x"
    proof-
      have "x  \<oplus>\<^sub>f 0  = (inv_into norms_all f')  ((f' x) + (f' 0))"

        by (metis UnI1 \<open>x \<in> norms_all\<close> image_eqI local.norm_zero normed_gyrolinear_space'.norm_oplus_f_def normed_gyrolinear_space'_axioms norms_all_def norms_def zero_in_dom)
      moreover have "(f' x) + (f' 0) = (f' x)"
        by (smt (verit, ccfv_SIG) normed_gyrolinear_space'_axioms normed_gyrolinear_space'_axioms_def normed_gyrolinear_space'_def)
      ultimately show ?thesis
        by (metis \<open>x \<in> norms_all\<close> bij_betw_inv_into_left f'_bij norms_all_def norms_def norms_neg_def)
      
    qed
  qed
next 
  fix x
  show "x \<in> norms_all \<Longrightarrow> \<exists>y\<in>norms_all. x  \<oplus>\<^sub>f y = 0"
  proof-
    assume "x\<in>norms_all"
    show " \<exists>y\<in>norms_all. x  \<oplus>\<^sub>f y = 0"
    proof-
      let ?y = "(inv_into norms_all f') (-(f' x))"
      have " x  \<oplus>\<^sub>f ?y = (inv_into norms_all f') ((f' x) + (f' ?y))"
        by (metis UNIV_I \<open>x \<in> norms_all\<close> bij_betw_imp_surj_on f'_bij inv_into_into norm_oplus_f_def norms_all_def norms_def norms_neg_def)
      moreover have " x  \<oplus>\<^sub>f ?y = (inv_into norms_all f') ((f' x) + (-(f' x)))"
        by (metis UNIV_I bij_betw_imp_surj_on calculation f'_bij f_inv_into_f norms_all_def norms_def norms_neg_def)
      moreover have "x  \<oplus>\<^sub>f ?y =(inv_into norms_all f') 0"
        using calculation(2) by force
      moreover have "x  \<oplus>\<^sub>f ?y = 0"
        by (smt (verit, ccfv_threshold) bij_betw_def calculation(2) f'_bij image_subset_iff inv_into_f_eq normed_gyrolinear_space'_axioms normed_gyrolinear_space'_axioms_def normed_gyrolinear_space'_def norms_all_def norms_def norms_neg_def sup.cobounded1 zero_in_dom)
      moreover have "?y \<in> norms_all"
        by (metis bij_betw_def f'_bij inv_into_into iso_tuple_UNIV_I norms_all_def norms_def norms_neg_def)
      ultimately show ?thesis
        by blast
    qed
  qed
next
  fix x a
  show "x \<in> norms_all \<Longrightarrow> a \<otimes>\<^sub>f x \<in> norms_all"
  proof-
    assume "x\<in>norms_all"
    show " a \<otimes>\<^sub>f x \<in> norms_all"
      by (metis \<open>x \<in> norms_all\<close> bij_betw_imp_surj_on bij_betw_inv_into f'_bij norm_otimes_f_def norms_all_def norms_def norms_neg_def rangeI)

  qed
next 
  fix x a b
  show "x \<in> norms_all \<Longrightarrow> (a + b) \<otimes>\<^sub>f x = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (b \<otimes>\<^sub>f x)"
  proof-
    assume "x\<in>norms_all"
    show "(a + b) \<otimes>\<^sub>f x = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (b \<otimes>\<^sub>f x)"
    proof-
      have "(a + b) \<otimes>\<^sub>f x = (inv_into norms_all f') ((a+b) * (f' x))"
        using \<open>x \<in> norms_all\<close> norm_otimes_f_def by presburger
      moreover have "(a + b) \<otimes>\<^sub>f x = (inv_into norms_all f') (a*(f' x) + b*(f' x))"
        using calculation by argo
      moreover have *:" a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (b \<otimes>\<^sub>f x) = (inv_into norms_all f')
      ((f' (a \<otimes>\<^sub>f x)) + (f' (b \<otimes>\<^sub>f x)))" 
        by (smt (verit, ccfv_SIG) \<open>x \<in> norms_all\<close> bij_betw_imp_surj_on bij_betw_inv_into f'_bij normed_gyrolinear_space'.norm_oplus_f_def normed_gyrolinear_space'.norm_otimes_f_def normed_gyrolinear_space'_axioms norms_all_def norms_def norms_neg_def rangeI)
    
      moreover have **:" (inv_into norms_all f')
      ((f' (a \<otimes>\<^sub>f x)) + (f' (b \<otimes>\<^sub>f x))) = (inv_into norms_all f')
    ((f' ((inv_into norms_all f') (a*(f' x)))) +
    (f' ((inv_into norms_all f') (b*(f' x)))))"
        using \<open>x \<in> norms_all\<close> norm_otimes_f_def by presburger
      moreover have "a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (b \<otimes>\<^sub>f x) = (inv_into norms_all f') ((a*(f' x)) + (b*(f' x)))"
        using * **
        by (metis UNIV_I bij_betw_inv_into_right f'_bij norms_all_def norms_def norms_neg_def)
       
      ultimately show ?thesis 
        by presburger
    qed
  qed
next
  fix x a b
  show " x \<in> norms_all \<Longrightarrow> a \<otimes>\<^sub>f (b \<otimes>\<^sub>f x) = (a * b) \<otimes>\<^sub>f x"
  proof-
    assume "x\<in>norms_all"
    show "a \<otimes>\<^sub>f (b \<otimes>\<^sub>f x) = (a * b) \<otimes>\<^sub>f x"
      by (smt (verit, best) UNIV_I \<open>x \<in> norms_all\<close> ab_semigroup_mult_class.mult_ac(1) bij_betw_imp_surj_on bij_betw_inv_into f'_bij f_inv_into_f norm_otimes_f_def norms_all_def norms_def norms_neg_def rangeI)
    
  qed
next 
  fix x
  show "x \<in> norms_all \<Longrightarrow> 1 \<otimes>\<^sub>f x = x"
  proof-
    assume "x\<in>norms_all"
    show " 1 \<otimes>\<^sub>f x = x"
    proof-
      have " 1 \<otimes>\<^sub>f x = (inv_into norms_all f') (1*(f' x))"
        using \<open>x \<in> norms_all\<close> norm_otimes_f_def by presburger
      then show ?thesis 
        by (metis \<open>x \<in> norms_all\<close> bij_betw_inv_into_left f'_bij mult_1 norms_all_def norms_def norms_neg_def)
        
    qed
  qed
next
  show "\<And>x y a.
       x \<in> norms_all \<Longrightarrow> y \<in> norms_all \<Longrightarrow> a \<otimes>\<^sub>f (x  \<oplus>\<^sub>f y) = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (a \<otimes>\<^sub>f y) "
  proof-
    fix x y a
    show " x \<in> norms_all \<Longrightarrow> y \<in> norms_all \<Longrightarrow> a \<otimes>\<^sub>f (x  \<oplus>\<^sub>f y) = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (a \<otimes>\<^sub>f y)"
    proof-
      assume "x \<in> norms_all"
      show " y \<in> norms_all \<Longrightarrow> a \<otimes>\<^sub>f (x  \<oplus>\<^sub>f y) = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (a \<otimes>\<^sub>f y)"
      proof-
       assume "y \<in> norms_all"
      show "  a \<otimes>\<^sub>f (x  \<oplus>\<^sub>f y) = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (a \<otimes>\<^sub>f y)"
      proof-
        have "a \<otimes>\<^sub>f (x  \<oplus>\<^sub>f y) = (inv_into norms_all f') (a*(f' (x  \<oplus>\<^sub>f y)))"
          by (metis UNIV_I \<open>x \<in> norms_all\<close> \<open>y \<in> norms_all\<close> bij_betw_imp_surj_on f'_bij
              inv_into_into norm_oplus_f_def norm_otimes_f_def norms_all_def norms_def
              norms_neg_def)
        moreover have " (inv_into norms_all f') (a*(f' (x  \<oplus>\<^sub>f y))) =
(inv_into norms_all f') (a* f' ((inv_into norms_all f')  ((f' x) + (f' y))))"
          by (simp add: \<open>x \<in> norms_all\<close> \<open>y \<in> norms_all\<close> norm_oplus_f_def)
        moreover have "(inv_into norms_all f') (a* f' ((inv_into norms_all f')  ((f' x) + (f' y)))) =
(inv_into norms_all f') (a* ((f' x) + (f' y)))"
          by (metis UNIV_I bij_betw_imp_surj_on f'_bij f_inv_into_f norms_all_def norms_def
              norms_neg_def)
        moreover have "a \<otimes>\<^sub>f (x  \<oplus>\<^sub>f y) = (inv_into norms_all f') (a* (f' x) + a*(f' y)) "
          by (simp add: calculation(1,2,3) distrib_left)
        moreover have " a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (a \<otimes>\<^sub>f y) = (inv_into norms_all f') ( ((f' (a \<otimes>\<^sub>f x)) + (f' (a \<otimes>\<^sub>f y))))"
          
          by (metis UNIV_I \<open>x \<in> norms_all\<close> \<open>y \<in> norms_all\<close> bij_betw_imp_surj_on f'_bij
              inv_into_into norm_oplus_f_def norm_otimes_f_def norms_all_def norms_def
              norms_neg_def)
        ultimately show ?thesis 
          by (metis (lifting) UNIV_I \<open>x \<in> norms_all\<close> \<open>y \<in> norms_all\<close> bij_betw_imp_surj_on f'_bij
              f_inv_into_f norm_otimes_f_def norms_all_def norms_def norms_neg_def)
      qed
    qed
  qed
    qed
  qed 



lemma r2:
  assumes "x\<in>dom" "y\<in>dom"
  shows "norm' (x \<oplus> y) \<le> (norm' x)  \<oplus>\<^sub>f (norm' y)"
proof-
    have " (f' (norm' (x \<oplus> y))) \<le> (f' (norm' x)) + (f' (norm' y))"
      using assms(1) assms(2) f'_r2 by blast
    moreover have "(inv_into norms_all f' (f' (norm' (x \<oplus> y)))) \<le> 
(inv_into norms_all f' ((f' (norm' x)) + (f' (norm' y))))"
      by (smt (verit, best) UNIV_I bij_betw_imp_surj_on calculation f_inv_into_f inv_into_into normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_axioms_def normed_gyrolinear_space'_def norms_all_def norms_def)

    ultimately show ?thesis   
      by (metis assms(1) assms(2) bij_betw_def f'_bij gyroplus_closed image_subset_iff inv_into_f_eq norm_oplus_f_def norms_all_def norms_def norms_neg_def sup.cobounded1)

qed

lemma r3:
  fixes r::real
  assumes "x\<in>dom"
  shows "norm' (r  \<otimes>  x) =  \<bar>r\<bar> \<otimes>\<^sub>f (norm' x)"
  by (smt (verit, del_insts) Un_iff assms bij_betw_imp_inj_on f'_bij f'_r3 image_eqI inv_into_f_eq norm_otimes_f_def norms_all_def norms_def norms_neg_def scale_closed)


lemma one_dim_vs:
  shows "one_dim_vector_space_with_domain norms_all norm_oplus_f 0 norm_otimes_f"
proof-
  have step1: "vector_space_with_domain  norms_all norm_oplus_f 0 norm_otimes_f"
    using vector_space_of_norms by auto
  moreover have step2: "\<forall>y. \<forall>x. (y\<in> norms_all \<and>
 x\<in> norms_all \<and> x\<noteq>0 \<longrightarrow> (\<exists>!r::real. y = r \<otimes>\<^sub>f x))"
  proof
    fix y
    show " \<forall>x. (y\<in> norms_all \<and>
 x\<in> norms_all \<and> x\<noteq>0 \<longrightarrow> (\<exists>!r::real. y = r \<otimes>\<^sub>f x))"
    proof
      fix x
      show "y\<in> norms_all \<and>
 x\<in> norms_all \<and> x\<noteq>0 \<longrightarrow> (\<exists>!r::real. y = r \<otimes>\<^sub>f x)"
      proof
        assume "y\<in> norms_all \<and>
 x\<in> norms_all \<and> x\<noteq>0"
        show "(\<exists>!r::real. y = r \<otimes>\<^sub>f x)"
        proof-
          have "(\<exists>r::real. y = r \<otimes>\<^sub>f x)"
          proof-
            let ?r = "f'(y)/f'(x)"
            have "?r \<otimes>\<^sub>f x = (inv_into norms_all f') (?r * (f' x))"
              by (simp add: \<open>y \<in> norms_all \<and> x \<in> norms_all \<and> x \<noteq> 0\<close> norm_otimes_f_def)
            moreover have " (inv_into norms_all f') (?r * (f' x)) = y"
              by (smt (verit, best) \<open>y \<in> norms_all \<and> x \<in> norms_all \<and> x \<noteq> 0\<close> bij_betw_inv_into_left f'_bij nonzero_eq_divide_eq normed_gyrolinear_space'_axioms normed_gyrolinear_space'_axioms_def normed_gyrolinear_space'_def norms_all_def norms_def norms_neg_def vector_space_of_norms vector_space_with_domain.zero_in_dom)
            ultimately show ?thesis
              by metis
             
          qed
          
          moreover have "\<forall>r1.\<forall>r2. (y = r1 \<otimes>\<^sub>f x \<and> y = r2 \<otimes>\<^sub>f x \<longrightarrow> r1=r2)"
          proof
            fix r1 
            show "\<forall>r2. y = r1 \<otimes>\<^sub>f x \<and> y = r2 \<otimes>\<^sub>f x \<longrightarrow> r1=r2"
            proof
              fix r2 
              show "y = r1 \<otimes>\<^sub>f x \<and> y = r2 \<otimes>\<^sub>f x \<longrightarrow> r1=r2"
              proof
                assume "y = r1 \<otimes>\<^sub>f x \<and> y = r2 \<otimes>\<^sub>f x "
                show "r1=r2"
                proof-
                        have "r1 \<otimes>\<^sub>f x = (inv_into norms_all f') (r1 * (f' x))"
            by (simp add: \<open>y \<in> norms_all \<and> x \<in> norms_all \<and> x \<noteq> 0\<close> norm_otimes_f_def)
          moreover have "r2 \<otimes>\<^sub>f x = (inv_into norms_all f') (r2 * (f' x))"
            using \<open>y \<in> norms_all \<and> x \<in> norms_all \<and> x \<noteq> 0\<close> norm_otimes_f_def by presburger
          moreover 
            have "(inv_into norms_all f') (r1 * (f' x)) = (inv_into norms_all f') (r2 * (f' x))"
              using \<open>y = r1 \<otimes>\<^sub>f x \<and> y = r2 \<otimes>\<^sub>f x\<close> calculation(1) calculation(2) by fastforce
            moreover have" f' ( (inv_into norms_all f') (r1 * (f' x))) =
        f'( (inv_into norms_all f') (r2 * (f' x)))"
              using calculation by presburger
            moreover have "r1* (f' x) = r2* (f' x)"
              by (metis UNIV_I bij_betw_imp_surj_on calculation(3) f'_bij inv_into_injective norms_all_def norms_def norms_neg_def)
            moreover have "(f' x)\<noteq>0"
              by (smt (verit, ccfv_threshold) \<open>y \<in> norms_all \<and> x \<in> norms_all \<and> x \<noteq> 0\<close> bij_betw_inv_into_left f'_bij norm_oplus_f_def norms_all_def norms_def norms_neg_def real_add_minus_iff vector_space_of_norms vector_space_with_domain.add_zero vector_space_with_domain.zero_in_dom)
            ultimately show ?thesis
              using mult_right_cancel by blast
          qed
          
        qed
      qed
    qed
    ultimately show ?thesis
      by blast
  qed
qed
qed
qed
  ultimately show ?thesis
    by (simp add: one_dim_vector_space_with_domain.intro one_dim_vector_space_with_domain_axioms.intro)
qed

end
context normed_gyrolinear_space 
begin
lemma is_normed_gyrolinear_space':
  shows "normed_gyrolinear_space' dom gyrozero gyroplus gyroinv gyr scale norm' 
(\<lambda>x. (if x \<in> (norm'`dom) then (f x) else
 (if x\<in> ( (\<lambda>x. - 1 * norm' x)`dom) then (-f (-x)) else undefined)))" 
proof
  show "\<forall>a\<in>dom. 0 \<le> norm' a"
    using norm_pos by blast
next
  show "bij_betw
     (\<lambda>x. if x \<in> norm' ` dom then f x
           else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x) else undefined)
     (norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom) UNIV"
  proof-
    have "inj_on  (\<lambda>x. if x \<in> norm' ` dom then f x
           else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x) else undefined)
     (norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom)"
    proof
      show " \<And>x y. x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
           y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
           (if x \<in> norm' ` dom then f x
            else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x)
                 else undefined) =
           (if y \<in> norm' ` dom then f y
            else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- y)
                 else undefined) \<Longrightarrow>
           x = y"
      proof-
        fix x y
        assume " x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom "
        show " y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
           (if x \<in> norm' ` dom then f x
            else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x)
                 else undefined) =
           (if y \<in> norm' ` dom then f y
            else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- y)
                 else undefined) \<Longrightarrow>
           x = y"
        proof-
          assume " y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom"
          show "(if x \<in> norm' ` dom then f x
            else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x)
                 else undefined) =
           (if y \<in> norm' ` dom then f y
            else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- y)
                 else undefined) \<Longrightarrow>
           x = y"
          proof-
            assume "(if x \<in> norm' ` dom then f x
            else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x)
                 else undefined) =
           (if y \<in> norm' ` dom then f y
            else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- y)
                 else undefined)"
            show "x=y"
            proof-
              have "x\<in> norm' ` dom \<or>  x \<in> (\<lambda>x. - 1 * norm' x) ` dom "
                using \<open>x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom\<close> by fastforce
              moreover {
                assume "x\<in> norm' ` dom"
                have "y\<in> norm' ` dom \<or>  y \<in> (\<lambda>x. - 1 * norm' x) ` dom "
                  using \<open>y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom\<close> by blast
                moreover {
                  assume "y \<in> norm' ` dom "
                  then have ?thesis 
                    by (metis \<open>(if x \<in> norm' ` dom then f x else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x) else undefined) = (if y \<in> norm' ` dom then f y else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- y) else undefined)\<close> \<open>x \<in> norm' ` dom\<close> bij_betw_inv_into_left f_bij)
                }
                moreover {
                  assume " y \<in> (\<lambda>x. - 1 * norm' x) ` dom"
                  moreover have "(if x \<in> norm' ` dom then f x
            else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x)
                 else undefined) = f x"
                    using \<open>x \<in> norm' ` dom\<close> by presburger
                  moreover have "y\<in> norm' ` dom\<or> \<not>y \<in>norm' ` dom"
                    by blast
                  moreover {
                    assume "y\<in>norm'`dom"
                    then have ?thesis 
                      using \<open>y \<in> norm' ` dom \<Longrightarrow> x = y\<close> by fastforce
                  }
                  moreover {
                    assume "\<not>y \<in>norm' ` dom"
                 
                    then have "f x =  - f (- y)"
                    using \<open>(if x \<in> norm' ` dom then f x else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x) else undefined) = (if y \<in> norm' ` dom then f y else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- y) else undefined)\<close> calculation(1) calculation(2) by presburger   
                  moreover have "f x = 0"
                    by (smt (verit) \<open>x \<in> norm' ` dom\<close> \<open>y \<in> (\<lambda>x. - 1 * norm' x) ` dom\<close> calculation f_pos image_iff)
                  moreover have "f (-y) = 0"
                    using calculation(1) calculation(2) by auto
                  moreover have "x=0"
                    using \<open>x \<in> norm' ` dom\<close> calculation(2) gyro_left_id image_subset_iff mult_cancel_right1 normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def norms_all_def norms_def order_dom2 scale_1 scale_distrib sup.cobounded1 zero_in_dom
                    by (smt (verit, del_insts))
                  moreover have "y=0"
                    by (smt (verit) \<open>x \<in> norm' ` dom\<close> \<open>y \<in> (\<lambda>x. - 1 * norm' x) ` dom\<close> bij_betw_iff_bijections calculation(2) calculation(3) calculation(4) f_bij image_iff)
                    ultimately have ?thesis 
                      by meson
                  }
                ultimately have ?thesis
                  by linarith
              }
            ultimately have ?thesis 
              by fastforce
            }
             moreover {
                assume "x\<in> (\<lambda>x. - 1 * norm' x)`dom"
                have "y\<in> norm' ` dom \<or>  y \<in> (\<lambda>x. - 1 * norm' x) ` dom "
                  using \<open>y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom\<close> by blast
                moreover {
                  assume "y \<in> norm' ` dom "
                  then have "-f (-x) = f y"
                    using \<open>(if x \<in> norm' ` dom then f x else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x) else undefined) = (if y \<in> norm' ` dom then f y else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- y) else undefined)\<close> \<open>x \<in> (\<lambda>x. - 1 * norm' x) ` dom\<close> gyro_left_id mult_cancel_right1 normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def norms_def norms_neg_def scale_1 scale_distrib zero_in_dom zero_only_norms_norms_neg
                    by (smt (verit, del_insts))
                  then have "x=0"
                    by (smt (verit, ccfv_SIG) \<open>x \<in> (\<lambda>x. - 1 * norm' x) ` dom\<close> \<open>y \<in> norm' ` dom\<close> image_iff normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def normed_gyrolinear_space_def zero_in_dom)
                  then have "y=0"
                    using \<open>x \<in> norm' ` dom \<Longrightarrow> x = y\<close> \<open>x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom\<close> norms_all_def norms_def norms_neg_def order_dom2 by blast
                  then have ?thesis
                    using  \<open>(if x \<in> norm' ` dom then f x else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x) else undefined) = (if y \<in> norm' ` dom then f y else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- y) else undefined)\<close> \<open>x \<in> norm' ` dom \<or> x \<in> (\<lambda>x. - 1 * norm' x) ` dom\<close> image_iff normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def zero_in_dom
                    using \<open>x = 0\<close> by force
                  }
                moreover {
                  assume " y \<in> (\<lambda>x. - 1 * norm' x) ` dom"
                  then have ?thesis  
                  by (smt (verit, ccfv_SIG) \<open>(if x \<in> norm' ` dom then f x else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x) else undefined) = (if y \<in> norm' ` dom then f y else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- y) else undefined)\<close> \<open>x \<in> (\<lambda>x. - 1 * norm' x) ` dom\<close> \<open>x \<in> norm' ` dom \<Longrightarrow> x = y\<close> calculation(2) f_mon image_iff)
                 
              }
              ultimately have ?thesis 
                by fastforce
            }
            ultimately show ?thesis by blast
            qed
          qed
        qed
      qed
    qed
    moreover have "(\<lambda>x. if x \<in> norm' ` dom then f x
            else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x) else undefined) `
(norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom) = UNIV "
    proof-
      have "f ` (norm'` dom) = {x::real. x\<ge>0}"
        by (meson bij_betw_imp_surj_on f_bij)
      moreover have "(\<lambda>x. - f (- x)) `  (\<lambda>x. - 1 * norm' x) ` dom = {x::real. x\<le>0}"
      proof
        show "(\<lambda>x. - f (- x)) ` (\<lambda>x. - 1 * norm' x) ` dom \<subseteq> {x. x \<le> 0}"
          using f_pos by fastforce
      next
        show "{x::real. x \<le> 0} \<subseteq> (\<lambda>x. - f (- x)) ` (\<lambda>x. - 1 * norm' x) ` dom"
        proof
          show "\<And>x. x \<in> {x::real. x \<le> 0} \<Longrightarrow> x \<in> (\<lambda>x. - f (- x)) ` (\<lambda>x. - 1 * norm' x) ` dom "
          proof-
            fix x
            assume "x \<in> {x::real. x \<le> 0}"
            show " x \<in> (\<lambda>x. - f (- x)) ` (\<lambda>x. - 1 * norm' x) ` dom"
            proof-
              have "-x\<in>{x::real. x\<ge>0}"
                using \<open>x \<in> {x. x \<le> 0}\<close> by force
              moreover obtain "t" where "t=-x \<and> t \<in> f`norm'`dom"
                using \<open>f ` norm' ` dom = {x. 0 \<le> x}\<close> calculation by presburger
              ultimately show ?thesis 
                using image_iff by fastforce 
            qed
          qed
        qed
      qed
      moreover have "(\<lambda>x. if x \<in> norm' ` dom then f x
            else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x) else undefined) `
(norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom) = f ` (norm'` dom) \<union> ((\<lambda>x. - f (- x)) `  (\<lambda>x. - 1 * norm' x) ` dom)"
      proof
        show " (\<lambda>x. if x \<in> norm' ` dom then f x
          else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x) else undefined) `
    (norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom)
    \<subseteq> f ` norm' ` dom \<union> (\<lambda>x. - f (- x)) ` (\<lambda>x. - 1 * norm' x) ` dom"
          using calculation(1) calculation(2) by force
      next
        show "f ` norm' ` dom \<union> (\<lambda>x. - f (- x)) ` (\<lambda>x. - 1 * norm' x) ` dom
    \<subseteq> (\<lambda>x. if x \<in> norm' ` dom then f x
            else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x)
                 else undefined) `
       (norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom)"
        proof
          show "\<And>x. x \<in> f ` norm' ` dom \<union> (\<lambda>x. - f (- x)) ` (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
         x \<in> (\<lambda>x. if x \<in> norm' ` dom then f x
                   else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x)
                        else undefined) `
              (norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom)"
          proof-
            fix x 
            assume " x \<in> f ` norm' ` dom \<union> (\<lambda>x. - f (- x)) ` (\<lambda>x. - 1 * norm' x) ` dom"
            show " x \<in> (\<lambda>x. if x \<in> norm' ` dom then f x
                   else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x)
                        else undefined) `
              (norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom)"
            proof-
              have " x \<in> f ` norm' ` dom \<or> x\<in> (\<lambda>x. - f (- x)) ` (\<lambda>x. - 1 * norm' x) ` dom"
                using \<open>x \<in> f ` norm' ` dom \<union> (\<lambda>x. - f (- x)) ` (\<lambda>x. - 1 * norm' x) ` dom\<close> by blast
              moreover {
                assume "x \<in> f ` norm' ` dom"
                then have ?thesis 
                  by force
              } moreover {
                assume " x\<in> (\<lambda>x. - f (- x)) ` (\<lambda>x. - 1 * norm' x) ` dom"
 then obtain "t" where "t\<in>(\<lambda>x. - 1 * norm' x) ` dom 
\<and> x = - f (- t)"
   by blast
  moreover have "t\<in>norm' ` dom \<or> \<not>t\<in>norm'`dom"
    by blast
  moreover {
    assume "t\<in>norm'`dom"
    then have ?thesis
      by (smt (z3) \<open>(\<lambda>x. - f (- x)) ` (\<lambda>x. - 1 * norm' x) ` dom = {x. x \<le> 0}\<close> \<open>x \<in> f ` norm' ` dom \<Longrightarrow> x \<in> (\<lambda>x. if x \<in> norm' ` dom then f x else if x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- x) else undefined) ` (norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom)\<close> calculation(1) f_mon f_pos image_iff mem_Collect_eq norm_pos)
  }
  moreover {
    assume "\<not>t\<in>norm'`dom"
    then have ?thesis 
      using calculation(1) by auto
  }
  ultimately have ?thesis 
    by argo
}
  ultimately show ?thesis 
    by argo
qed
qed
qed
qed

      moreover have "{x::real. x\<ge>0} \<union> {x::real. x\<le>0} = UNIV"
        by fastforce
      ultimately show ?thesis 
        by argo
    qed
    ultimately show ?thesis 
      by (simp add: bij_betw_def)
qed
next
  show " \<forall>y z. y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and>
          z \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> z < y \<longrightarrow>
          (if z \<in> norm' ` dom then f z
           else if z \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (-z) else undefined)
          < (if y \<in> norm' ` dom then f y
             else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (-y) else undefined)"
  proof
    fix y
    show " \<forall>z. y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and>
             z \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> z < y \<longrightarrow>
             (if z \<in> norm' ` dom then f z
              else if z \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (-z) else undefined)
             < (if y \<in> norm' ` dom then f y
                else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (-y) else undefined)"
    proof
      fix z 
      show  "y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and>
             z \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> z < y \<longrightarrow>
             (if z \<in> norm' ` dom then f z
              else if z \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (-z) else undefined)
             < (if y \<in> norm' ` dom then f y
                else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (-y) else undefined)"
      proof
        assume *: "y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and>
             z \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> z < y"
        show "(if z \<in> norm' ` dom then f z
              else if z \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (-z) else undefined)
             < (if y \<in> norm' ` dom then f y
                else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (-y) else undefined)"
        proof-
          have "y \<in> norm' ` dom \<or> y\<in> (\<lambda>x. - 1 * norm' x) ` dom"
            using "*" by force
          moreover {
            assume "y\<in> norm'`dom"
            have "z \<in> norm' ` dom \<or> z\<in> (\<lambda>x. - 1 * norm' x) ` dom"
              using "*" by blast
            moreover {
              assume "z\<in>norm'`dom"
              then have ?thesis
                using "*" \<open>y \<in> norm' ` dom\<close> f_mon by presburger
            }
            moreover {
              assume "z\<in> (\<lambda>x. - 1 * norm' x) ` dom"
              obtain "t" where "t \<in> dom \<and> z = -  norm' t"
                using \<open>z \<in> (\<lambda>x. - 1 * norm' x) ` dom\<close> by force
              moreover  have "-f (-z) \<le> 0"
                using f_pos 
                by (simp add: calculation)
              moreover have "y > z"
                using "*" by force
              moreover have "f y \<ge>0"
                by (simp add: \<open>y \<in> norm' ` dom\<close> f_pos)
              moreover have "f y \<noteq> -f (-z)"
              proof(rule ccontr)
                assume "\<not>(f y \<noteq> -f (-z))"
                have "f y = - f (-z)"
                  using \<open>\<not> f y \<noteq> - f (- z)\<close> by fastforce
                moreover have "f y = 0"
                  using \<open>- f (- z) \<le> 0\<close> \<open>0 \<le> f y\<close> calculation by force
                moreover have "y=0"
                  by (smt (verit, best) \<open>y \<in> norm' ` dom\<close> calculation(2) image_iff normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def zero_in_dom)
                ultimately show False 
                  by (smt (verit, best) \<open>t \<in> dom \<and> z = - norm' t\<close> \<open>y \<in> norm' ` dom\<close> \<open>z < y\<close> f_mon imageI)
              qed
              moreover have "f y > - f (-z)"
                using calculation(4) calculation(5) 
                using calculation(2) by fastforce
              ultimately have ?thesis 
                using \<open>y \<in> norm' ` dom\<close> \<open>z \<in> (\<lambda>x. - 1 * norm' x) ` dom\<close> \<open>z \<in> norm' ` dom \<Longrightarrow> (if z \<in> norm' ` dom then f z else if z \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- z) else undefined) < (if y \<in> norm' ` dom then f y else if y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- y) else undefined)\<close> by presburger
            }
            ultimately have ?thesis 
              by fastforce
          }
          moreover {
            assume " y\<in> (\<lambda>x. - 1 * norm' x) ` dom"
            then have ?thesis 
              by (smt (z3) "*" calculation(2) f_mon image_iff norm_pos norms_all_def norms_def norms_neg_def order_dom1_strict)
          }
          ultimately show ?thesis
            by fastforce
        qed
      qed
   qed
 qed
next
  show "(if 0 \<in> norm' ` dom then f 0
     else if 0 \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- 0) else undefined) =
    0"
    using Un_def gyro_left_id image_subset_iff inf_sup_ord(3) mem_Collect_eq mult_cancel_right1 normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def norms_def norms_neg_def scale_1 scale_distrib sup_commute zero_in_dom
    by (smt (verit, del_insts) image_eqI)
next
  show "\<forall>x\<in>dom.
       \<forall>y\<in>dom.
          (if norm' (x \<oplus> y) \<in> norm' ` dom then f (norm' (x \<oplus> y))
           else if norm' (x \<oplus> y) \<in> (\<lambda>x. - 1 * norm' x) ` dom
                then - f (- norm' (x \<oplus> y)) else undefined)
          \<le> (if norm' x \<in> norm' ` dom then f (norm' x)
              else if norm' x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- norm' x)
                   else undefined) +
             (if norm' y \<in> norm' ` dom then f (norm' y)
              else if norm' y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- norm' y)
                   else undefined)"
  proof
    fix x 
    assume "x\<in>dom"
    show "\<forall>y\<in>dom.
          (if norm' (x \<oplus> y) \<in> norm' ` dom then f (norm' (x \<oplus> y))
           else if norm' (x \<oplus> y) \<in> (\<lambda>x. - 1 * norm' x) ` dom
                then - f (- norm' (x \<oplus> y)) else undefined)
          \<le> (if norm' x \<in> norm' ` dom then f (norm' x)
              else if norm' x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- norm' x)
                   else undefined) +
             (if norm' y \<in> norm' ` dom then f (norm' y)
              else if norm' y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- norm' y)
                   else undefined)"
    proof
      fix y
      assume "y\<in>dom"
      show "(if norm' (x \<oplus> y) \<in> norm' ` dom then f (norm' (x \<oplus> y))
           else if norm' (x \<oplus> y) \<in> (\<lambda>x. - 1 * norm' x) ` dom
                then - f (- norm' (x \<oplus> y)) else undefined)
          \<le> (if norm' x \<in> norm' ` dom then f (norm' x)
              else if norm' x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- norm' x)
                   else undefined) +
             (if norm' y \<in> norm' ` dom then f (norm' y)
              else if norm' y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- norm' y)
                   else undefined)"
      proof-
        have "(if norm' (x \<oplus> y) \<in> norm' ` dom then f (norm' (x \<oplus> y))
           else if norm' (x \<oplus> y) \<in> (\<lambda>x. - 1 * norm' x) ` dom
                then - f (- norm' (x \<oplus> y)) else undefined) =  f (norm' (x \<oplus> y))"
          by (simp add: \<open>x \<in> dom\<close> \<open>y \<in> dom\<close> gyroplus_closed)
        moreover have "(if norm' x \<in> norm' ` dom then f (norm' x)
              else if norm' x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- norm' x)
                   else undefined) = f (norm' x)"
          using \<open>x \<in> dom\<close> by auto
        moreover have "(if norm' y \<in> norm' ` dom then f (norm' y)
              else if norm' y \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- norm' y)
                   else undefined) = f (norm' y)"
          by (simp add: \<open>y \<in> dom\<close>)
        moreover have " f (norm' (x \<oplus> y)) \<le> f (norm' x) + f (norm' y)"
        proof -
          have "\<exists>fa a fb. normed_gyrolinear_space_axioms dom a (\<oplus>) fb fa norm' f"
            by (smt (z3) normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms)
          then show ?thesis
            by (smt (z3) \<open>x \<in> dom\<close> \<open>y \<in> dom\<close> normed_gyrolinear_space_axioms_def)
        qed
        ultimately show ?thesis 
          by presburger
      qed
    qed
  qed
next
  show "\<forall>r. \<forall>x\<in>dom.
           (if norm' (r \<otimes> x) \<in> norm' ` dom then f (norm' (r \<otimes> x))
            else if norm' (r \<otimes> x) \<in> (\<lambda>x. - 1 * norm' x) ` dom
                 then - f (- norm' (r \<otimes> x)) else undefined) =
           \<bar>r\<bar> *
           (if norm' x \<in> norm' ` dom then f (norm' x)
            else if norm' x \<in> (\<lambda>x. - 1 * norm' x) ` dom then - f (- norm' x)
                 else undefined)"
    using image_eqI normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def scale_closed
    by (smt (verit, ccfv_threshold))
next
  show " \<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>x\<in>dom. norm' (gyr u v x) = norm' x"
  proof -
    have "\<exists>f fa a fb. normed_gyrolinear_space_axioms dom a fb gyr f norm' fa"
      by (smt (z3) normed_gyrolinear_space_axioms normed_gyrolinear_space_def)
    then show ?thesis
      by (smt (z3) normed_gyrolinear_space_axioms_def)
  qed
next
  show "\<forall>x\<in>dom. (norm' x = 0) = (x = 0\<^sub>g)"
  proof
    fix x
    assume "x\<in>dom"
    show " (norm' x = 0) = (x = 0\<^sub>g)"
    proof -
      have "normed_gyrolinear_space_axioms dom 0\<^sub>g (\<oplus>) gyr (\<otimes>) norm' f"
        by (smt (z3) normed_gyrolinear_space_axioms normed_gyrolinear_space_def)
      then show ?thesis
        by (simp add: \<open>x \<in> dom\<close> normed_gyrolinear_space_axioms_def)
    qed
  qed
qed

end

locale normed_gyrolinear_space'' = 
   gyrolinear_space + 
  fixes norm'::"'a \<Rightarrow> real"
  fixes oplus'::"real \<Rightarrow> real \<Rightarrow> real"
  fixes otimes'::"real\<Rightarrow>real \<Rightarrow> real"
 (* fixes otimes'_zero::"real"*)
  assumes norm_pos:"\<forall>a\<in>dom. (norm' a \<ge> 0)"
  assumes ax_space: "one_dim_vector_space_with_domain ((norm' ` dom) \<union> ((\<lambda>x. -1 * norm' x) ` dom))
      oplus' 0 otimes'"
  assumes norm_ineq: "\<forall>x::'a\<in>dom. \<forall>y::'a\<in>dom. (norm' (gyroplus x y)) \<le> oplus' (norm' x) (norm' y)"
  assumes norm_scale:"\<forall>r::real. \<forall>x\<in>dom. (norm' (scale r x)) = otimes' \<bar>r\<bar> (norm' x)"
  assumes norm_gyr:"\<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>x\<in>dom. norm' (gyr u v x) = norm' x"
  assumes norm_zero: "\<forall>x::'a\<in>dom. ((norm' x) = 0 \<longleftrightarrow> x = gyrozero)"
begin

definition norms::"real set" where 
  "norms = norm' ` dom"

definition norms_neg::"real set" where 
  "norms_neg = (\<lambda>x. -1 * norm' x) ` dom"

definition norms_all::"real set" where 
  "norms_all = norms \<union> norms_neg"

lemma norms_neq_not_empty:
  shows "norms_neg \<noteq> {}"
proof-
  have " \<exists>x.(x\<in>dom \<and> x\<noteq>gyrozero)"
    using non_trivial_dom by force
  then show ?thesis 
    using norms_neg_def by force
qed

  


lemma zero_only_norms_norms_neg:
  assumes "x\<in>norms" "x\<in>norms_neg"
  shows "x=0"
proof-
  have "x\<ge>0"
    using norms_def norm_pos
    using assms(1) by auto
  moreover have "x\<le>0"
     using norms_neg_def norm_pos
     using assms(2) by auto
   ultimately show ?thesis 
     by argo
 qed

lemma order_dom1:
  assumes "x=0" "y\<in>norms_all"
   "x\<ge>y"
 shows "y\<in> norms_neg"
  by (smt (verit, ccfv_threshold) UnE assms(1) assms(2) assms(3) image_iff norm_pos norms_all_def norms_def norms_neg_def)


lemma order_dom1_strict:
  assumes "x=0" "y\<in>norms_all"
   "x>y"
 shows "y\<in> norms_neg"
  by (smt (verit, ccfv_threshold) UnE assms(1) assms(2) assms(3) image_iff norm_pos norms_all_def norms_def norms_neg_def)

lemma order_dom2:
  assumes "x=0" "y\<in>norms_all"
   "y\<ge>0"
 shows "y\<in> norms"
  by (smt (verit, ccfv_threshold) UnE assms(2) assms(3) image_iff norm_pos norms_all_def norms_def norms_neg_def)

lemma not_trivial_domen_has_pos:
  assumes "\<exists>x. (x\<in>norms_all \<and> x\<noteq>0)"
  shows "\<exists>x. (x\<in>norms \<and> x\<noteq>0)"
  using assms norms_all_def norms_def norms_neg_def by auto

lemma not_trivial_123:
  assumes "\<exists>x\<in>dom. x\<noteq>gyrozero"
  shows " \<exists>x. x \<in> norms_all \<and> x \<noteq> 0"
  using local.norm_zero non_trivial_dom norms_all_def norms_def by auto

lemma iso_with_real:
  assumes "\<exists>x. (x\<in>norms_all \<and> x\<noteq>0)" (* not trivial domain *)
  shows "\<exists>g. (bij_betw g norms_all UNIV \<and> (g 0) = 0 \<and>
  (\<forall>u.\<forall>v. (u\<in>norms_all \<and> v\<in>norms_all \<longrightarrow> g (oplus' u v) = (g u) + (g v)))
 \<and> (\<forall>u.\<forall>r::real. (u\<in>norms_all \<longrightarrow> g (otimes' r u) = r*(g u)))
)" (*\<and> (\<forall>u. (u\<in>norms \<longrightarrow> (g u)\<ge>0))*)
proof-
  obtain "x" where "x\<in>norms \<and> x\<noteq>0"
    using assms not_trivial_domen_has_pos by presburger
  moreover have "x\<in> norms_all"
    by (simp add: calculation norms_all_def)
  have "\<forall>y. (y\<in>norms_all \<longrightarrow> (\<exists>!r.(y = otimes' r x)))"
    using ax_space  one_dim_vector_space_with_domain_axioms_def
    using \<open>x \<in> norms_all\<close> calculation norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(2)
    by (smt (verit, best) Un_upper1 gyro_left_inv image_subset_iff local.norm_zero
        norm_scale scale_1 scale_distrib scale_minus1_inv zero_in_dom)
  
  let ?g = "\<lambda>y. (THE r. y = otimes' r x)"
  have "bij_betw ?g norms_all UNIV"
  proof-
    have "inj_on ?g norms_all"
      by (smt (verit, best) \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> inj_on_def the_equality)
    moreover have "\<forall>r::real. \<exists>y. (y\<in> norms_all \<and> y = otimes' r x)"
      by (metis \<open>x \<in> norms_all\<close> ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed)
    moreover have "\<forall>r::real.\<exists>y\<in>norms_all. ?g y = r"
      using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> calculation(2) by blast
    ultimately show ?thesis 
      by (smt (verit, ccfv_threshold) UNIV_eq_I bij_betw_apply inj_on_imp_bij_betw)
  qed
  moreover have "?g 0 = 0"
  proof-
    obtain "r" where "0 = otimes' r x"
     
      by (metis Un_upper1 \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> image_subset_iff
          local.norm_zero norms_all_def norms_def zero_in_dom)
      
    moreover obtain "xx" where "xx \<in> dom \<and> x=norm' xx "
      using norms_all_def 
      using norms_def norms_neg_def
      using \<open>x \<in> norms \<and> x \<noteq> 0\<close> by auto

(*(norm' (scale r x)) = otimes' \<bar>r\<bar> (norm' x)*)
    moreover  have "otimes' 0 (norm' xx) = norm' (0 \<otimes> xx)"
      using norm_zero
      by (simp add: calculation(2) norm_scale)
     
    moreover have "otimes' 0 x = 0"
      
      by (smt (verit, del_insts) calculation(2,3) gyro_left_inv local.norm_zero scale_1
          scale_distrib scale_minus1_inv zero_in_dom)
   
    ultimately show ?thesis 

      by (smt (verit, del_insts) Un_iff \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close>
          imageI local.norm_zero norms_all_def norms_def the_equality zero_in_dom)
    
  qed
  moreover have "\<forall>u.\<forall>v. (u\<in>norms_all \<and> v\<in>norms_all \<longrightarrow> ?g (oplus' u v) = (?g u) + (?g v))"
  proof
    fix u
    show "\<forall>v. (u\<in>norms_all \<and> v\<in>norms_all \<longrightarrow> ?g (oplus' u v) = (?g u) + (?g v))"
    proof
      fix v
      show "u\<in>norms_all \<and> v\<in>norms_all \<longrightarrow> ?g (oplus' u v) = (?g u) + (?g v)"
      proof
        assume "u\<in>norms_all \<and> v\<in>norms_all"
        show " ?g (oplus' u v) = (?g u) + (?g v)"
        proof-
          obtain "a" where "u = otimes' a x"
            using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> \<open>u \<in> norms_all \<and> v \<in> norms_all\<close> by blast
          moreover obtain "b" where "v = otimes' b x"
            using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> \<open>u \<in> norms_all \<and> v \<in> norms_all\<close> by blast
          moreover have *:"oplus' u v = otimes' (a+b) x"
            by (metis \<open>x \<in> norms_all\<close> ax_space calculation(1) calculation(2) norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain_def vector_space_with_domain.smult_distr_sadd)
          moreover have "oplus' u v \<in> norms_all"
            by (metis "*" \<open>x \<in> norms_all\<close> ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed)
          moreover have "?g (oplus' u v) = (a+b)"
            using * 
            using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> calculation(4) by auto
          ultimately show ?thesis 
            by (smt (verit, del_insts) \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> \<open>u \<in> norms_all \<and> v \<in> norms_all\<close> the1_equality)
        qed
      qed
    qed
  qed
  moreover have "(\<forall>u.\<forall>r::real. (u\<in>norms_all \<longrightarrow> ?g (otimes' r u) = r*(?g u)))"
  proof
    fix u
    show "\<forall>r::real. (u\<in>norms_all \<longrightarrow> ?g (otimes' r u) = r*(?g u))"
    proof
      fix r
      show "u\<in>norms_all \<longrightarrow> ?g (otimes' r u) = r*(?g u)"
      proof
        assume "u\<in>norms_all"
        show "?g (otimes' r u) = r*(?g u)"
        proof-
          obtain "a" where "u = otimes' a x"
            using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> \<open>u \<in> norms_all\<close> by blast
          moreover have "otimes' r u = otimes' (r*a) x"
            by (metis \<open>x \<in> norms_all\<close> ax_space calculation norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_assoc)
          moreover have "otimes' r u \<in> norms_all"
            by (metis \<open>u \<in> norms_all\<close> ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed)
          moreover have "?g (otimes' r u) = (r*a)"
            using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> calculation(2) calculation(3) by auto
          ultimately show ?thesis 
            by (smt (verit, ccfv_threshold) \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> \<open>u \<in> norms_all\<close> theI')
        qed
      qed
    qed
  qed
 
  ultimately show ?thesis 
    by blast
qed


definition g_iso::"(real\<Rightarrow>real)\<Rightarrow>bool" where
  "g_iso g \<longleftrightarrow> (bij_betw g norms_all UNIV \<and> (g 0) = 0 \<and>
  (\<forall>u.\<forall>v. (u\<in>norms_all \<and> v\<in>norms_all \<longrightarrow> g (oplus' u v) = (g u) + (g v)))
 \<and> (\<forall>u.\<forall>r::real. (u\<in>norms_all \<longrightarrow> g (otimes' r u) = r*(g u))))"

lemma iso_neg_with_real:
  assumes "\<exists>x. (x\<in>norms_all \<and> x\<noteq>0)" (* not trivial domain *)
  shows "g_iso g \<longrightarrow> g_iso (\<lambda>x. -1 * (g x))" 
proof
  assume "g_iso g"
  show " g_iso (\<lambda>x. -1 * (g x))"
  proof-
    have "bij_betw (\<lambda>x. -1 * (g x)) norms_all UNIV"
    proof-
      have "inj_on (\<lambda>x. -1 * (g x)) norms_all"
        by (smt (verit, ccfv_threshold) \<open>g_iso g\<close> bij_betw_imp_inj_on g_iso_def inj_on_def)
      moreover have "\<forall>r::real.\<exists>y\<in>norms_all. ((\<lambda>x. -1 * (g x)) y = r)"
        by (metis UNIV_I \<open>g_iso g\<close> bij_betw_iff_bijections g_iso_def minus_equation_iff mult_cancel_right2 mult_minus_left)
      ultimately show ?thesis 
        by (metis (mono_tags, lifting) UNIV_eq_I bij_betwE bij_betw_imageI)
    qed
    moreover have " (\<lambda>x. -1 * (g x)) 0 = 0"
      using \<open>g_iso g\<close> g_iso_def by force
    moreover have "(\<forall>u.\<forall>v. (u\<in>norms_all \<and> v\<in>norms_all \<longrightarrow>  (\<lambda>x. -1 * (g x)) (oplus' u v)
 = ( (\<lambda>x. -1 * (g x)) u) + ( (\<lambda>x. -1 * (g x)) v)))"
      using \<open>g_iso g\<close> g_iso_def by auto
    moreover have "(\<forall>u.\<forall>r::real. (u\<in>norms_all \<longrightarrow>  (\<lambda>x. -1 * (g x)) (otimes' r u) = r*( (\<lambda>x. -1 * (g x)) u)))"
      using \<open>g_iso g\<close> g_iso_def by auto
    ultimately show ?thesis 
      using g_iso_def by presburger
  qed
qed

lemma iso_with_real_positive_on_norms:
  assumes "\<exists>x. (x\<in>norms_all \<and> x\<noteq>0)" (* not trivial domain *)
  shows "\<exists>g. (g_iso g \<and> (\<forall>x.(x\<in>norms \<longrightarrow> (g x)\<ge>0))
\<and> bij_betw (\<lambda>x. if x \<in> norms then (g x) else undefined) norms {r::real. r\<ge>0})"
proof-
  obtain "xx" where "xx\<in>norms \<and> xx\<noteq>0"
    using assms not_trivial_domen_has_pos by blast
  moreover obtain "x" where "norm' x = xx \<and> x\<in>dom"
    using calculation norms_def by auto
  moreover obtain "g" where "g_iso g"
    using iso_with_real
    using assms g_iso_def by blast
  let ?g = "if (g xx) < 0 then  (\<lambda>x. -1 * (g x)) else g"
  have *:"?g xx \<ge> 0"
    by force
  moreover have "?g xx \<noteq>0"
  proof (rule ccontr)
    assume "\<not>(?g xx \<noteq>0)"
    have "?g xx = 0"
      using \<open>\<not> (if g xx < 0 then \<lambda>x. - 1 * g x else g) xx \<noteq> 0\<close> by blast
    then have "?g xx = g xx"
      by (smt (verit, ccfv_threshold))
    then have "g xx = 0"
      by (simp add: \<open>(if g xx < 0 then \<lambda>x. - 1 * g x else g) xx = 0\<close>)
    then have "xx=0"
     
      by (metis \<open>g_iso g\<close> bij_betw_iff_bijections calculation(2) g_iso_def image_subset_iff
          inf_sup_ord(3) local.norm_zero norms_all_def norms_def zero_in_dom)
     
    then show False 
      using calculation(1) by blast
  qed
  moreover have "g_iso ?g"
    using \<open>g_iso g\<close> assms iso_neg_with_real by presburger
  moreover have "\<forall>x.(x\<in>norms \<longrightarrow> (?g x)\<ge>0)"
  proof(rule ccontr)
    assume "\<not>(\<forall>x.(x\<in>norms \<longrightarrow> (?g x)\<ge>0))"
    have "\<exists>x. (x\<in>norms \<and> (?g x) < 0)"
      using \<open>\<not> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> (if g xx < 0 then \<lambda>x. - 1 * g x else g) x)\<close> by fastforce
    moreover obtain "yy" where "yy \<in> norms \<and> (?g yy) <0"
      using calculation by blast
    moreover obtain "y" where "norm' y = yy \<and> y\<in>dom"
      using calculation(2) norms_def by auto
    let ?A = "{norm' (r \<otimes> x) | r::real. True}"
    let ?B = "{norm' (r \<otimes> y) | r::real. True}"
    have "?A \<union> ?B \<subseteq> norms"
      using norms_def 
      using \<open>norm' x = xx \<and> x \<in> dom\<close> \<open>norm' y = yy \<and> y \<in> dom\<close> scale_closed by auto
    let ?gA = "{(?g a)|a. a\<in>?A}"
    have "?gA = {r::real. r\<ge>0}"
    proof-
      have "\<forall>a. (a\<in>?A \<longrightarrow> ?g a \<ge>0)"
      proof
        fix a
        show "(a\<in>?A \<longrightarrow> ?g a \<ge>0)"
        proof
            assume "a\<in>?A"
            show "?g a \<ge>0"
            proof-
              obtain "r" where "a = norm'  (r \<otimes> x) "
                using \<open>a \<in> {norm' (r \<otimes> x) |r. True}\<close> by blast
              moreover have "?g a = ?g (norm'  (r \<otimes> x) )"
                using calculation by presburger
              moreover have "?g a = ?g ( otimes' \<bar>r\<bar> (norm' x))"
                by (simp add: \<open>norm' x = xx \<and> x \<in> dom\<close> calculation(1) norm_scale) 
              moreover have "?g a =  \<bar>r\<bar> * ?g (norm' x)"
                by (metis Un_iff \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' x = xx \<and> x \<in> dom\<close> \<open>xx \<in> norms \<and> xx \<noteq> 0\<close> calculation(3) normed_gyrolinear_space''.g_iso_def normed_gyrolinear_space''_axioms norms_all_def)
              ultimately show ?thesis 
                by (simp add: \<open>norm' x = xx \<and> x \<in> dom\<close>)
          
            qed
        qed
      qed
      moreover have "?gA \<subseteq> {r::real. r\<ge>0}"
        using calculation by fastforce
      moreover have "{r::real. r\<ge>0} \<subseteq> ?gA"
      proof-
        have "bij_betw ?g norms_all UNIV"
          using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> g_iso_def by blast
        moreover have "\<forall>r::real. (r\<ge>0 \<longrightarrow> r\<in>?gA)"
        proof
          fix r
          show "r\<ge>0 \<longrightarrow> r\<in>?gA"
          proof
            assume "r\<ge>0"
            show "r\<in>?gA"
            proof-
              obtain "r'" where "\<bar>r'\<bar> = r / (?g xx)"
                using  *
                by (meson \<open>0 \<le> r\<close> abs_of_nonneg divide_nonneg_nonneg)
              moreover have "r =  \<bar>r'\<bar> * (?g xx)"
                by (simp add: \<open>(if g xx < 0 then \<lambda>x. - 1 * g x else g) xx \<noteq> 0\<close> calculation)
              moreover have "r =  \<bar>r'\<bar> * (?g (norm' x))"
                using \<open>norm' x = xx \<and> x\<in>dom\<close> calculation(2) by blast
              moreover have "r = ?g (otimes' \<bar>r'\<bar>  (norm' x))"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' x = xx\<and>x\<in>dom\<close> \<open>xx \<in> norms \<and> xx \<noteq> 0\<close> calculation(3) g_iso_def norms_all_def by auto
              moreover have "r = ?g (norm'  (\<bar>r'\<bar>  \<otimes> x))"
                by (simp add: \<open>norm' x = xx \<and> x \<in> dom\<close> calculation(4) norm_scale)

              ultimately show ?thesis 
                by blast
            qed
          qed
        qed
        ultimately show ?thesis 
          by blast
      qed
      
      ultimately show ?thesis 
        by fastforce
    qed
    let ?gB = "{(?g b)|b. b\<in>?B}"
    have "?gB = {r::real. r\<le>0}"


 proof-
      have "\<forall>a. (a\<in>?B \<longrightarrow> ?g a \<le>0)"
      proof
        fix a
        show "(a\<in>?B \<longrightarrow> ?g a \<le>0)"
        proof
            assume "a\<in>?B"
            show "?g a\<le>0"
            proof-
              obtain "r" where "a = norm'  (r \<otimes> y) "
                     using \<open>a \<in> {norm' (r \<otimes> y) |r. True}\<close> by blast
              moreover have "?g a = ?g (norm'  (r \<otimes> y) )"
                using calculation by presburger
              moreover have "?g a = ?g ( otimes' \<bar>r\<bar> (norm' y))"
                by (simp add: \<open>norm' y = yy \<and> y \<in> dom\<close> calculation(1) norm_scale)
               
              moreover have "?g a =  \<bar>r\<bar> * ?g (norm' y)"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' y = yy \<and> y\<in>dom\<close> \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> calculation(3) g_iso_def norms_all_def by auto
               
              ultimately show ?thesis 
                by (simp add: \<open>norm' y = yy \<and> y\<in>dom\<close> \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> mult_le_0_iff order_less_imp_le)
            qed
        qed
      qed
      moreover have "?gB \<subseteq> {r::real. r\<le>0}"
        using calculation by fastforce
      moreover have "{r::real. r\<le>0} \<subseteq> ?gB"
      proof-
        have "bij_betw ?g norms_all UNIV"
          using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> g_iso_def by blast
        moreover have "\<forall>r::real. (r\<le>0 \<longrightarrow> r\<in>?gB)"
        proof
          fix r
          show "r\<le>0 \<longrightarrow> r\<in>?gB"
          proof
            assume "r\<le>0"
            show "r\<in>?gB"
            proof-
              obtain "r'" where "\<bar>r'\<bar> = r / (?g yy)"
                using  *
                by (metis \<open>r \<le> 0\<close> \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> abs_if divide_less_0_iff less_eq_real_def not_less_iff_gr_or_eq)
              moreover have "r =  \<bar>r'\<bar> * (?g yy)"
                using \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> calculation by auto
              moreover have "r =  \<bar>r'\<bar> * (?g (norm' y))"
                using \<open>norm' y = yy \<and> y\<in>dom\<close> calculation(2) by blast
              moreover have "r = ?g (otimes' \<bar>r'\<bar>  (norm' y))"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' y = yy\<and>y\<in>dom\<close> \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> calculation(3) g_iso_def norms_all_def by auto
              moreover have "r = ?g (norm'  (\<bar>r'\<bar>  \<otimes> y))"
                by (simp add: \<open>norm' y = yy \<and> y \<in> dom\<close> calculation(4) norm_scale)
               
              ultimately show ?thesis 
                by blast
            qed
          qed
        qed
        ultimately show ?thesis 
          by blast
      qed
      
      ultimately show ?thesis 
        by fastforce
    qed

    let ?gX_norms = "{(?g x)|x. x\<in>norms}"
    let ?gX_norms_all = "{(?g x)|x. x\<in>norms_all}"
    let ?gA_union_B = "{(?g x)|x. x\<in> ?A\<union>?B}"
    have "?gA_union_B \<subseteq> ?gX_norms"
      using \<open>{norm' (r \<otimes> x) |r. True} \<union> {norm' (r \<otimes> y) |r. True} \<subseteq> norms\<close> by force
    moreover have "?gA_union_B = ?gA \<union> ?gB"
    proof-
      have "?gA_union_B \<subseteq> ?gA \<union> ?gB"
        by blast
      moreover have "?gA \<union> ?gB \<subseteq> ?gA_union_B"
        by blast
      ultimately show ?thesis
        by force
    qed
    moreover have "?gA_union_B = UNIV"
      using \<open>{(if g xx < 0 then \<lambda>x. - 1 * g x else g) a |a. a \<in> {norm' (r \<otimes> x) |r. True}} = {r. 0 \<le> r}\<close> \<open>{(if g xx < 0 then \<lambda>x. - 1 * g x else g) b |b. b \<in> {norm' (r \<otimes> y) |r. True}} = {r. r \<le> 0}\<close> calculation(4) by force
    moreover have "UNIV \<subseteq> ?gX_norms"
      using calculation(3) calculation(5) by argo
   
    obtain "a" where "a\<in>norms_all \<and> \<not>a\<in>norms"
      by (metis (mono_tags, lifting) Un_iff add.inverse_inverse add.inverse_neutral image_eqI local.norm_zero mult_minus1 non_trivial_dom norms_all_def norms_neg_def zero_only_norms_norms_neg)

        let ?a = "?g a"
        have "?a \<in> ?gX_norms_all "

          using \<open>a \<in> norms_all \<and> a \<notin> norms\<close> by blast

        moreover have "\<not>?a\<in> ?gX_norms"
        proof(rule ccontr)
          assume "\<not>(\<not>?a\<in> ?gX_norms)"
          have "?a\<in>?gX_norms"
            using \<open>\<not> (if g xx < 0 then \<lambda>x. - 1 * g x else g) a \<notin> {(if g xx < 0 then \<lambda>x. - 1 * g x else g) x |x. x \<in> norms}\<close> by blast
          then obtain "b" where "b\<in>norms \<and> ?g b = ?a"
            by force
         
            then show False using  \<open>a \<in> norms_all \<and> a \<notin> norms\<close> \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> bij_betw_inv_into_left g_iso_def inf_sup_ord(3) norms_all_def subsetD
              by (smt (verit, ccfv_threshold) \<open>g_iso g\<close>)
          qed
          moreover have "False" 

            using \<open>UNIV \<subseteq> {(if g xx < 0 then \<lambda>x. - 1 * g x else g) x |x. x \<in> norms}\<close> calculation(7) by blast
            
    ultimately show False 
      by auto
  qed
  

  moreover have " bij_betw (\<lambda>x. if x \<in> norms then (?g x) else undefined) norms {r::real. r\<ge>0}"
  proof-
    let ?f = "(\<lambda>x. if x \<in> norms then (?g x) else undefined)"
     let ?A = "{norm' (r \<otimes> x) | r::real. True}"
     let ?gA = "{(?g a)|a. a\<in>?A}"
     have s1:"?gA = {r::real. r\<ge>0}"
        proof-
      have "\<forall>a. (a\<in>?A \<longrightarrow> ?g a \<ge>0)"
      proof
        fix a
        show "(a\<in>?A \<longrightarrow> ?g a \<ge>0)"
        proof
            assume "a\<in>?A"
            show "?g a \<ge>0"
            proof-
              obtain "r" where "a = norm'  (r \<otimes> x) "
                using \<open>a \<in> {norm' (r \<otimes> x) |r. True}\<close> by blast
              moreover have "?g a = ?g (norm'  (r \<otimes> x) )"
                using calculation by presburger
              moreover have "?g a = ?g ( otimes' \<bar>r\<bar> (norm' x))"
                by (simp add: \<open>norm' x = xx \<and> x \<in> dom\<close> calculation(1) norm_scale)
              moreover have "?g a =  \<bar>r\<bar> * ?g (norm' x)"
                by (metis Un_iff \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' x = xx \<and> x \<in> dom\<close> \<open>xx \<in> norms \<and> xx \<noteq> 0\<close> calculation(3) normed_gyrolinear_space''.g_iso_def normed_gyrolinear_space''_axioms norms_all_def)
               
              ultimately show ?thesis 
                by (simp add: \<open>norm' x = xx \<and> x \<in> dom\<close>)
                
            qed
        qed
      qed
      moreover have "?gA \<subseteq> {r::real. r\<ge>0}"
        using calculation by fastforce
      moreover have "{r::real. r\<ge>0} \<subseteq> ?gA"
      proof-
        have "bij_betw ?g norms_all UNIV"
          using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> g_iso_def by blast
        moreover have "\<forall>r::real. (r\<ge>0 \<longrightarrow> r\<in>?gA)"
        proof
          fix r
          show "r\<ge>0 \<longrightarrow> r\<in>?gA"
          proof
            assume "r\<ge>0"
            show "r\<in>?gA"
            proof-
              obtain "r'" where "\<bar>r'\<bar> = r / (?g xx)"
                using  *
                by (meson \<open>0 \<le> r\<close> abs_of_nonneg divide_nonneg_nonneg)
              moreover have "r =  \<bar>r'\<bar> * (?g xx)"
                by (simp add: \<open>(if g xx < 0 then \<lambda>x. - 1 * g x else g) xx \<noteq> 0\<close> calculation)
              moreover have "r =  \<bar>r'\<bar> * (?g (norm' x))"
                using \<open>norm' x = xx\<and>x\<in>dom\<close> calculation(2) by blast
              moreover have "r = ?g (otimes' \<bar>r'\<bar>  (norm' x))"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' x = xx\<and>x\<in>dom\<close> \<open>xx \<in> norms \<and> xx \<noteq> 0\<close> calculation(3) g_iso_def norms_all_def by auto
              moreover have "r = ?g (norm'  (\<bar>r'\<bar>  \<otimes> x))"
                by (simp add: \<open>norm' x = xx \<and> x \<in> dom\<close> calculation(4) norm_scale)
                
              ultimately show ?thesis 
                by blast
            qed
          qed
        qed
        ultimately show ?thesis 
          by blast
      qed
      
      ultimately show ?thesis 
        by fastforce
    qed
     moreover have s2:"\<forall>y\<in>dom. (?g (norm' y) \<ge>0)"
       using \<open>\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> (if g xx < 0 then \<lambda>x. - 1 * g x else g) x\<close> norms_def
       by blast
     moreover have "norms = ?A"
     proof-
       have "\<forall>y\<in>dom. (?g (norm' y) \<in> ?gA)"
         using s1 s2 by blast
       moreover have "norms \<subseteq> ?A"
       proof-
         have "\<forall>y. (y\<in>norms \<longrightarrow> y\<in>?A)"
         proof
           fix y
           show "y\<in>norms \<longrightarrow> y\<in>?A"
           proof
             assume "y\<in>norms"
             show "y\<in>?A"
             proof-
               obtain "yy" where "y=norm' yy \<and> yy \<in>dom"
                 using \<open>y \<in> norms\<close> norms_def by auto
               moreover have "?g (norm' yy) \<in>?gA"
                 using calculation s1 s2 by auto
                 
               moreover have "norm' yy \<in> ?A"
               proof-
                 obtain "h" where "h \<in> ?A \<and> ?g h = ?g (norm' yy)"
                   using calculation(2) by fastforce
                 moreover have "?g h \<ge>0"
                   using calculation s2 
                   by (simp add: \<open>y = norm' yy \<and> yy \<in> dom\<close>)
                
                 moreover {
                   assume "?g = g"
                   have " g h = g (norm' yy)"
                     by (smt (verit, ccfv_SIG) calculation(1))
                   
                   moreover have "h=norm' yy"
                   proof-
                     have "h\<in>norms"
                       using \<open>h \<in> {norm' (r \<otimes> x) |r. True} \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) h = (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' yy)\<close> \<open>norm' x = xx \<and> x \<in> dom\<close> norms_def scale_closed by force
                      
                     moreover have "norm' yy \<in> norms"
                       using \<open>y = norm' yy\<and>yy\<in>dom\<close> \<open>y \<in> norms\<close> by blast
                     ultimately show ?thesis 
                       by (metis \<open>g h = g (norm' yy)\<close> \<open>g_iso g\<close> bij_betw_inv_into_left g_iso_def inf_sup_ord(3) norms_all_def subset_iff)
                   qed
                   ultimately have ?thesis
                     using \<open>h \<in> {norm' (r \<otimes> x) |r. True} \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) h = (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' yy)\<close> by blast
                 }
                   moreover {
                   assume "?g = (\<lambda>x. -1 * (g x))"
                   have " g h = g (norm' yy)"
                     by (smt (verit, ccfv_SIG) calculation(1))
                   
                   moreover have "h=norm' yy"
                   proof-
                     have "h\<in>norms"
                       using \<open>h \<in> {norm' (r \<otimes> x) |r. True} \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) h = (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' yy)\<close> \<open>norm' x = xx \<and> x \<in> dom\<close> norms_def scale_closed by auto
                       
                     moreover have "norm' yy \<in> norms"
                       using \<open>y = norm' yy\<and>yy\<in>dom\<close> \<open>y \<in> norms\<close> by blast
                     ultimately show ?thesis 
                       by (metis \<open>g h = g (norm' yy)\<close> \<open>g_iso g\<close> bij_betw_inv_into_left g_iso_def inf_sup_ord(3) norms_all_def subset_iff)
                   qed
                   ultimately have ?thesis
                     using \<open>h \<in> {norm' (r \<otimes> x) |r. True} \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) h = (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' yy)\<close> by blast
                 }
                 ultimately show ?thesis 
                   by argo
               qed
               ultimately show ?thesis 
                 by fastforce
             qed
         qed
       qed
        show ?thesis 
          using \<open>\<forall>y. y \<in> norms \<longrightarrow> y \<in> {norm' (r \<otimes> x) |r. True}\<close> by blast
      qed
      ultimately show ?thesis 
        using norms_def
        using \<open>norm' x = xx \<and> x \<in> dom\<close> scale_closed by auto
        
    qed
     moreover have step1:"inj_on ?f  norms"
     proof-
       have "\<forall>x.\<forall>y. (x\<in> norms \<and> y\<in> norms \<and> (?f x) = (?f y) \<longrightarrow> x=y)"
       proof
         fix x 
         show "\<forall>y. (x\<in> norms \<and> y\<in> norms \<and> (?f x) = (?f y) \<longrightarrow> x=y)"
         proof
           fix y 
           show " (x\<in> norms \<and> y\<in> norms \<and> (?f x) = (?f y) \<longrightarrow> x=y)"
             by (metis \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> bij_betw_imp_inj_on g_iso_def inf_sup_ord(3) inj_on_def norms_all_def subsetD)
         qed
       qed
       then show ?thesis
         using inj_on_def by blast
     qed
     moreover have "\<forall>r::real. (r\<ge>0 \<longrightarrow> (\<exists>x. (x\<in> norms \<and> ?f x = r)))"
       by (smt (verit) calculation(3) mem_Collect_eq s1)
       
     moreover have step2:"\<forall>r::real. (r\<ge>0 \<longrightarrow> (\<exists>x\<in> norms.( ?f x = r)))"
 
       using calculation(5) by blast
     moreover have "\<forall>r\<in>{x::real. x\<ge>0}. (\<exists>x\<in>norms. (?f x = r))"
       using step2
       by blast
     moreover have **:"?f=(\<lambda>x. if x \<in> norms then (?g x) else undefined)"
       by meson
     moreover have "?f ` norms = {r::real. r\<ge>0}"
       by (smt (verit) Collect_cong Setcompr_eq_image calculation(3) s1)
     ultimately show ?thesis 
       by (simp add: bij_betw_def)
    
   qed
 
  ultimately show ?thesis
    by blast
qed

lemma iso_with_real_positive_on_norms2:
  assumes "\<exists>x. (x\<in>norms_all \<and> x\<noteq>0)" (* not trivial domain *)
  shows "\<exists>g. (g_iso g \<and> (\<forall>x.(x\<in>norms \<longrightarrow> (g x)\<ge>0))
\<and> bij_betw (\<lambda>x. if x \<in> norms then (g x) else undefined) norms {r::real. r\<ge>0}
\<and> (\<forall>r. (\<forall>x\<in>dom. (otimes'  \<bar>r\<bar> (norm' x) = (inv_into norms_all g) (\<bar>r\<bar> * (g (norm' x)))))))"
proof-
  obtain "xx" where "xx\<in>norms \<and> xx\<noteq>0"
    using assms not_trivial_domen_has_pos by blast
  moreover obtain "x" where "norm' x = xx \<and> x\<in>dom"
    using calculation norms_def by auto
  moreover obtain "g" where "g_iso g"
    using iso_with_real
    using assms g_iso_def by blast
  let ?g = "if (g xx) < 0 then  (\<lambda>x. -1 * (g x)) else g"
  have *:"?g xx \<ge> 0"
    by force
  moreover have "?g xx \<noteq>0"
  proof (rule ccontr)
    assume "\<not>(?g xx \<noteq>0)"
    have "?g xx = 0"
      using \<open>\<not> (if g xx < 0 then \<lambda>x. - 1 * g x else g) xx \<noteq> 0\<close> by blast
    then have "?g xx = g xx"
      by (smt (verit, ccfv_threshold))
    then have "g xx = 0"
      by (simp add: \<open>(if g xx < 0 then \<lambda>x. - 1 * g x else g) xx = 0\<close>)
    then have "xx=0"
  
      by (metis \<open>g_iso g\<close> bij_betw_iff_bijections calculation(2) g_iso_def image_subset_iff
          inf_sup_ord(3) local.norm_zero norms_all_def norms_def zero_in_dom)
     
    then show False 
      using calculation(1) by blast
  qed
  moreover have "g_iso ?g"
    using \<open>g_iso g\<close> assms iso_neg_with_real by presburger
  moreover have "\<forall>x.(x\<in>norms \<longrightarrow> (?g x)\<ge>0)"
  proof(rule ccontr)
    assume "\<not>(\<forall>x.(x\<in>norms \<longrightarrow> (?g x)\<ge>0))"
    have "\<exists>x. (x\<in>norms \<and> (?g x) < 0)"
      using \<open>\<not> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> (if g xx < 0 then \<lambda>x. - 1 * g x else g) x)\<close> by fastforce
    moreover obtain "yy" where "yy \<in> norms \<and> (?g yy) <0"
      using calculation by blast
    moreover obtain "y" where "norm' y = yy \<and> y\<in>dom"
      using calculation(2) norms_def by auto
    let ?A = "{norm' (r \<otimes> x) | r::real. True}"
    let ?B = "{norm' (r \<otimes> y) | r::real. True}"
    have "?A \<union> ?B \<subseteq> norms"
      using norms_def 
      using \<open>norm' x = xx \<and> x \<in> dom\<close> \<open>norm' y = yy \<and> y \<in> dom\<close> scale_closed by auto
    let ?gA = "{(?g a)|a. a\<in>?A}"
    have "?gA = {r::real. r\<ge>0}"
    proof-
      have "\<forall>a. (a\<in>?A \<longrightarrow> ?g a \<ge>0)"
      proof
        fix a
        show "(a\<in>?A \<longrightarrow> ?g a \<ge>0)"
        proof
            assume "a\<in>?A"
            show "?g a \<ge>0"
            proof-
              obtain "r" where "a = norm'  (r \<otimes> x) "
                using \<open>a \<in> {norm' (r \<otimes> x) |r. True}\<close> by blast
              moreover have "?g a = ?g (norm'  (r \<otimes> x) )"
                using calculation by presburger
              moreover have "?g a = ?g ( otimes' \<bar>r\<bar> (norm' x))"
                by (simp add: \<open>norm' x = xx \<and> x \<in> dom\<close> calculation(1) norm_scale) 
              moreover have "?g a =  \<bar>r\<bar> * ?g (norm' x)"
                by (metis Un_iff \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' x = xx \<and> x \<in> dom\<close> \<open>xx \<in> norms \<and> xx \<noteq> 0\<close> calculation(3) normed_gyrolinear_space''.g_iso_def normed_gyrolinear_space''_axioms norms_all_def)
              ultimately show ?thesis 
                by (simp add: \<open>norm' x = xx \<and> x \<in> dom\<close>)
          
            qed
        qed
      qed
      moreover have "?gA \<subseteq> {r::real. r\<ge>0}"
        using calculation by fastforce
      moreover have "{r::real. r\<ge>0} \<subseteq> ?gA"
      proof-
        have "bij_betw ?g norms_all UNIV"
          using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> g_iso_def by blast
        moreover have "\<forall>r::real. (r\<ge>0 \<longrightarrow> r\<in>?gA)"
        proof
          fix r
          show "r\<ge>0 \<longrightarrow> r\<in>?gA"
          proof
            assume "r\<ge>0"
            show "r\<in>?gA"
            proof-
              obtain "r'" where "\<bar>r'\<bar> = r / (?g xx)"
                using  *
                by (meson \<open>0 \<le> r\<close> abs_of_nonneg divide_nonneg_nonneg)
              moreover have "r =  \<bar>r'\<bar> * (?g xx)"
                by (simp add: \<open>(if g xx < 0 then \<lambda>x. - 1 * g x else g) xx \<noteq> 0\<close> calculation)
              moreover have "r =  \<bar>r'\<bar> * (?g (norm' x))"
                using \<open>norm' x = xx \<and> x\<in>dom\<close> calculation(2) by blast
              moreover have "r = ?g (otimes' \<bar>r'\<bar>  (norm' x))"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' x = xx\<and>x\<in>dom\<close> \<open>xx \<in> norms \<and> xx \<noteq> 0\<close> calculation(3) g_iso_def norms_all_def by auto
              moreover have "r = ?g (norm'  (\<bar>r'\<bar>  \<otimes> x))"
                by (simp add: \<open>norm' x = xx \<and> x \<in> dom\<close> calculation(4) norm_scale)

              ultimately show ?thesis 
                by blast
            qed
          qed
        qed
        ultimately show ?thesis 
          by blast
      qed
      
      ultimately show ?thesis 
        by fastforce
    qed
    let ?gB = "{(?g b)|b. b\<in>?B}"
    have "?gB = {r::real. r\<le>0}"


 proof-
      have "\<forall>a. (a\<in>?B \<longrightarrow> ?g a \<le>0)"
      proof
        fix a
        show "(a\<in>?B \<longrightarrow> ?g a \<le>0)"
        proof
            assume "a\<in>?B"
            show "?g a\<le>0"
            proof-
              obtain "r" where "a = norm'  (r \<otimes> y) "
                     using \<open>a \<in> {norm' (r \<otimes> y) |r. True}\<close> by blast
              moreover have "?g a = ?g (norm'  (r \<otimes> y) )"
                using calculation by presburger
              moreover have "?g a = ?g ( otimes' \<bar>r\<bar> (norm' y))"
                by (simp add: \<open>norm' y = yy \<and> y \<in> dom\<close> calculation(1) norm_scale)
               
              moreover have "?g a =  \<bar>r\<bar> * ?g (norm' y)"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' y = yy \<and> y\<in>dom\<close> \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> calculation(3) g_iso_def norms_all_def by auto
               
              ultimately show ?thesis 
                by (simp add: \<open>norm' y = yy \<and> y\<in>dom\<close> \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> mult_le_0_iff order_less_imp_le)
            qed
        qed
      qed
      moreover have "?gB \<subseteq> {r::real. r\<le>0}"
        using calculation by fastforce
      moreover have "{r::real. r\<le>0} \<subseteq> ?gB"
      proof-
        have "bij_betw ?g norms_all UNIV"
          using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> g_iso_def by blast
        moreover have "\<forall>r::real. (r\<le>0 \<longrightarrow> r\<in>?gB)"
        proof
          fix r
          show "r\<le>0 \<longrightarrow> r\<in>?gB"
          proof
            assume "r\<le>0"
            show "r\<in>?gB"
            proof-
              obtain "r'" where "\<bar>r'\<bar> = r / (?g yy)"
                using  *
                by (metis \<open>r \<le> 0\<close> \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> abs_if divide_less_0_iff less_eq_real_def not_less_iff_gr_or_eq)
              moreover have "r =  \<bar>r'\<bar> * (?g yy)"
                using \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> calculation by auto
              moreover have "r =  \<bar>r'\<bar> * (?g (norm' y))"
                using \<open>norm' y = yy \<and> y\<in>dom\<close> calculation(2) by blast
              moreover have "r = ?g (otimes' \<bar>r'\<bar>  (norm' y))"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' y = yy\<and>y\<in>dom\<close> \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> calculation(3) g_iso_def norms_all_def by auto
              moreover have "r = ?g (norm'  (\<bar>r'\<bar>  \<otimes> y))"
                by (simp add: \<open>norm' y = yy \<and> y \<in> dom\<close> calculation(4) norm_scale)
               
              ultimately show ?thesis 
                by blast
            qed
          qed
        qed
        ultimately show ?thesis 
          by blast
      qed
      
      ultimately show ?thesis 
        by fastforce
    qed

    let ?gX_norms = "{(?g x)|x. x\<in>norms}"
    let ?gX_norms_all = "{(?g x)|x. x\<in>norms_all}"
    let ?gA_union_B = "{(?g x)|x. x\<in> ?A\<union>?B}"
    have "?gA_union_B \<subseteq> ?gX_norms"
      using \<open>{norm' (r \<otimes> x) |r. True} \<union> {norm' (r \<otimes> y) |r. True} \<subseteq> norms\<close> by force
    moreover have "?gA_union_B = ?gA \<union> ?gB"
    proof-
      have "?gA_union_B \<subseteq> ?gA \<union> ?gB"
        by blast
      moreover have "?gA \<union> ?gB \<subseteq> ?gA_union_B"
        by blast
      ultimately show ?thesis
        by force
    qed
    moreover have "?gA_union_B = UNIV"
      using \<open>{(if g xx < 0 then \<lambda>x. - 1 * g x else g) a |a. a \<in> {norm' (r \<otimes> x) |r. True}} = {r. 0 \<le> r}\<close> \<open>{(if g xx < 0 then \<lambda>x. - 1 * g x else g) b |b. b \<in> {norm' (r \<otimes> y) |r. True}} = {r. r \<le> 0}\<close> calculation(4) by force
    moreover have "UNIV \<subseteq> ?gX_norms"
      using calculation(3) calculation(5) by argo
  
    obtain "a" where "a\<in>norms_all \<and> \<not>a\<in>norms"
      by (metis (mono_tags, lifting) Un_iff add.inverse_inverse add.inverse_neutral image_eqI local.norm_zero mult_minus1 non_trivial_dom norms_all_def norms_neg_def zero_only_norms_norms_neg)

        let ?a = "?g a"
        have "?a \<in> ?gX_norms_all "

          using \<open>a \<in> norms_all \<and> a \<notin> norms\<close> by blast

        moreover have "\<not>?a\<in> ?gX_norms"
        proof(rule ccontr)
          assume "\<not>(\<not>?a\<in> ?gX_norms)"
          have "?a\<in>?gX_norms"
            using \<open>\<not> (if g xx < 0 then \<lambda>x. - 1 * g x else g) a \<notin> {(if g xx < 0 then \<lambda>x. - 1 * g x else g) x |x. x \<in> norms}\<close> by blast
          then obtain "b" where "b\<in>norms \<and> ?g b = ?a"
            by force
         
            then show False using  \<open>a \<in> norms_all \<and> a \<notin> norms\<close> \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> bij_betw_inv_into_left g_iso_def inf_sup_ord(3) norms_all_def subsetD
              by (smt (verit, ccfv_threshold) \<open>g_iso g\<close>)
          qed
          moreover have "False" 

            using \<open>UNIV \<subseteq> {(if g xx < 0 then \<lambda>x. - 1 * g x else g) x |x. x \<in> norms}\<close> calculation(7) by blast
            
    ultimately show False 
      by auto
  qed
  

  moreover have " bij_betw (\<lambda>x. if x \<in> norms then (?g x) else undefined) norms {r::real. r\<ge>0}"
  proof-
    let ?f = "(\<lambda>x. if x \<in> norms then (?g x) else undefined)"
     let ?A = "{norm' (r \<otimes> x) | r::real. True}"
     let ?gA = "{(?g a)|a. a\<in>?A}"
     have s1:"?gA = {r::real. r\<ge>0}"
        proof-
      have "\<forall>a. (a\<in>?A \<longrightarrow> ?g a \<ge>0)"
      proof
        fix a
        show "(a\<in>?A \<longrightarrow> ?g a \<ge>0)"
        proof
            assume "a\<in>?A"
            show "?g a \<ge>0"
            proof-
              obtain "r" where "a = norm'  (r \<otimes> x) "
                using \<open>a \<in> {norm' (r \<otimes> x) |r. True}\<close> by blast
              moreover have "?g a = ?g (norm'  (r \<otimes> x) )"
                using calculation by presburger
              moreover have "?g a = ?g ( otimes' \<bar>r\<bar> (norm' x))"
                by (simp add: \<open>norm' x = xx \<and> x \<in> dom\<close> calculation(1) norm_scale)
              moreover have "?g a =  \<bar>r\<bar> * ?g (norm' x)"
                by (metis Un_iff \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' x = xx \<and> x \<in> dom\<close> \<open>xx \<in> norms \<and> xx \<noteq> 0\<close> calculation(3) normed_gyrolinear_space''.g_iso_def normed_gyrolinear_space''_axioms norms_all_def)
               
              ultimately show ?thesis 
                by (simp add: \<open>norm' x = xx \<and> x \<in> dom\<close>)
                
            qed
        qed
      qed
      moreover have "?gA \<subseteq> {r::real. r\<ge>0}"
        using calculation by fastforce
      moreover have "{r::real. r\<ge>0} \<subseteq> ?gA"
      proof-
        have "bij_betw ?g norms_all UNIV"
          using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> g_iso_def by blast
        moreover have "\<forall>r::real. (r\<ge>0 \<longrightarrow> r\<in>?gA)"
        proof
          fix r
          show "r\<ge>0 \<longrightarrow> r\<in>?gA"
          proof
            assume "r\<ge>0"
            show "r\<in>?gA"
            proof-
              obtain "r'" where "\<bar>r'\<bar> = r / (?g xx)"
                using  *
                by (meson \<open>0 \<le> r\<close> abs_of_nonneg divide_nonneg_nonneg)
              moreover have "r =  \<bar>r'\<bar> * (?g xx)"
                by (simp add: \<open>(if g xx < 0 then \<lambda>x. - 1 * g x else g) xx \<noteq> 0\<close> calculation)
              moreover have "r =  \<bar>r'\<bar> * (?g (norm' x))"
                using \<open>norm' x = xx\<and>x\<in>dom\<close> calculation(2) by blast
              moreover have "r = ?g (otimes' \<bar>r'\<bar>  (norm' x))"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' x = xx\<and>x\<in>dom\<close> \<open>xx \<in> norms \<and> xx \<noteq> 0\<close> calculation(3) g_iso_def norms_all_def by auto
              moreover have "r = ?g (norm'  (\<bar>r'\<bar>  \<otimes> x))"
                by (simp add: \<open>norm' x = xx \<and> x \<in> dom\<close> calculation(4) norm_scale)
                
              ultimately show ?thesis 
                by blast
            qed
          qed
        qed
        ultimately show ?thesis 
          by blast
      qed
      
      ultimately show ?thesis 
        by fastforce
    qed
     moreover have s2:"\<forall>y\<in>dom. (?g (norm' y) \<ge>0)"
       using \<open>\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> (if g xx < 0 then \<lambda>x. - 1 * g x else g) x\<close> norms_def
       by blast
     moreover have "norms = ?A"
     proof-
       have "\<forall>y\<in>dom. (?g (norm' y) \<in> ?gA)"
         using s1 s2 by blast
       moreover have "norms \<subseteq> ?A"
       proof-
         have "\<forall>y. (y\<in>norms \<longrightarrow> y\<in>?A)"
         proof
           fix y
           show "y\<in>norms \<longrightarrow> y\<in>?A"
           proof
             assume "y\<in>norms"
             show "y\<in>?A"
             proof-
               obtain "yy" where "y=norm' yy \<and> yy \<in>dom"
                 using \<open>y \<in> norms\<close> norms_def by auto
               moreover have "?g (norm' yy) \<in>?gA"
                 using calculation s1 s2 by auto
                 
               moreover have "norm' yy \<in> ?A"
               proof-
                 obtain "h" where "h \<in> ?A \<and> ?g h = ?g (norm' yy)"
                   using calculation(2) by fastforce
                 moreover have "?g h \<ge>0"
                   using calculation s2 
                   by (simp add: \<open>y = norm' yy \<and> yy \<in> dom\<close>)
                
                 moreover {
                   assume "?g = g"
                   have " g h = g (norm' yy)"
                     by (smt (verit, ccfv_SIG) calculation(1))
                   
                   moreover have "h=norm' yy"
                   proof-
                     have "h\<in>norms"
                       using \<open>h \<in> {norm' (r \<otimes> x) |r. True} \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) h = (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' yy)\<close> \<open>norm' x = xx \<and> x \<in> dom\<close> norms_def scale_closed by force
                      
                     moreover have "norm' yy \<in> norms"
                       using \<open>y = norm' yy\<and>yy\<in>dom\<close> \<open>y \<in> norms\<close> by blast
                     ultimately show ?thesis 
                       by (metis \<open>g h = g (norm' yy)\<close> \<open>g_iso g\<close> bij_betw_inv_into_left g_iso_def inf_sup_ord(3) norms_all_def subset_iff)
                   qed
                   ultimately have ?thesis
                     using \<open>h \<in> {norm' (r \<otimes> x) |r. True} \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) h = (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' yy)\<close> by blast
                 }
                   moreover {
                   assume "?g = (\<lambda>x. -1 * (g x))"
                   have " g h = g (norm' yy)"
                     by (smt (verit, ccfv_SIG) calculation(1))
                   
                   moreover have "h=norm' yy"
                   proof-
                     have "h\<in>norms"
                       using \<open>h \<in> {norm' (r \<otimes> x) |r. True} \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) h = (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' yy)\<close> \<open>norm' x = xx \<and> x \<in> dom\<close> norms_def scale_closed by auto
                       
                     moreover have "norm' yy \<in> norms"
                       using \<open>y = norm' yy\<and>yy\<in>dom\<close> \<open>y \<in> norms\<close> by blast
                     ultimately show ?thesis 
                       by (metis \<open>g h = g (norm' yy)\<close> \<open>g_iso g\<close> bij_betw_inv_into_left g_iso_def inf_sup_ord(3) norms_all_def subset_iff)
                   qed
                   ultimately have ?thesis
                     using \<open>h \<in> {norm' (r \<otimes> x) |r. True} \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) h = (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' yy)\<close> by blast
                 }
                 ultimately show ?thesis 
                   by argo
               qed
               ultimately show ?thesis 
                 by fastforce
             qed
         qed
       qed
        show ?thesis 
          using \<open>\<forall>y. y \<in> norms \<longrightarrow> y \<in> {norm' (r \<otimes> x) |r. True}\<close> by blast
      qed
      ultimately show ?thesis 
        using norms_def
        using \<open>norm' x = xx \<and> x \<in> dom\<close> scale_closed by auto
        
    qed
     moreover have step1:"inj_on ?f  norms"
     proof-
       have "\<forall>x.\<forall>y. (x\<in> norms \<and> y\<in> norms \<and> (?f x) = (?f y) \<longrightarrow> x=y)"
       proof
         fix x 
         show "\<forall>y. (x\<in> norms \<and> y\<in> norms \<and> (?f x) = (?f y) \<longrightarrow> x=y)"
         proof
           fix y 
           show " (x\<in> norms \<and> y\<in> norms \<and> (?f x) = (?f y) \<longrightarrow> x=y)"
             by (metis \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> bij_betw_imp_inj_on g_iso_def inf_sup_ord(3) inj_on_def norms_all_def subsetD)
         qed
       qed
       then show ?thesis
         using inj_on_def by blast
     qed
     moreover have "\<forall>r::real. (r\<ge>0 \<longrightarrow> (\<exists>x. (x\<in> norms \<and> ?f x = r)))"
       by (smt (verit) calculation(3) mem_Collect_eq s1)
       
     moreover have step2:"\<forall>r::real. (r\<ge>0 \<longrightarrow> (\<exists>x\<in> norms.( ?f x = r)))"
 
       using calculation(5) by blast
     moreover have "\<forall>r\<in>{x::real. x\<ge>0}. (\<exists>x\<in>norms. (?f x = r))"
       using step2
       by blast
     moreover have **:"?f=(\<lambda>x. if x \<in> norms then (?g x) else undefined)"
       by meson
     moreover have "?f ` norms = {r::real. r\<ge>0}"
       by (smt (verit) Collect_cong Setcompr_eq_image calculation(3) s1)
     ultimately show ?thesis 
       by (simp add: bij_betw_def)
    
   qed
   moreover have "(\<forall>r. (\<forall>x\<in>dom. (otimes'  \<bar>r\<bar> (norm' x) = (inv_into norms_all ?g) (\<bar>r\<bar> * (?g (norm' x))))))"
  
   proof
     fix r
     show " (\<forall>x\<in>dom. (otimes'  \<bar>r\<bar> (norm' x)= (inv_into norms_all ?g) (\<bar>r\<bar> * (?g (norm' x)))))"
     proof
       fix x
       assume "x\<in>dom"
       show " (otimes'  \<bar>r\<bar> (norm' x) = (inv_into norms_all ?g) ( \<bar>r\<bar>  * (?g (norm' x))))"
       proof-
         have "?g (norm' (scale r x)) = ?g (otimes'  \<bar>r\<bar> (norm' x))"
           by (simp add: \<open>x \<in> dom\<close> norm_scale)
         moreover have "?g (otimes'  \<bar>r\<bar> (norm' x)) =  \<bar>r\<bar>* (?g (norm' x)) "
          
           using UnCI \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>x \<in> dom\<close> g_iso_def
             image_eqI norms_all_def norms_def by force
         moreover have "bij_betw ?g norms_all UNIV"
           using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> g_iso_def by blast
         moreover have "bij_betw (inv_into norms_all ?g) UNIV norms_all "
      
           using bij_betw_inv_into calculation(3) by blast
       
            
        moreover have "otimes'  \<bar>r\<bar> (norm' x)\<in>UNIV"
        
          by blast
        moreover have " (inv_into norms_all ?g) (?g (otimes'  \<bar>r\<bar> (norm' x))) = otimes'  \<bar>r\<bar> (norm' x)"
           using `bij_betw ?g norms_all UNIV` `otimes'  \<bar>r\<bar> (norm' x)\<in>UNIV`
            `bij_betw (inv_into norms_all ?g) UNIV norms_all `
         
           by (metis UnCI \<open>x \<in> dom\<close> bij_betw_inv_into_left image_eqI norm_scale norms_all_def
               norms_def scale_closed)
         ultimately show ?thesis 
       
           by presburger
       qed
     qed
   qed
  ultimately show ?thesis
    by blast
qed


lemma comparing_norms_help:
  assumes "x\<in>norms" "y\<in>norms_all"
  "x\<le>y"
shows "y\<in> norms"
proof-
  have "x < y \<or> x=y"
    using assms(3) by argo
  moreover {
    assume "x<y"
    have ?thesis 
      by (smt (verit, del_insts) \<open>x < y\<close> assms(1) assms(2) image_iff norm_pos norms_def order_dom2)
    
  }
  moreover {
    assume "x=y"
    have ?thesis 
      using \<open>x = y\<close> assms(1) by blast
  }
  ultimately show ?thesis by blast
qed

lemma existence_of_f:
 assumes "\<exists>x. (x\<in>norms_all \<and> x\<noteq>0)" (* not trivial domain *)
  shows "\<exists>f. (bij_betw f norms {x::real. x\<ge>0}
\<and>  (\<forall>y::real. \<forall>z::real. (( y\<in> norms \<and>
z\<in>  norms \<and> y>z)\<longrightarrow> (f y) > (f z)))
  \<and> (\<forall>x\<in>dom. \<forall>y\<in>dom. f(norm' (x \<oplus> y)) \<le> (f (norm' x)) + (f (norm' y)))
\<and> (\<forall>r::real. (\<forall>x\<in>dom. (f (norm' (r \<otimes> x)) = \<bar>r\<bar> * (f (norm' x)))))
\<and> (\<forall>x\<in>dom. \<forall>y\<in>dom. (f (oplus' (norm' x) (norm' y))) = (f (norm' x)) + (f (norm' y)))
\<and> (\<forall>r::real. \<forall>x\<in>dom. f (otimes' \<bar>r\<bar> (norm' x)) = \<bar>r\<bar>*f(norm' x)))"
proof-
  obtain "g" where "(g_iso g \<and> (\<forall>x.(x\<in>norms \<longrightarrow> (g x)\<ge>0))
\<and> bij_betw (\<lambda>x. if x \<in> norms then (g x) else undefined) norms {r::real. r\<ge>0})"
    using  iso_with_real_positive_on_norms
    assms by blast
  let ?f = "\<lambda>x. if x \<in> norms then (g x) else undefined"
  have "\<forall>\<alpha>::real. \<forall>\<beta>::real. \<forall>x\<in>dom. ((0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>) \<longrightarrow> ((otimes' \<alpha>  (norm' x)) \<le> (otimes' \<beta>  (norm' x))))"
  proof
    fix \<alpha> 
    show " \<forall>\<beta>::real. \<forall>x\<in>dom.((0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>) \<longrightarrow> ((otimes' \<alpha>  (norm' x)) \<le> (otimes' \<beta>  (norm' x))))"
    proof
      fix \<beta>
      show " \<forall>x\<in>dom.((0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>) \<longrightarrow> ((otimes' \<alpha>  (norm' x)) \<le> (otimes' \<beta>  (norm' x))))"
      proof
        fix x 
        assume "x\<in>dom"
        show "((0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>) \<longrightarrow> ((otimes' \<alpha>  (norm' x)) \<le> (otimes' \<beta>  (norm' x))))"
        proof
          assume "0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>"
          show "((otimes' \<alpha>  (norm' x)) \<le> (otimes' \<beta>  (norm' x)))"
          proof-
            have "otimes' \<alpha>  (norm' x) = norm' (\<alpha> \<otimes> x)"
              by (simp add: \<open>0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>\<close> \<open>x \<in> dom\<close> norm_scale)

            moreover have " norm' (\<alpha> \<otimes> x) = norm' (((\<beta>+\<alpha>)/2 - (\<beta>-\<alpha>)/2)\<otimes> x)"
              by (simp add: add_divide_distrib diff_divide_distrib)
            moreover have "norm' (((\<beta>+\<alpha>)/2 - (\<beta>-\<alpha>)/2)\<otimes> x) = 
            norm' (((\<beta>+\<alpha>)/2) \<otimes> x \<oplus>  (- (\<beta>-\<alpha>)/2) \<otimes> x )"
              by (metis \<open>x \<in> dom\<close> divide_minus_left minus_real_def scale_distrib)
              
            moreover have " norm' (((\<beta>+\<alpha>)/2) \<otimes> x \<oplus>  (- (\<beta>-\<alpha>)/2) \<otimes> x )
        \<le>  oplus' (norm' (((\<beta>+\<alpha>)/2)\<otimes> x)) (norm' ((-(\<beta>-\<alpha>)/2)  \<otimes> x))"
              by (simp add: \<open>x \<in> dom\<close> norm_ineq scale_closed)
            moreover have "-(\<beta>-\<alpha>)/2 \<le>0"
              by (simp add: \<open>0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>\<close>)
            moreover have "(\<beta>+\<alpha>)/2 \<ge>0"
              using \<open>0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>\<close> by auto
            moreover have *:"(norm' (((\<beta>+\<alpha>)/2)\<otimes> x)) =(otimes' ((\<beta>+\<alpha>)/2) (norm' x))"
              using \<open>x \<in> dom\<close> calculation(6) norm_scale by fastforce
            moreover have " \<bar>-(\<beta>-\<alpha>)/2\<bar> = (\<beta>-\<alpha>)/2 "
              using calculation(5) by force
            moreover have **:"(norm' ((-(\<beta>-\<alpha>)/2)\<otimes> x)) =(otimes' ((\<beta>-\<alpha>)/2) (norm' x))"
              using \<open>x \<in> dom\<close> calculation(8) norm_scale by force
            moreover have "  oplus' (norm' (((\<beta>+\<alpha>)/2)\<otimes> x)) (norm' ((-(\<beta>-\<alpha>)/2)  \<otimes> x)) =
       oplus' (otimes' ((\<beta>+\<alpha>)/2) (norm' x)) (otimes' ( (\<beta>-\<alpha>)/2) (norm' x)) "
              using * **
              by presburger
            moreover have "oplus' (otimes' ((\<beta>+\<alpha>)/2) (norm' x)) (otimes' ( (\<beta>-\<alpha>)/2) (norm' x))
      = otimes' ((\<beta>+\<alpha>)/2 + ((\<beta>-\<alpha>)/2)) (norm' x)"
              using  ax_space one_dim_vector_space_with_domain_def
              vector_space_with_domain.smult_distr_sadd[of norms_all oplus' 0 otimes']
              by (metis UnCI \<open>x \<in> dom\<close> image_eqI vector_space_with_domain.smult_distr_sadd)
            moreover have " otimes' ((\<beta>+\<alpha>)/2 + ((\<beta>-\<alpha>)/2)) (norm' x) = otimes' \<beta> (norm' x)"
              by argo
            ultimately show ?thesis 
              by linarith
          qed
        qed
      qed
    qed
  qed
  moreover have "\<forall>\<alpha>::real. \<forall>\<beta>::real. \<forall>x\<in>dom. ((0 < \<alpha> \<and> \<alpha> < \<beta> \<and> x\<noteq>gyrozero) \<longrightarrow> ((otimes' \<alpha>  (norm' x)) < (otimes' \<beta>  (norm' x))))"
    by (smt (verit, best) bij_betw_iff_bijections calculation image_subset_iff inf_sup_ord(3) iso_with_real local.norm_zero mult_right_cancel norms_all_def norms_def zero_in_dom)
  moreover obtain "xx0" where "xx0\<in>norms \<and> xx0\<noteq>0"
    using assms not_trivial_domen_has_pos by blast
  moreover obtain "x0" where "xx0 = norm' x0"
    using calculation(3) norms_def by auto
  moreover have mon:"(\<forall>y z. y \<in> norms \<and> z \<in> norms \<and> z < y \<longrightarrow> ?f z < ?f y)"
  proof
    fix y 
    show "\<forall>z. (y \<in> norms \<and> z \<in> norms \<and> z < y \<longrightarrow> ?f z < ?f y)"
    proof
      fix z 
      show "y \<in> norms \<and> z \<in> norms \<and> z < y \<longrightarrow> ?f z < ?f y"
      proof
        assume "y \<in>norms \<and> z \<in> norms \<and> z < y"
        show "?f z < ?f y"
        proof-
          let ?alpha = "(?f y)/(?f (norm' x0))"
          let ?beta = "(?f z)/(?f (norm' x0))"
          have "otimes' ?alpha (norm' x0) = y"
            
            by (smt (verit, del_insts) \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> \<open>y \<in> norms \<and> z \<in> norms \<and> z < y\<close> ax_space bij_betw_imp_inj_on calculation(3) calculation(4) g_iso_def in_mono inf_sup_ord(3) inj_on_def nonzero_eq_divide_eq norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed vector_space_with_domain.zero_in_dom)
          moreover have "otimes' ?beta (norm' x0) = z"
            
            by (smt (verit, del_insts) \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> \<open>xx0 = norm' x0\<close> \<open>xx0 \<in> norms \<and> xx0 \<noteq> 0\<close> \<open>y \<in> norms \<and> z \<in> norms \<and> z < y\<close> ax_space bij_betw_imp_inj_on g_iso_def inf_sup_ord(3) inj_on_def nonzero_eq_divide_eq norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) subset_iff vector_space_with_domain.smult_closed vector_space_with_domain.zero_in_dom)
          moreover have "?alpha \<ge> 0 \<and> ?beta \<ge>0"
             using \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> \<open>xx0 = norm' x0\<close> \<open>xx0 \<in> norms \<and> xx0 \<noteq> 0\<close> \<open>y \<in> norms \<and> z \<in> norms \<and> z < y\<close> by auto
           moreover have "0 < ?alpha \<and> ?alpha < ?beta \<longleftrightarrow> 0<y \<and> y<z"
             by (smt (verit, best) \<open>\<forall>\<alpha> \<beta>. \<forall>x\<in>dom. 0 < \<alpha> \<and> \<alpha> < \<beta> \<and> x \<noteq> 0\<^sub>g \<longrightarrow> otimes' \<alpha> (norm' x) < otimes' \<beta> (norm' x)\<close> \<open>xx0 = norm' x0\<close> \<open>xx0 \<in> norms \<and> xx0 \<noteq> 0\<close> \<open>y \<in> norms \<and> z \<in> norms \<and> z < y\<close> calculation(1) calculation(2) image_iff local.norm_zero norms_def)
             
           moreover have "0<?alpha \<and> ?alpha < ?beta \<longleftrightarrow> 0 \<le> (?f y) \<and> (?f y) < (?f z)"
             by (smt (verit, best) \<open>\<forall>\<alpha> \<beta>. \<forall>x\<in>dom. 0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta> \<longrightarrow> otimes' \<alpha> (norm' x) \<le> otimes' \<beta> (norm' x)\<close> \<open>xx0 = norm' x0\<close> \<open>xx0 \<in> norms \<and> xx0 \<noteq> 0\<close> \<open>y \<in> norms \<and> z \<in> norms \<and> z < y\<close> calculation(1) calculation(2) calculation(3) divide_nonneg_nonpos divide_strict_right_mono image_iff norms_def)
           
           ultimately show ?thesis
             using \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> \<open>y \<in> norms \<and> z \<in> norms \<and> z < y\<close> by auto
         qed
      qed
    qed
  qed
  moreover have " (\<forall>x\<in>dom. \<forall>y\<in>dom. ?f (norm' (x \<oplus> y)) \<le> ?f (norm' x) + ?f (norm' y))"
  proof
    fix x 
    assume "x\<in>dom"
    show "\<forall>y\<in>dom. (?f (norm' (x \<oplus> y)) \<le> ?f (norm' x) + ?f (norm' y))"
    proof
      fix y
      assume "y\<in>dom"
      show " (?f (norm' (x \<oplus> y)) \<le> ?f (norm' x) + ?f (norm' y))"
      proof-
        have "norm' x\<in>norms"
          using norms_def 
          using \<open>x \<in> dom\<close> by blast
        moreover have "norm' y \<in> norms"
          using norms_def
          using \<open>y \<in> dom\<close> by blast
        moreover have "norm' (x \<oplus> y)\<in> norms"
          using norms_def 
          using \<open>x \<in> dom\<close> \<open>y \<in> dom\<close> gyroplus_closed by blast
        moreover have "norm' (x \<oplus> y) \<le> oplus' (norm' x) (norm' y)"
          by (simp add: \<open>x \<in> dom\<close> \<open>y \<in> dom\<close> norm_ineq)
        moreover have "(?f (norm' (x \<oplus> y))) \<le> (?f (oplus' (norm' x) (norm' y)))"
        proof-
          have "norm' (x \<oplus> y) \<le> oplus' (norm' x) (norm' y) \<or> norm' (x \<oplus> y) = oplus' (norm' x) (norm' y)"
            using calculation(4) by blast
          moreover {
            assume st1:"norm' (x \<oplus> y) < oplus' (norm' x) (norm' y)"
            have "norm' x \<in> norms"
              using norms_def 
              using \<open>norm' x \<in> norms\<close> by blast
            moreover have "norm' y \<in> norms"
              using norms_def 
              using \<open>norm' y \<in> norms\<close> by blast
            moreover have "vector_space_with_domain norms_all oplus' 0 otimes'"
              using ax_space norms_def 
              one_dim_vector_space_with_domain_def
              by (metis norms_all_def norms_neg_def)
            moreover have "oplus' (norm' x) (norm' y) \<in> norms_all"
              by (metis Un_iff calculation(1) calculation(2) calculation(3) norms_all_def vector_space_with_domain.add_closed)
            moreover have st2:"norm' (x \<oplus> y)\<in> norms"
              by (simp add: \<open>norm' (x \<oplus> y) \<in> norms\<close>)
            moreover have st3:"oplus' (norm' x) (norm' y) \<in> norms"  
              using \<open>norm' (x \<oplus> y) \<le> oplus' (norm' x) (norm' y)\<close> calculation(4) comparing_norms_help st2 by blast
moreover have "(?f (norm' (x \<oplus> y))) < (?f (oplus' (norm' x) (norm' y)))"
              using mon st1 st2 st3
              by blast
            ultimately have ?thesis 
              by linarith
          }
          moreover {
              assume "norm' (x \<oplus> y) = oplus' (norm' x) (norm' y)"
              then have ?thesis 
                by auto
            }
            ultimately show ?thesis
              by fastforce
        qed 
        moreover have " (?f (oplus' (norm' x) (norm' y))) = (?f (norm' x)) + (?f (norm' y))"
        proof-
          have f1:"norm' (x \<oplus> y) \<le> oplus' (norm' x) (norm' y)"
            using calculation(4) by force
          moreover have f2:"norm' (x \<oplus> y) \<in> norms"
            by (simp add: \<open>norm' (x \<oplus> y) \<in> norms\<close>)
          moreover have f3:"vector_space_with_domain norms_all oplus' 0 otimes'"
              using ax_space norms_def 
              one_dim_vector_space_with_domain_def
              by (metis norms_all_def norms_neg_def)
          moreover have "oplus' (norm' x) (norm' y)\<in> norms"
              by (metis UnI1 \<open>norm' x \<in> norms\<close> \<open>norm' y \<in> norms\<close> f1 f2 f3 normed_gyrolinear_space''.comparing_norms_help normed_gyrolinear_space''_axioms norms_all_def vector_space_with_domain.add_closed)
            ultimately show ?thesis 
              using \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> \<open>norm' x \<in> norms\<close> \<open>norm' y \<in> norms\<close> g_iso_def norms_all_def by force
          qed
          ultimately show ?thesis 
            by force
      qed
    qed
  qed

  moreover have "(\<forall>r::real. (\<forall>x\<in>dom. (?f (norm' (r \<otimes> x)) = \<bar>r\<bar> * (?f (norm' x)))))"
    by (smt (verit, del_insts) \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> image_eqI image_subset_iff inf_sup_ord(3) norm_scale normed_gyrolinear_space''.g_iso_def normed_gyrolinear_space''_axioms norms_all_def norms_def scale_closed)



 moreover have " (\<forall>x\<in>dom. \<forall>y\<in>dom.  (?f (oplus' (norm' x) (norm' y))) = (?f (norm' x)) + (?f (norm' y)))"
  proof
    fix x 
    assume "x\<in>dom"
    show "\<forall>y\<in>dom.  ((?f (oplus' (norm' x) (norm' y))) = (?f (norm' x)) + (?f (norm' y)))"
    proof
      fix y
      assume "y\<in>dom"
      show " ((?f (oplus' (norm' x) (norm' y))) = (?f (norm' x)) + (?f (norm' y)))"
      proof-
        have "norm' x\<in>norms"
          using norms_def 
          using \<open>x \<in> dom\<close> by blast
        moreover have "norm' y \<in> norms"
          using norms_def
          using \<open>y \<in> dom\<close> by blast
        moreover have "norm' (x \<oplus> y)\<in> norms"
          using norms_def 
          using \<open>x \<in> dom\<close> \<open>y \<in> dom\<close> gyroplus_closed by blast
        moreover have "norm' (x \<oplus> y) \<le> oplus' (norm' x) (norm' y)"
          by (simp add: \<open>x \<in> dom\<close> \<open>y \<in> dom\<close> norm_ineq)
        moreover have "(?f (norm' (x \<oplus> y))) \<le> (?f (oplus' (norm' x) (norm' y)))"
        proof-
          have "norm' (x \<oplus> y) \<le> oplus' (norm' x) (norm' y) \<or> norm' (x \<oplus> y) = oplus' (norm' x) (norm' y)"
            using calculation(4) by blast
          moreover {
            assume st1:"norm' (x \<oplus> y) < oplus' (norm' x) (norm' y)"
            have "norm' x \<in> norms"
              using norms_def 
              using \<open>norm' x \<in> norms\<close> by blast
            moreover have "norm' y \<in> norms"
              using norms_def 
              using \<open>norm' y \<in> norms\<close> by blast
            moreover have "vector_space_with_domain norms_all oplus' 0 otimes'"
              using ax_space norms_def 
              one_dim_vector_space_with_domain_def
              by (metis norms_all_def norms_neg_def)
            moreover have "oplus' (norm' x) (norm' y) \<in> norms_all"
              by (metis Un_iff calculation(1) calculation(2) calculation(3) norms_all_def vector_space_with_domain.add_closed)
            moreover have st2:"norm' (x \<oplus> y)\<in> norms"
              by (simp add: \<open>norm' (x \<oplus> y) \<in> norms\<close>)
            moreover have st3:"oplus' (norm' x) (norm' y) \<in> norms"  
              using \<open>norm' (x \<oplus> y) \<le> oplus' (norm' x) (norm' y)\<close> calculation(4) comparing_norms_help st2 by blast
moreover have "(?f (norm' (x \<oplus> y))) < (?f (oplus' (norm' x) (norm' y)))"
              using mon st1 st2 st3
              by blast
            ultimately have ?thesis 
              by linarith
          }
          moreover {
              assume "norm' (x \<oplus> y) = oplus' (norm' x) (norm' y)"
              then have ?thesis 
                by auto
            }
            ultimately show ?thesis
              by fastforce
        qed 
        moreover have " (?f (oplus' (norm' x) (norm' y))) = (?f (norm' x)) + (?f (norm' y))"
        proof-
          have f1:"norm' (x \<oplus> y) \<le> oplus' (norm' x) (norm' y)"
            using calculation(4) by force
          moreover have f2:"norm' (x \<oplus> y) \<in> norms"
            by (simp add: \<open>norm' (x \<oplus> y) \<in> norms\<close>)
          moreover have f3:"vector_space_with_domain norms_all oplus' 0 otimes'"
              using ax_space norms_def 
              one_dim_vector_space_with_domain_def
              by (metis norms_all_def norms_neg_def)
          moreover have "oplus' (norm' x) (norm' y)\<in> norms"
              by (metis UnI1 \<open>norm' x \<in> norms\<close> \<open>norm' y \<in> norms\<close> f1 f2 f3 normed_gyrolinear_space''.comparing_norms_help normed_gyrolinear_space''_axioms norms_all_def vector_space_with_domain.add_closed)
            ultimately show ?thesis 
              using \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> \<open>norm' x \<in> norms\<close> \<open>norm' y \<in> norms\<close> g_iso_def norms_all_def by force
          qed
          ultimately show ?thesis 
            by force
      qed
    qed
  qed
  moreover have "\<forall>r::real. \<forall>x\<in>dom. ?f (otimes' \<bar>r\<bar> (norm' x)) = \<bar>r\<bar>*?f(norm' x)"
  
    by (metis calculation(7) norm_scale)
 
  ultimately show ?thesis
    using \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> 
    by blast
qed



end
context normed_gyrolinear_space'
begin
lemma is_normed_gyrolinear_space'':
  shows "normed_gyrolinear_space'' dom gyrozero gyroplus gyroinv gyr scale norm' 
(\<lambda>x y. (if x\<in>norms_all \<and> y\<in>norms_all then (inv_into norms_all f') ((f' x)+(f' y)) else undefined))
(\<lambda>r a. (if a\<in>norms_all  then (inv_into norms_all f') (r*(f' a)) else undefined))"
proof
  show "\<forall>a\<in>dom. 0 \<le> norm' a"
    using norm_pos by argo
next
  show " \<And>x y. x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
           y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
           (if x \<in> norms_all \<and> y \<in> norms_all
            then inv_into norms_all f' (f' x + f' y) else undefined)
           \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom"
    by (metis UNIV_I bij_betw_imp_surj_on f'_bij inv_into_into norms_all_def norms_def norms_neg_def)
next
  show "0 \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom"
    using local.norm_zero zero_in_dom by fastforce
next
  show "\<And>x y z.
       x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
       y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
       z \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
       (if (if x \<in> norms_all \<and> y \<in> norms_all
            then inv_into norms_all f' (f' x + f' y) else undefined)
           \<in> norms_all \<and>
           z \<in> norms_all
        then inv_into norms_all f'
              (f' (if x \<in> norms_all \<and> y \<in> norms_all
                   then inv_into norms_all f' (f' x + f' y) else undefined) +
               f' z)
        else undefined) =
       (if x \<in> norms_all \<and>
           (if y \<in> norms_all \<and> z \<in> norms_all
            then inv_into norms_all f' (f' y + f' z) else undefined)
           \<in> norms_all
        then inv_into norms_all f'
              (f' x +
               f' (if y \<in> norms_all \<and> z \<in> norms_all
                   then inv_into norms_all f' (f' y + f' z) else undefined))
        else undefined)"
  proof -
    fix x :: real and y :: real and z :: real
    assume a1: "z \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom"
    assume a2: "y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom"
    assume a3: "x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom"
    obtain rr :: "'a \<Rightarrow> real" where
      f4: "\<forall>X1. rr X1 = - 1 * norm' X1"
      by moura
    then have f5: "norms_all = norm' ` dom \<union> rr ` dom"
      using norms_all_def norms_def norms_neg_def by presburger
    then have f6: "x \<in> norms_all"
      using f4 a3 by presburger
    have f7: "y \<in> norms_all"
      using f5 f4 a2 by presburger
    have f8: "z \<in> norms_all"
      using f5 f4 a1 by presburger
    have "bij_betw f' norms_all UNIV"
      using f5 f4 f'_bij by presburger
    then have "inv_into norms_all f' (f' y + f' z) \<in> norms_all \<and> inv_into norms_all f' (f' x + f' y) \<in> norms_all \<and> inv_into norms_all f' (f' (inv_into norms_all f' (f' x + f' y)) + f' z) = inv_into norms_all f' (f' x + f' (inv_into norms_all f' (f' y + f' z)))"
      by (simp add: add.assoc bij_betw_imp_surj_on f_inv_into_f inv_into_into)
    then show "(if (if x \<in> norms_all \<and> y \<in> norms_all then inv_into norms_all f' (f' x + f' y) else undefined) \<in> norms_all \<and> z \<in> norms_all then inv_into norms_all f' (f' (if x \<in> norms_all \<and> y \<in> norms_all then inv_into norms_all f' (f' x + f' y) else undefined) + f' z) else undefined) = (if x \<in> norms_all \<and> (if y \<in> norms_all \<and> z \<in> norms_all then inv_into norms_all f' (f' y + f' z) else undefined) \<in> norms_all then inv_into norms_all f' (f' x + f' (if y \<in> norms_all \<and> z \<in> norms_all then inv_into norms_all f' (f' y + f' z) else undefined)) else undefined)"
      using f8 f7 f6 by presburger
  qed
next
  show "\<And>x y. x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
           y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
           (if x \<in> norms_all \<and> y \<in> norms_all
            then inv_into norms_all f' (f' x + f' y) else undefined) =
           (if y \<in> norms_all \<and> x \<in> norms_all
            then inv_into norms_all f' (f' y + f' x) else undefined)"
    by argo
next
  show " \<And>x. x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
         (if x \<in> norms_all \<and> 0 \<in> norms_all
          then inv_into norms_all f' (f' x + f' 0) else undefined) =
         x"
    by (metis norm_oplus_f_def norms_all_def norms_def norms_neg_def vector_space_of_norms vector_space_with_domain.add_zero)
next
  show "\<And>x. x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
         \<exists>y\<in>norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom.
            (if x \<in> norms_all \<and> y \<in> norms_all
             then inv_into norms_all f' (f' x + f' y) else undefined) =
            0"
    by (metis norm_oplus_f_def norms_all_def norms_def norms_neg_def vector_space_of_norms vector_space_with_domain.add_inv)
next
  show "\<And>x a. x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
           (if x \<in> norms_all then inv_into norms_all f' (a * f' x)
            else undefined)
           \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom"
    by (metis UNIV_I bij_betw_imp_surj_on f'_bij inv_into_into norms_all_def norms_def norms_neg_def)
next
  show " \<And>x a b.
       x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
       (if x \<in> norms_all then inv_into norms_all f' ((a + b) * f' x)
        else undefined) =
       (if (if x \<in> norms_all then inv_into norms_all f' (a * f' x)
            else undefined)
           \<in> norms_all \<and>
           (if x \<in> norms_all then inv_into norms_all f' (b * f' x)
            else undefined)
           \<in> norms_all
        then inv_into norms_all f'
              (f' (if x \<in> norms_all then inv_into norms_all f' (a * f' x)
                   else undefined) +
               f' (if x \<in> norms_all then inv_into norms_all f' (b * f' x)
                   else undefined))
        else undefined)"
    by (smt (verit, ccfv_SIG) norm_oplus_f_def normed_gyrolinear_space'.norm_otimes_f_def normed_gyrolinear_space'_axioms norms_all_def norms_def norms_neg_def vector_space_of_norms vector_space_with_domain.smult_distr_sadd)
next
  show "\<And>x a b.
       x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
       (if (if x \<in> norms_all then inv_into norms_all f' (b * f' x)
            else undefined)
           \<in> norms_all
        then inv_into norms_all f'
              (a *
               f' (if x \<in> norms_all then inv_into norms_all f' (b * f' x)
                   else undefined))
        else undefined) =
       (if x \<in> norms_all then inv_into norms_all f' (a * b * f' x)
        else undefined)"
    by (smt (verit) UNIV_I bij_betw_imp_surj_on f'_bij f_inv_into_f inv_into_into mult.assoc norms_all_def norms_def norms_neg_def)
next
  show "\<And>x. x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
         (if x \<in> norms_all then inv_into norms_all f' (1 * f' x)
          else undefined) =
         x"
    by (metis norm_otimes_f_def norms_all_def norms_def norms_neg_def vector_space_of_norms vector_space_with_domain.smult_one)
next
  show "\<forall>y x. y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and>
          x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> x \<noteq> 0 \<longrightarrow>
          (\<exists>!r. y =
                (if x \<in> norms_all then inv_into norms_all f' (r * f' x)
                 else undefined))"
  proof
    show " \<And>y. \<forall>x. y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and>
             x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> x \<noteq> 0 \<longrightarrow>
             (\<exists>!r. y =
                   (if x \<in> norms_all then inv_into norms_all f' (r * f' x)
                    else undefined))"
    proof-
      fix y
      show "\<forall>x. y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and>
             x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> x \<noteq> 0 \<longrightarrow>
             (\<exists>!r. y =
                   (if x \<in> norms_all then inv_into norms_all f' (r * f' x)
                    else undefined))"
      proof
        fix x
        show "y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and>
             x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> x \<noteq> 0 \<longrightarrow>
             (\<exists>!r. y =
                   (if x \<in> norms_all then inv_into norms_all f' (r * f' x)
                    else undefined))"
        proof
          assume "y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and>
             x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> x \<noteq> 0"
          show "(\<exists>!r. y =
                   (if x \<in> norms_all then inv_into norms_all f' (r * f' x)
                    else undefined))"
          proof-
            have "x\<in>norms_all"
              using \<open>y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> x \<noteq> 0\<close> norms_all_def norms_def norms_neg_def by argo
            let ?r = "(f' y)/(f' x)"
            have "f' x \<noteq>0"
              by (smt (verit, del_insts) \<open>y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> x \<noteq> 0\<close> f'_mon normed_gyrolinear_space'.axioms(2) normed_gyrolinear_space'_axioms normed_gyrolinear_space'_axioms_def norms_all_def norms_def norms_neg_def vector_space_of_norms vector_space_with_domain.zero_in_dom)
            then have "y = inv_into norms_all f' (?r * f' x)"
              by (metis \<open>y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<and> x \<noteq> 0\<close> bij_betw_inv_into_left f'_bij nonzero_eq_divide_eq norms_all_def norms_def norms_neg_def)
            then show ?thesis
              by (metis UNIV_I \<open>f' x \<noteq> 0\<close> \<open>x \<in> norms_all\<close> bij_betw_imp_surj_on f'_bij f_inv_into_f nonzero_mult_div_cancel_right norms_all_def norms_def norms_neg_def)
          qed
        qed
          qed

  qed
 
qed
next
  show "\<forall>x\<in>dom.
       \<forall>y\<in>dom.
          norm' (x \<oplus> y)
          \<le> (if norm' x \<in> norms_all \<and> norm' y \<in> norms_all
              then inv_into norms_all f' (f' (norm' x) + f' (norm' y))
              else undefined)"
    using norm_oplus_f_def r2 by auto
next
  show "\<forall>r. \<forall>x\<in>dom.
           norm' (r \<otimes> x) =
           (if norm' x \<in> norms_all
            then inv_into norms_all f' (\<bar>r\<bar> * f' (norm' x)) else undefined)"
    by (simp add: norm_otimes_f_def r3)
next
  show "\<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>x\<in>dom. norm' (gyr u v x) = norm' x"
    using norm_gyr by linarith
next
  show " \<forall>x\<in>dom. (norm' x = 0) = (x = 0\<^sub>g) "
    using local.norm_zero by force
next
  show " \<And>x y a.
       x \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
       y \<in> norm' ` dom \<union> (\<lambda>x. - 1 * norm' x) ` dom \<Longrightarrow>
       (if (if x \<in> norms_all \<and> y \<in> norms_all then inv_into norms_all f' (f' x + f' y)
            else undefined)
           \<in> norms_all
        then inv_into norms_all f'
              (a *
               f' (if x \<in> norms_all \<and> y \<in> norms_all
                   then inv_into norms_all f' (f' x + f' y) else undefined))
        else undefined) =
       (if (if x \<in> norms_all then inv_into norms_all f' (a * f' x) else undefined)
           \<in> norms_all \<and>
           (if y \<in> norms_all then inv_into norms_all f' (a * f' y) else undefined)
           \<in> norms_all
        then inv_into norms_all f'
              (f' (if x \<in> norms_all then inv_into norms_all f' (a * f' x)
                   else undefined) +
               f' (if y \<in> norms_all then inv_into norms_all f' (a * f' y)
                   else undefined))
        else undefined)"
    by (smt (verit) UNIV_I bij_betw_imp_surj_on f'_bij f_inv_into_f inv_into_into
        norms_all_def norms_def norms_neg_def ring_class.ring_distribs(1))
qed
end

context ggv_space
begin
lemma is_normed_gyrolinear'':
  assumes " plus'_zero = 0"
  shows "normed_gyrolinear_space'' dom gyrozero gyroplus gyroinv gyr scale gyronorm plus' smult'"

proof-
  have *:"gyrolinear_space dom gyrozero gyroplus gyroinv gyr scale"
    by (simp add: gyrocommutative_gyrogroup_axioms gyrolinear_space_axioms_def
        gyrolinear_space_def scale_1_ggv scale_assoc_ggv scale_closed_ggv scale_distrib_ggv scale_gyr1_ggv
        scale_gyr_id_ggv)
  moreover have A1:"(\<forall>a\<in>dom. 0 \<le> gyronorm a)"
    by (simp add: gyronorm_def)
  moreover have A2:" one_dim_vector_space_with_domain (gyronorm ` dom \<union> (\<lambda>x. - 1 * gyronorm x) ` dom)
          plus' plus'_zero smult'"
    using one_dim_vs_ggv
    using norm_set_equality by argo
  
  moreover have A3: " (\<forall>x\<in>dom. \<forall>y\<in>dom. gyronorm (gyroplus x y) \<le> plus' (gyronorm x) (gyronorm y))"
    by (simp add: gyronorm_def gyroplus_closed local.norm_triangle_ineq_ggv)
  moreover have A4: "  (\<forall>r. \<forall>x\<in>dom. gyronorm (scale r x) = smult' \<bar>r\<bar> (gyronorm x))"
    by (simp add: gyronorm_def norm_smult'_ggv scale_closed_ggv)
  moreover have A5: "   (\<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>x\<in>dom. gyronorm (gyr u v x) = gyronorm x)"
    by (simp add: ax_norm_ggv gyr_def_closed gyronorm_def)
  moreover have A6:"    (\<forall>x\<in>dom. (gyronorm x = plus'_zero) = (x = gyrozero))"
    using local.norm_zero norm_zero_iff
    by (simp add: gyronorm_def prop_3_2a)

  moreover have N:"((\<forall>a\<in>dom. 0 \<le> \<llangle>a\<rrangle>) \<and>
     one_dim_vector_space_with_domain (gyronorm ` dom \<union> (\<lambda>x. - 1 * \<llangle>x\<rrangle>) ` dom) plus' plus'_zero
      smult' \<and>
     (\<forall>x\<in>dom. \<forall>y\<in>dom. \<llangle>x \<oplus> y\<rrangle> \<le> plus' (\<llangle>x\<rrangle>) (\<llangle>y\<rrangle>))) \<and>
    (\<forall>r. \<forall>x\<in>dom. \<llangle>r \<otimes> x\<rrangle> = smult' \<bar>r\<bar> (\<llangle>x\<rrangle>)) \<and>
    (\<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>x\<in>dom. \<llangle>gyr u v x\<rrangle> = \<llangle>x\<rrangle>) \<and> (\<forall>x\<in>dom. (\<llangle>x\<rrangle> = plus'_zero) = (x = 0\<^sub>g))"
    using A1 A2 A3 A4 A5 A6 

    by meson
  
  moreover have " normed_gyrolinear_space''_axioms dom 0\<^sub>g (\<oplus>) gyr (\<otimes>) gyronorm plus' smult'"
    using N   normed_gyrolinear_space''_axioms_def[of dom gyrozero gyroplus gyr scale gyronorm plus' smult']
    using assms by fastforce
  moreover have M:"gyrolinear_space dom gyrozero gyroplus gyroinv gyr scale \<and>  normed_gyrolinear_space''_axioms dom 0\<^sub>g (\<oplus>) gyr (\<otimes>) gyronorm plus' smult'"
    using "*" calculation(9) by force
  ultimately show ?thesis
      using normed_gyrolinear_space''_def[of dom gyrozero gyroplus gyroinv gyr scale gyronorm plus' smult']
      M 
      by blast
qed

lemma gyrodistance_metric_zero_iff:
  assumes "a\<in>dom" "b\<in>dom"
  shows "d\<^sub>\<oplus> a b = plus'_zero \<longleftrightarrow> a = b"
  unfolding gyrodistance_def gyronorm_def
  using gyronorm_def norm_zero_iff  fi_zero
  by (metis assms(1,2) ax1 gyro_left_inv gyroplus_closed oplus_ominus_cancel
      prop_3_2a)


end



















(*


lemma I6_39:
  shows "a \<oplus> (1/2) \<otimes> (\<ominus> a \<oplus> b) = (1/2) \<otimes> (a \<oplus>\<^sub>c b)"
  by (metis I6_38 gyro_equation_right gyro_inv_idem)

text "T6.16"
lemma I6_40:
  shows "gyr ((r + s) \<otimes> a) b x = gyr (r\<otimes>a) (s\<otimes>a \<oplus> b) (gyr (s\<otimes>a) b x)"
  by (metis (mono_tags, opaque_lifting) comp_eq_elim gyroauto_id id_def gyr_nested_1 scale_distrib)

(* ---------------------------------------------------------------------------- *)
definition collinear :: "'a => 'a => 'a => bool" where
  "collinear x y z \<longleftrightarrow> (y = z \<or> (\<exists>t::real. (x = y \<oplus> t \<otimes> (\<ominus> y \<oplus> z))))"

lemma collinear_aab:
  shows "collinear a a b"
  by (metis collinear_def gyro_right_id gyro_rigth_inv scale_distrib scale_minus)

lemma collinear_bab:
  shows "collinear b a b"
  by (metis collinear_def gyro_equation_right scale_1)

lemma T6_20:
  assumes "collinear p1 a b" "collinear p2 a b" "a \<noteq> b" "p1 \<noteq> p2"
  shows "\<forall>x. (collinear x p1 p2 \<longrightarrow> collinear x a b)"
proof safe
  obtain t1 where t1: "p1 = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)"
    using \<open>collinear p1 a b\<close> \<open>a \<noteq> b\<close> collinear_def 
    by auto
  obtain t2 where t2: "p2 = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)"
    using \<open>collinear p2 a b\<close> \<open>a \<noteq> b\<close> collinear_def
    by blast

  fix x
  assume "collinear x p1 p2"
  show "collinear x a b"
  proof-
    obtain t where t: "x = p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2)"
      using \<open>collinear x p1 p2\<close> \<open>p1 \<noteq> p2\<close> collinear_def 
      by blast
    have "x = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> t \<otimes> (\<ominus> (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> (a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)))"
      using t1 t2 t
      by simp
    then have "x = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> t \<otimes> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) ((-t1 + t2) \<otimes> (\<ominus> a \<oplus> b))"
      by (smt (verit, best) gyr_def scale_distrib)
    then have "x = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) ((t*(-t1 + t2)) \<otimes> (\<ominus> a \<oplus> b))"
      using gyroauto_property scale_assoc by presburger
    then have "x = a \<oplus> (t1 \<otimes> (\<ominus> a \<oplus> b) \<oplus> ((t*(-t1 + t2)) \<otimes> (\<ominus> a \<oplus> b)))"
      by (simp add: gyro_left_assoc)
    then  have "x = a \<oplus> (t1 + t*(-t1 + t2)) \<otimes> (\<ominus> a \<oplus> b)"
      by (simp add: scale_distrib)
    then show ?thesis  
      using collinear_def by blast
  qed
qed


lemma T6_20_1:
  assumes "collinear p1 a b" "collinear p2 a b" "p1 \<noteq> p2" "a \<noteq> b"
  shows "\<forall>x. (collinear x a b \<longrightarrow> collinear x p1 p2)"
proof safe
  obtain t1 where t1: "p1 = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)"
    using \<open>collinear p1 a b\<close> \<open>a \<noteq> b\<close> collinear_def 
    by auto
  obtain t3 where t3: "p2 = a \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b)"
    using \<open>collinear p2 a b\<close> \<open>a \<noteq> b\<close> collinear_def
    by blast

  fix x
  assume "collinear x a b"
  show "collinear x p1 p2" 
  proof-
    obtain t2 where "x = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)"
      using \<open>collinear x a b\<close> \<open>a \<noteq> b\<close> collinear_def
      by blast
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
        by (metis (no_types, lifting) gyro_translation_2a mult.commute scale_assoc scale_minus1)
      then have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) (((-t1+t3)*t) \<otimes> (\<ominus> a \<oplus> b) )"
        by (metis (no_types, opaque_lifting) gyroauto_property minus_mult_commute mult.commute mult.right_neutral scale_assoc scale_distrib scale_minus1)
      then have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = a \<oplus> (t1 \<otimes> (\<ominus> a \<oplus> b) \<oplus> ((-t1+t3)*t) \<otimes> (\<ominus> a \<oplus> b)) "
        using gyro_left_assoc by metis
      then have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = a \<oplus> (t1 + (-t1+t3)*t) \<otimes> ((\<ominus> a \<oplus> b))"
        using scale_distrib by presburger
      moreover have "t1 + (-t1+t3)*t = t2"
        using \<open>t1 \<noteq> t3\<close> t
        by simp
      ultimately
      have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)"
        by blast
      then show ?thesis
        using \<open>x = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)\<close> 
        unfolding collinear_def
        by metis
    qed
  qed
qed

lemma collinear_sym1:
  assumes "collinear a b c"
  shows "collinear b a c"
  using T6_20_1 assms collinear_aab collinear_bab collinear_def by blast

lemma collinear_sym2:
  assumes "collinear a b c"
  shows "collinear a c b"
  by (metis T6_20 assms collinear_aab collinear_bab)

lemma collinear_transitive:
  assumes "collinear a b c" "collinear d b c" "b \<noteq> c"
  shows "collinear a d b" 
  by (metis T6_20 assms(1) assms(2) assms(3) collinear_bab collinear_sym1 collinear_sym2)

lemma collinear_translate':
  shows "x = u \<oplus> t \<otimes> (\<ominus> u \<oplus> v) \<longleftrightarrow> 
        (\<ominus> a \<oplus> x) = (\<ominus> a \<oplus> u) \<oplus> t \<otimes> (\<ominus> (\<ominus> a \<oplus> u) \<oplus> (\<ominus> a \<oplus> v))"
  thm gyro_translation_2a
  by (metis (no_types, lifting) gyr_misc_2 gyro_right_assoc gyro_translation_2a gyroauto_property oplus_ominus_cancel)

definition translate where
  "translate a x = \<ominus> a \<oplus> x"

lemma collinear_translate:
  shows "collinear u v w \<longleftrightarrow> collinear (translate a u) (translate a v) (translate a w)"
  unfolding collinear_def translate_def
  by (metis collinear_translate' gyro_left_cancel')

definition gyroline :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "gyroline a b = {x. collinear x a b}"

definition between :: "'a => 'a => 'a => bool" where
  "between x y z \<longleftrightarrow> (\<exists>t::real. 0 \<le> t \<and> t \<le> 1 \<and> y = x \<oplus> t \<otimes> (\<ominus> x \<oplus> z))"

lemma between_xxy [simp]:
  shows "between x x y"
  unfolding between_def
  by (rule_tac x=0 in exI) simp

lemma between_xyy [simp]:
  shows "between x y y"
  unfolding between_def
  by (rule_tac x=1 in exI) (simp add: scale_1)

lemma between_xyx:
  assumes "between x y x"
  shows "y = x"
  using assms
  unfolding between_def
  by auto

lemma between_translate:
  shows "between u v w \<longleftrightarrow> between (translate a u) (translate a v) (translate a w)"
  unfolding between_def translate_def
  using collinear_translate' 
  by auto

definition distance where
  "distance u v = \<llangle>\<ominus> u \<oplus> v\<rrangle>"

lemma distance_translate:
  shows "distance u v = distance (translate a u) (translate a v)"
  unfolding distance_def translate_def
  using gyro_translation_2a norm_gyr 
  by metis

end*)

context normed_gyrolinear_space
begin

lemma proposition_3_4_help:
  fixes h::"real\<Rightarrow>real"
  assumes  "inj_on h (norm'` dom)"
  shows "bij_betw h (norm' ` dom) (h ` norm' ` dom)"
  using assms bij_betw_imageI by blast
 
lemma proposition_3_4:
  fixes h::"real\<Rightarrow>real"
  assumes "h 0 = 0" "inj_on h (norm'`dom)" "\<forall>x\<in>(norm'`dom). (h x)\<ge>0" 
    "\<forall>x\<in>(norm'`dom). \<forall>y\<in>(norm'`dom). (x > y \<longrightarrow> (h x) > (h y))"
  shows "normed_gyrolinear_space dom gyrozero gyroplus gyroinv gyr scale
         (\<lambda>x. if x \<in> dom then (h \<circ> norm')x else undefined)
 (\<lambda>x. if x \<in> (h`norm'`dom) then (f \<circ> (inv_into ( norm' ` dom) h)) x else undefined)"
proof
  show  "\<forall>a\<in>dom. 0 \<le> (if a \<in> dom then (h \<circ> norm') a else undefined)"
    by (simp add: assms(3))
next
  show " \<forall>y. y \<in> (\<lambda>x. if x \<in> dom then (h \<circ> norm') x else undefined) ` dom \<longrightarrow>
        0 \<le> (if y \<in> h`norm' ` dom then (f \<circ> inv_into (norm' ` dom) h) y
              else undefined)"
  proof-
    have "\<forall>y. y \<in> (h \<circ> norm') ` dom \<longrightarrow> 0 \<le> (f \<circ> (inv_into (norm' ` dom) h)) y"
  proof
    fix y
    show " y \<in> (h \<circ> norm') ` dom \<longrightarrow> 0 \<le> (f \<circ> (inv_into (norm' ` dom) h)) y"
    proof
    assume " y \<in> (h \<circ> norm') ` dom"
    show "0 \<le> (f \<circ> (inv_into ( norm' ` dom) h)) y"
      by (metis \<open>y \<in> (h \<circ> norm') ` dom\<close> comp_apply f_pos image_comp inv_into_into)
     qed
   qed
   then show ?thesis
     by (simp add: image_comp)
 qed
next
  show " bij_betw
     (\<lambda>x. if x \<in> h ` norm' ` dom then (f \<circ> inv_into (norm' ` dom) h) x
           else undefined)
     ((\<lambda>x. if x \<in> dom then (h \<circ> norm') x else undefined) ` dom) {x. 0 \<le> x}"
  proof-
    have " bij_betw (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') ` dom) {x. 0 \<le> x}"

    by (metis assms(2) bij_betw_comp_iff bij_betw_imageI bij_betw_inv_into f_bij image_comp)
  then show ?thesis
    by (smt (z3) bij_betw_def comp_def imageE imageI image_cong inj_on_def)
qed
next
  show " \<forall>y z. y \<in> (\<lambda>x. if x \<in> dom then (h \<circ> norm') x else undefined) ` dom \<and>
          z \<in> (\<lambda>x. if x \<in> dom then (h \<circ> norm') x else undefined) ` dom \<and>
          z < y \<longrightarrow>
          (if z \<in> h ` norm' ` dom then (f \<circ> inv_into (norm' ` dom) h) z
           else undefined)
          < (if y \<in> h ` norm' ` dom then (f \<circ> inv_into (norm' ` dom) h) y
             else undefined)"
  proof-
    have "\<forall>y z. y \<in> (h \<circ> norm') ` dom \<and> z \<in> (h \<circ> norm') ` dom \<and> z < y \<longrightarrow>
          (f \<circ> inv_into (norm' ` dom) h) z < (f \<circ> inv_into (norm' ` dom) h) y"
    by (smt (verit, best) assms(4) comp_apply f_inv_into_f f_mon image_comp inv_into_into norm_pos)
  then show ?thesis 
    by (simp add: image_iff)
qed
next
  show " \<forall>x\<in>dom.
       \<forall>y\<in>dom.
          (if (if x \<oplus> y \<in> dom then (h \<circ> norm') (x \<oplus> y) else undefined)
              \<in> h ` norm' ` dom
           then (f \<circ> inv_into (norm' ` dom) h)
                 (if x \<oplus> y \<in> dom then (h \<circ> norm') (x \<oplus> y) else undefined)
           else undefined)
          \<le> (if (if x \<in> dom then (h \<circ> norm') x else undefined) \<in> h ` norm' ` dom
              then (f \<circ> inv_into (norm' ` dom) h)
                    (if x \<in> dom then (h \<circ> norm') x else undefined)
              else undefined) +
             (if (if y \<in> dom then (h \<circ> norm') y else undefined)
                 \<in> h ` norm' ` dom
              then (f \<circ> inv_into (norm' ` dom) h)
                    (if y \<in> dom then (h \<circ> norm') y else undefined)
              else undefined)"
  proof-
    have " \<forall>x\<in>dom.
       \<forall>y\<in>dom.
          (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') (x \<oplus> y))
          \<le> (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') x) +
             (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') y)"
  proof
    fix x 
    assume "x\<in>dom"
    show "\<forall>y\<in>dom.
          (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') (x \<oplus> y))
          \<le> (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') x) +
             (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') y)"
    proof
      fix y
      assume "y\<in>dom"
      show " (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') (x \<oplus> y))
          \<le> (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') x) +
             (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') y)"
      proof-
        have " (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') (x \<oplus> y)) =
            f (norm' (x \<oplus> y))"

          by (simp add: \<open>x \<in> dom\<close> \<open>y \<in> dom\<close> assms(2) gyroplus_closed)

        moreover have "  f (norm' (x \<oplus> y)) \<le> f (norm' x) + f (norm' y)"
        proof -
          have "normed_gyrolinear_space_axioms dom 0\<^sub>g (\<oplus>) gyr (\<otimes>) norm' f"
            by (meson normed_gyrolinear_space_axioms normed_gyrolinear_space_def)
          then show ?thesis
            by (simp add: \<open>x \<in> dom\<close> \<open>y \<in> dom\<close> normed_gyrolinear_space_axioms_def)
        qed
        ultimately show ?thesis 
          by (simp add: \<open>x \<in> dom\<close> \<open>y \<in> dom\<close> assms(2))
    
      qed
    qed
  qed
  then show ?thesis
    by (simp add: gyroplus_closed)
qed
next
  show " \<forall>r. \<forall>x\<in>dom.
           (if (if r \<otimes> x \<in> dom then (h \<circ> norm') (r \<otimes> x) else undefined)
               \<in> h ` norm' ` dom
            then (f \<circ> inv_into (norm' ` dom) h)
                  (if r \<otimes> x \<in> dom then (h \<circ> norm') (r \<otimes> x) else undefined)
            else undefined) =
           \<bar>r\<bar> *
           (if (if x \<in> dom then (h \<circ> norm') x else undefined) \<in> h ` norm' ` dom
            then (f \<circ> inv_into (norm' ` dom) h)
                  (if x \<in> dom then (h \<circ> norm') x else undefined)
            else undefined)"
  proof-
    have " \<forall>r. \<forall>x\<in>dom.
           (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') (r \<otimes> x)) =
           \<bar>r\<bar> * (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') x)"
  proof
    fix r
    show " \<forall>x\<in>dom. (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') (r \<otimes> x)) =
           \<bar>r\<bar> * (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') x)"
    proof
      fix x
      assume "x\<in>dom"
      show " (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') (r \<otimes> x)) =
           \<bar>r\<bar> * (f \<circ> inv_into (norm' ` dom) h) ((h \<circ> norm') x)"
        by (smt (verit, del_insts) \<open>x \<in> dom\<close> assms(2) bij_betw_imp_inj_on comp_apply image_eqI inv_into_f_eq normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def proposition_3_4_help scale_closed)
    qed
  qed
  then show ?thesis 
    by (simp add: scale_closed)
qed
next
  show " \<forall>u\<in>dom.
       \<forall>v\<in>dom.
          \<forall>x\<in>dom.
             (if gyr u v x \<in> dom then (h \<circ> norm') (gyr u v x) else undefined) =
             (if x \<in> dom then (h \<circ> norm') x else undefined)"
  proof-
    have "\<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>x\<in>dom. (h \<circ> norm') (gyr u v x) = (h \<circ> norm') x"
    by (smt (verit, ccfv_threshold) comp_apply normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def)
  then show ?thesis 
    by (smt (z3) gyrogroup_axioms gyrogroup_axioms_def gyrogroup_def)
qed
next
  show "\<forall>x\<in>dom. ((if x \<in> dom then (h \<circ> norm') x else undefined) = 0) = (x = 0\<^sub>g)"
  proof-
    have "\<forall>x\<in>dom. ((h \<circ> norm') x = 0) \<longleftrightarrow> (x = 0\<^sub>g)"
  proof
    fix x
    assume "x\<in>dom"
    show " ((h \<circ> norm') x = 0) \<longleftrightarrow> (x = 0\<^sub>g)"
    proof
      show " (h \<circ> norm') x = 0 \<Longrightarrow> x = 0\<^sub>g"
        by (smt (verit, best) \<open>x \<in> dom\<close> assms(1) assms(2) comp_def image_iff inj_onD normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def zero_in_dom)
    next
      show "x = 0\<^sub>g \<Longrightarrow> (h \<circ> norm') x = 0"
        by (smt (verit) \<open>x \<in> dom\<close> assms(1) comp_apply normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def)
    qed
  qed
  then show ?thesis 
    by auto
qed
qed

end


locale fi_iso = 
  gyrolinear_space + 
  fixes fi::"'a \<Rightarrow> 'b" 
  assumes fi_inj_dom:"inj_on fi dom"

begin


definition fi_inv::"'b \<Rightarrow> 'b"  where 
  "fi_inv b = (if (b\<in>fi`dom) then (fi (gyroinv ((inv_into dom fi) b)))
     else undefined)"

lemma fi_inv_def_lemma:
  shows "\<forall>a\<in>dom. (fi_inv (fi a) = fi (gyroinv a))"
  by (simp add: fi_inj_dom fi_inv_def)

definition fi_gyr::"'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow>'b" where
  "fi_gyr a b c = (if a\<in>(fi`dom) \<and> b\<in>(fi`dom) \<and> c\<in>(fi`dom) then 
      fi (gyr ((inv_into dom fi)a)  ((inv_into dom fi)b)  ((inv_into dom fi)c))
else undefined)"

lemma  fi_gyr_def_lemma:
  shows "\<forall>a\<in>dom.\<forall>b\<in>dom.\<forall>c\<in>dom. fi_gyr (fi a) (fi b) (fi c) = fi (gyr a b c)"
  by (simp add: fi_gyr_def fi_inj_dom)

definition  fi_plus::"'b\<Rightarrow>'b\<Rightarrow>'b" where 
  "fi_plus a b = (if a\<in>(fi`dom) \<and> b\<in>(fi`dom) then fi((gyroplus ((inv_into dom fi)a)
    ((inv_into dom fi)b))) else undefined)"

lemma  fi_plus_def_lemma:
  shows "\<forall>a\<in>dom. \<forall>b\<in>dom. fi_plus (fi a) (fi b) = fi (gyroplus a b)"
  by (simp add: fi_inj_dom fi_plus_def)

definition fi_scale::"real \<Rightarrow> 'b \<Rightarrow> 'b" where 
  "fi_scale r a = (if a\<in>(fi`dom) then fi (scale r ((inv_into dom fi)a))
    else undefined)"

lemma fi_scale_def_lemma:
  shows "\<forall>r::real. \<forall>a\<in>dom. fi_scale r (fi a) = fi (scale r a)"
  by (simp add: fi_inj_dom fi_scale_def)


(*
"gyr a b x = \<ominus> (a \<oplus> b) \<oplus> (a \<oplus> (b \<oplus> x))"
*)
interpretation fi_X_groupoid:  gyrogroupoid "(fi ` dom)" "(fi 0\<^sub>g)" fi_plus
proof
  show "fi 0\<^sub>g \<in> (fi`dom)"
    using zero_in_dom by blast

next
  show "\<And>a b. a \<in> (fi`dom) \<and> b \<in> (fi`dom) \<longrightarrow> fi_plus a b \<in> (fi`dom)"
    by (simp add: fi_plus_def gyroplus_closed inv_into_into)
next
  show "\<exists>a. a \<in> fi ` dom \<and> a \<noteq> fi 0\<^sub>g"
    by (meson fi_inj_dom imageI inj_on_def non_trivial_dom zero_in_dom)
qed

interpretation fi_X_gyrolin_space: gyrolinear_space "(fi ` dom)" "(fi gyrozero)" fi_plus 
  fi_inv fi_gyr fi_scale
proof
  show "\<And>a. a \<in> fi ` dom \<longrightarrow> fi_inv a \<in> fi ` dom"
    by (metis ax1 fi_inv_def image_iff inv_into_into)

next
  show "\<And>a b c. a \<in> fi ` dom \<and> b \<in> fi ` dom \<and> c \<in> fi ` dom \<longrightarrow> fi_gyr a b c \<in> fi ` dom"
    by (smt (verit, ccfv_threshold) fi_gyr_def_lemma gyrogroup_axioms gyrogroup_axioms_def gyrogroup_def image_iff)
next
  show "\<And>a. a \<in> fi ` dom \<longrightarrow> fi_plus (fi 0\<^sub>g) a = a"
    using fi_plus_def_lemma zero_in_dom by force
next 
  show " \<And>a. a \<in> fi ` dom \<longrightarrow> fi_plus (fi_inv a) a = fi 0\<^sub>g"
    using ax1 fi_inv_def_lemma fi_plus_def_lemma by force
next
  show " \<And> a b z.
       a \<in> fi ` dom \<and> b \<in> fi ` dom \<and> z \<in> fi ` dom \<longrightarrow>
       fi_plus a (fi_plus b z) = fi_plus (fi_plus a b) (fi_gyr a b z)"
  proof-
    fix a b z
    show " a \<in> fi ` dom \<and> b \<in> fi ` dom \<and> z \<in> fi ` dom \<longrightarrow>
       fi_plus a (fi_plus b z) = fi_plus (fi_plus a b) (fi_gyr a b z)"
    proof
      assume " a \<in> fi ` dom \<and> b \<in> fi ` dom \<and> z \<in> fi ` dom "
      show " fi_plus a (fi_plus b z) = fi_plus (fi_plus a b) (fi_gyr a b z)"
      proof-
        obtain "a'" where "a'\<in>dom \<and> a = (fi a')"
          using \<open>a \<in> fi ` dom \<and> b \<in> fi ` dom \<and> z \<in> fi ` dom\<close> by blast
        moreover obtain "b'" where "b'\<in>dom \<and> b = (fi b')"
          using \<open>a \<in> fi ` dom \<and> b \<in> fi ` dom \<and> z \<in> fi ` dom\<close> by blast
        moreover obtain "z'" where "z'\<in>dom \<and> z = (fi z')"
          using \<open>a \<in> fi ` dom \<and> b \<in> fi ` dom \<and> z \<in> fi ` dom\<close> by blast
        moreover have "fi_plus a (fi_plus b z) = fi_plus (fi a') (fi_plus (fi b') (fi z'))"
          using calculation(1) calculation(2) calculation(3) by blast
        moreover have " fi_plus (fi a') (fi_plus (fi b') (fi z')) = fi_plus (fi a')   (fi (gyroplus b' z'))"
          using calculation(2) calculation(3) fi_plus_def_lemma by auto
        moreover have " fi_plus (fi a')   (fi (gyroplus b' z')) = fi (gyroplus a' (gyroplus b' z'))"
          by (simp add: calculation(1) calculation(2) calculation(3) fi_plus_def_lemma gyroplus_closed)
        moreover have " fi (gyroplus a' (gyroplus b' z')) = fi ( (a' \<oplus> b') \<oplus> (gyr a' b' z'))"
          using calculation(1) calculation(2) calculation(3) gyro_left_assoc by presburger
        moreover have " fi ( (a' \<oplus> b') \<oplus> (gyr a' b' z')) = fi_plus (fi (a' \<oplus> b')) (fi (gyr a' b' z'))"
          by (metis bij_betwE calculation(1) calculation(2) calculation(3) fi_plus_def_lemma gyr_gyroaut gyroaut_def gyroplus_closed)
        ultimately show ?thesis 
          using fi_gyr_def_lemma fi_plus_def_lemma by auto  
      qed
  qed
qed
next
  show "\<And>a b. a \<in> fi ` dom \<and> b \<in> fi ` dom \<longrightarrow>
           (\<forall>x\<in>fi ` dom. fi_gyr a b x = fi_gyr (fi_plus a b) b x)"
  proof-
    fix a b
    show " a \<in> fi ` dom \<and> b \<in> fi ` dom \<longrightarrow>
           (\<forall>x\<in>fi ` dom. fi_gyr a b x = fi_gyr (fi_plus a b) b x)"
    proof
      assume "a \<in> fi ` dom \<and> b \<in> fi ` dom"
      show "(\<forall>x\<in>fi ` dom. fi_gyr a b x = fi_gyr (fi_plus a b) b x)"
      proof
        fix x
        assume "x\<in>fi`dom"
        show " fi_gyr a b x = fi_gyr (fi_plus a b) b x"
        proof-
          obtain "a'" where "a'\<in>dom \<and> fi a' = a"
            using \<open>a \<in> fi ` dom \<and> b \<in> fi ` dom\<close> by blast
          moreover  obtain "b'" where "b'\<in>dom \<and> fi b' = b"
            using \<open>a \<in> fi ` dom \<and> b \<in> fi ` dom\<close> by blast
          moreover  obtain "x'" where "x'\<in>dom \<and> fi x' = x"
            using \<open>x \<in> fi ` dom\<close> by blast
          ultimately show ?thesis 
            by (metis fi_gyr_def_lemma fi_plus_def_lemma gyr_left_loop gyroplus_closed)
        qed
      qed
    qed
  qed
next
  show "\<And>x y. x \<in> fi ` dom \<and> y \<in> fi ` dom \<longrightarrow>
           gyrogroupoid.gyroaut (fi ` dom) fi_plus (fi_gyr x y)"
  proof
    fix x y
    assume " x \<in> fi ` dom \<and> y \<in> fi ` dom "
    show " gyrogroupoid.gyroaut (fi ` dom) fi_plus (fi_gyr x y)"
    proof-
      let ?fi_dom = "fi`dom"
      let ?fi_zero = "fi  gyrozero"
      let ?fi_gyr = "(fi_gyr x y)"
       obtain "x'" where "x'\<in>dom \<and> fi x' = x"
            using \<open>x \<in> fi ` dom \<and> y \<in> fi ` dom\<close> by blast
          moreover  obtain "y'" where "y'\<in>dom \<and> fi y' =y"
            using \<open>x \<in> fi ` dom \<and> y \<in> fi ` dom\<close> by blast
          
           moreover have A:"bij_betw  (fi_gyr x y) (fi`dom) (fi`dom) "
           proof-
             have "\<forall>t\<in>dom. (fi_gyr x y (fi t)) = fi (gyr x' y' t)"
               using calculation(1) calculation(2) fi_gyr_def_lemma by blast
             moreover have "bij_betw (gyr x' y') dom dom"
               using \<open>x' \<in> dom \<and> fi x' = x\<close> \<open>y' \<in> dom \<and> fi y' = y\<close> gyr_gyroaut gyroaut_def by blast
             moreover have "inj_on (fi_gyr x y) (fi`dom)"
                  by (smt (verit) bij_betw_iff_bijections calculation(1) calculation(2) fi_inj_dom inj_on_def inj_on_imp_bij_betw)
                moreover have "(fi_gyr x y)`fi`dom = fi`dom"
                proof-
                  have "(fi_gyr x y)`fi`dom \<subseteq> fi`dom"
                    by (smt (verit, ccfv_SIG) bij_betw_def calculation(1) calculation(2) image_iff image_subsetI)
                  moreover have " fi`dom \<subseteq> (fi_gyr x y)`fi`dom"
                    by (smt (verit) \<open>\<forall>t\<in>dom. fi_gyr x y (fi t) = fi (gyr x' y' t)\<close> \<open>bij_betw (gyr x' y') dom dom\<close> bij_betw_def image_iff image_subsetI)
                  ultimately show ?thesis 
                    by blast
                qed
                ultimately show ?thesis 
                  by (metis inj_on_imp_bij_betw)
              qed
           moreover have B:"\<forall>a\<in> (fi`dom). (\<forall>b\<in> (fi`dom). ((fi_gyr x y)  (fi_plus a b) = fi_plus
 ( (fi_gyr x y)  a) ( (fi_gyr x y)  b)))"
           proof
             fix a 
             assume "a\<in>(fi ` dom)"
             show "(\<forall>b\<in> (fi`dom). ((fi_gyr x y)  (fi_plus a b) = fi_plus
 ( (fi_gyr x y)  a) ( (fi_gyr x y)  b)))"
             proof
               fix b
               assume "b\<in>(fi ` dom)"
               show "((fi_gyr x y)  (fi_plus a b) = fi_plus
 ( (fi_gyr x y)  a) ( (fi_gyr x y)  b))"
               proof-
                 obtain "a'" where "a'\<in>dom \<and> a = fi a'"
                   using \<open>a \<in> fi ` dom\<close> by blast
                 moreover  obtain "b'" where "b'\<in>dom \<and> b = fi b'"
                   using \<open>b \<in> fi ` dom\<close> by blast
                 moreover have "(fi_gyr x y)  (fi_plus a b) = fi (gyr x' y' (gyroplus a' b')) "
                   using \<open>x' \<in> dom \<and> fi x' = x\<close> \<open>y' \<in> dom \<and> fi y' = y\<close> calculation(1) calculation(2) fi_gyr_def_lemma fi_plus_def_lemma gyroplus_closed by force
                 moreover have "fi (gyr x' y' (gyroplus a' b')) = fi (gyroplus (gyr x' y' a') (gyr x' y' b'))"
                   by (simp add: \<open>x' \<in> dom \<and> fi x' = x\<close> \<open>y' \<in> dom \<and> fi y' = y\<close> calculation(1) calculation(2))
                 ultimately show ?thesis 
                   by (smt (verit, del_insts) \<open>x' \<in> dom \<and> fi x' = x\<close> \<open>y' \<in> dom \<and> fi y' = y\<close> fi_gyr_def_lemma fi_plus_def_lemma gyrogroup_axioms gyrogroup_axioms_def gyrogroup_def)
               qed
             qed
           qed
           moreover have AB: "(bij_betw  (fi_gyr x y) (fi`dom) (fi`dom)) \<and>
(\<forall>a\<in> (fi`dom). (\<forall>b\<in> (fi`dom). ((fi_gyr x y)  (fi_plus a b) = fi_plus
 ( (fi_gyr x y)  a) ( (fi_gyr x y)  b))))"
             using A B by fastforce
           moreover have *:" gyrogroupoid (fi ` dom) (fi 0\<^sub>g) fi_plus"
             using fi_X_groupoid.gyrogroupoid_axioms by blast
           moreover have "fi_X_groupoid.gyroaut (fi_gyr x y)"
             using gyrogroupoid.gyroaut_def[of ?fi_dom ?fi_zero fi_plus, OF *]
             AB 
             by blast
           ultimately show ?thesis 
             by force      
    qed
  qed
next
  show "\<forall>a\<in>fi ` dom. \<forall>b\<in>fi ` dom. fi_plus a b = fi_gyr a b (fi_plus b a)"
    by (smt (verit, best) f_inv_into_f fi_gyr_def_lemma fi_plus_def_lemma gyro_commute gyroplus_closed inv_into_into)
next
  show "\<forall>r. \<forall>x\<in>fi ` dom. fi_scale r x \<in> fi ` dom"
    using fi_scale_def_lemma scale_closed by force
next
  show "\<forall>a\<in>fi ` dom. fi_scale 1 a = a"
    by (simp add: fi_scale_def_lemma scale_1)
next
  show " \<forall>r1 r2.
       \<forall>a\<in>fi ` dom. fi_scale (r1 + r2) a = fi_plus (fi_scale r1 a) (fi_scale r2 a)"
  proof
    fix r1 
    show " \<forall>r2. \<forall>a\<in>fi ` dom. fi_scale (r1 + r2) a = fi_plus (fi_scale r1 a) (fi_scale r2 a)"
    proof
      fix r2
      show " \<forall>a\<in>fi ` dom. fi_scale (r1 + r2) a = fi_plus (fi_scale r1 a) (fi_scale r2 a)"
      proof
        fix a
        assume "a\<in>fi ` dom"
        show " fi_scale (r1 + r2) a = fi_plus (fi_scale r1 a) (fi_scale r2 a)"
          using \<open>a \<in> fi ` dom\<close> fi_plus_def_lemma fi_scale_def_lemma scale_closed scale_distrib by force
      qed
    qed
  qed
next
  show  "\<forall>r1 r2. \<forall>a\<in>fi ` dom. fi_scale (r1 * r2) a = fi_scale r1 (fi_scale r2 a)"
    by (simp add: fi_scale_def_lemma scale_assoc scale_closed)
next
  show "\<forall>u\<in>fi ` dom.
       \<forall>v\<in>fi ` dom.
          \<forall>r. \<forall>a\<in>fi ` dom. fi_gyr u v (fi_scale r a) = fi_scale r (fi_gyr u v a)"
    by (smt (z3) f_inv_into_f fi_gyr_def_lemma fi_scale_def_lemma gyroauto_property gyrogroup_axioms gyrogroup_axioms_def gyrogroup_def inv_into_into scale_closed)
next 
  show " \<forall>r1 r2. \<forall>v\<in>fi ` dom. \<forall>x\<in>fi ` dom. fi_gyr (fi_scale r1 v) (fi_scale r2 v) x = x"
    by (simp add: fi_gyr_def_lemma fi_scale_def_lemma gyroauto_id scale_closed)
qed

lemma gyrolin_I:
  shows " gyrolinear_space (fi ` dom) (fi gyrozero) fi_plus 
  fi_inv fi_gyr fi_scale"
  using fi_X_gyrolin_space.gyrolinear_space_axioms by fastforce
end



locale fi_iso2 =
  fi_iso + normed_gyrolinear_space
begin

interpretation is_fi_iso: fi_iso dom "0\<^sub>g" "(\<oplus>)" "\<ominus>" gyr "(\<otimes>)" fi 
  by (simp add: fi_gyr_def fi_inj_dom fi_inv_def fi_iso.intro fi_iso_axioms_def fi_plus_def fi_scale_def gyrolinear_space_axioms)

interpretation fi_X_gyrolin_space: gyrolinear_space "(fi ` dom)" "(fi gyrozero)" fi_plus 
  fi_inv fi_gyr fi_scale
  using gyrolin_I by blast


definition fi_norm::"'b \<Rightarrow> real" where 
  "fi_norm a = (if a\<in>(fi`dom) then  (norm' ((inv_into dom fi)a))
    else undefined)"

lemma fi_norm_def_lemma: "\<forall>a\<in>dom. fi_norm (fi a) = norm' a"
  using fi_inj_dom fi_norm_def by auto

interpretation fi_X_norm_gyrolin_space: normed_gyrolinear_space "(fi ` dom)" "(fi gyrozero)" fi_plus 
  fi_inv fi_gyr fi_scale fi_norm f
proof
  show "\<forall>a\<in>fi ` dom. 0 \<le> fi_norm a"
    by (simp add: fi_norm_def_lemma norm_pos)
next
  show " \<forall>y. y \<in> fi_norm ` fi ` dom \<longrightarrow> 0 \<le> f y"
    by (simp add: f_pos fi_norm_def_lemma image_iff)
next
  show "bij_betw f (fi_norm ` fi ` dom) {x. 0 \<le> x}"
    by (smt (verit, ccfv_SIG) f_bij fi_norm_def_lemma image_cong image_image)

next
  show "\<forall>y z. y \<in> fi_norm ` fi ` dom \<and> z \<in> fi_norm ` fi ` dom \<and> z < y \<longrightarrow> f z < f y"
    by (simp add: f_mon fi_norm_def_lemma image_iff)
next
  show "\<forall>x\<in>fi ` dom.
       \<forall>y\<in>fi ` dom. f (fi_norm (fi_plus x y)) \<le> f (fi_norm x) + f (fi_norm y)"
  proof
    fix x 
    assume "x\<in>fi`dom"
    show "  \<forall>y\<in>fi ` dom. f (fi_norm (fi_plus x y)) \<le> f (fi_norm x) + f (fi_norm y)"
    proof
      fix y
      assume "y\<in>fi`dom"
      show "f (fi_norm (fi_plus x y)) \<le> f (fi_norm x) + f (fi_norm y)"
      proof-
        obtain "x'" where "x'\<in>dom \<and> fi x' = x"
          using \<open>x \<in> fi ` dom\<close> by blast  
        moreover obtain "y'" where "y'\<in>dom \<and> fi y' = y"
          using \<open>y \<in> fi ` dom\<close> by blast
        moreover have "fi_norm (fi_plus x y) = fi_norm (fi (gyroplus x' y'))"
          using \<open>y' \<in> dom \<and> fi y' = y\<close> calculation fi_plus_def_lemma by fastforce
        moreover have "fi_norm (fi_plus x y) = norm' (gyroplus x' y')"
          by (simp add: calculation(1) calculation(2) calculation(3) fi_norm_def_lemma gyroplus_closed)
        moreover have "f (fi_norm (fi_plus x y)) \<le> f(norm' x') + f(norm' y')"
        proof -
          have "normed_gyrolinear_space_axioms dom 0\<^sub>g (\<oplus>) gyr (\<otimes>) norm' f"
            by (metis (no_types) normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms)
          then show ?thesis
            by (simp add: calculation(1) calculation(2) calculation(4) normed_gyrolinear_space_axioms_def)
        qed
        ultimately show ?thesis 
          using fi_norm_def_lemma by force
      qed
    qed
  qed
next
  show " \<forall>r. \<forall>x\<in>fi ` dom. f (fi_norm (fi_scale r x)) = \<bar>r\<bar> * f (fi_norm x)"
    by (smt (verit, ccfv_SIG) fi_norm_def_lemma
        fi_scale_def_lemma image_iff normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def normed_gyrolinear_space_def scale_closed)
next
  show " \<forall>u\<in>fi ` dom. \<forall>v\<in>fi ` dom. \<forall>x\<in>fi ` dom. fi_norm (fi_gyr u v x) = fi_norm x"
  proof
    fix u
    assume "u\<in>fi`dom"
    show " \<forall>v\<in>fi ` dom. \<forall>x\<in>fi ` dom. fi_norm (fi_gyr u v x) = fi_norm x"
    proof
      fix v
      assume "v\<in>fi`dom"
      show " \<forall>x\<in>fi ` dom. fi_norm (fi_gyr u v x) = fi_norm x "
      proof
        fix x
        assume "x\<in>fi`dom"
        show "fi_norm (fi_gyr u v x) = fi_norm x"
        proof-
          obtain "u'" where "u'\<in>dom \<and> fi u' = u"
            using \<open>u \<in> fi ` dom\<close> by blast
          moreover obtain "v'" where "v'\<in>dom \<and> fi v' = v"
            using \<open>v \<in> fi ` dom\<close> by blast
          moreover obtain "x'" where "x'\<in>dom \<and> fi x' = x"
            using \<open>x \<in> fi ` dom\<close> by blast
          moreover have "fi_norm (fi_gyr u v x) = fi_norm (fi (gyr u' v' x'))"
            using calculation(1) calculation(2) calculation(3) fi_gyr_def_lemma by force
          moreover have "fi_norm (fi_gyr u v x) = norm' (gyr u' v' x')"
            by (metis (full_types) bij_betw_iff_bijections calculation(1) calculation(2) calculation(3) calculation(4) fi_norm_def_lemma gyr_gyroaut gyroaut_def)
          moreover have "norm' (gyr u' v' x') = norm' x'"
          proof -
            have "normed_gyrolinear_space_axioms dom 0\<^sub>g (\<oplus>) gyr (\<otimes>) norm' f"
              by (meson normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms)
            then show ?thesis
              by (simp add: calculation(1) calculation(2) calculation(3) normed_gyrolinear_space_axioms_def)
          qed
          ultimately show ?thesis 
            by (metis fi_norm_def_lemma)
        qed
      qed
    qed
  qed
next
  show "\<forall>x\<in>fi ` dom. (fi_norm x = 0) = (x = fi 0\<^sub>g)"
  proof
    fix x
    assume "x\<in>fi`dom"
    show " (fi_norm x = 0) = (x = fi 0\<^sub>g)"
      by (smt (verit, best) \<open>x \<in> fi ` dom\<close> f_inv_into_f fi_norm_def_lemma inv_into_into normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def zero_in_dom)
  qed
qed


lemma normed_gyrolin_I:
  shows "normed_gyrolinear_space (fi ` dom) (fi gyrozero) fi_plus 
  fi_inv fi_gyr fi_scale fi_norm f"
  using fi_X_norm_gyrolin_space.normed_gyrolinear_space_axioms by blast
  
end


context normed_gyrolinear_space
begin

lemma proposition_3_10:
  fixes \<alpha>::real
  fixes \<alpha>_plus::"'a\<Rightarrow>'a \<Rightarrow>'a"
  assumes "\<alpha> \<noteq> 0"
  "\<forall>a.\<forall>b. \<alpha>_plus a b =  (if (a\<in>dom \<and> b\<in>dom) then scale (1/\<alpha>) (gyroplus (scale \<alpha> a) (scale \<alpha> b))
    else undefined)"
shows "normed_gyrolinear_space dom gyrozero \<alpha>_plus (\<lambda>x. (if x \<in>dom then gyroinv x else undefined))
 (\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)
 )  (\<lambda>r a. if a \<in> dom then r \<otimes> a else undefined)
(\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
          else undefined) f"
proof-
  let ?fi = "\<lambda>x. (if x \<in> dom then scale (1/\<alpha>) x else undefined)"
  let ?fi_inv ="\<lambda>x. if x\<in>dom then (scale \<alpha> x) else undefined"
  have "bij_betw ?fi dom dom"
  proof-
    have "inj_on ?fi dom"
      using assms(1) div_by_1 divide_divide_eq_right divide_self inj_on_inverseI scale_1 scale_assoc times_divide_eq_right
    proof -
      have "\<forall>a r. r \<otimes> (if a \<in> dom then (1 / \<alpha>) \<otimes> a else undefined) = (r / \<alpha>) \<otimes> a \<or> a \<notin> dom"
        by (smt (z3) div_by_1 divide_divide_eq_right scale_assoc times_divide_eq_right)
      then show ?thesis
        by (smt (z3) assms(1) divide_self inj_on_inverseI scale_1)
    qed
    moreover have "?fi ` dom = dom"
    proof
      show "?fi`dom \<subseteq> dom"
        by (simp add: image_subset_iff scale_closed)
    next
      show "dom \<subseteq> ?fi ` dom"
      proof
        fix x 
        assume "x\<in>dom"
        show "x\<in>?fi ` dom"
        proof-
          have "(scale (1/ \<alpha>) (scale \<alpha> x)) = x"
            by (metis \<open>x \<in> dom\<close> assms(1) nonzero_eq_divide_eq scale_1 scale_assoc)
          moreover have "scale \<alpha> x \<in>dom"
            using \<open>x \<in> dom\<close> scale_closed by force
          ultimately show ?thesis 
            using image_iff by fastforce
        qed
      qed
    qed
    ultimately show ?thesis 
      by (simp add: bij_betw_def)
  qed
 
  moreover have "\<forall>x\<in>dom. ((inv_into dom ?fi) x = ?fi_inv x)"
  proof-
    {
    fix x
    assume "x\<in>dom"
    have "scale \<alpha> (scale (1/ \<alpha>) x) = scale 1 x"
      by (metis \<open>x \<in> dom\<close> assms(1) mult.commute nonzero_eq_divide_eq scale_assoc)
    moreover have "scale \<alpha> (scale (1/ \<alpha>) x) = x"
      using \<open>x \<in> dom\<close> calculation scale_1 by fastforce
    ultimately have "\<forall>x\<in>dom. (?fi_inv \<circ> ?fi) x = x"
      by (smt (verit, best) assms(1) comp_apply mult.commute nonzero_eq_divide_eq scale_1 scale_assoc scale_closed)
  }
  then show ?thesis 
    by (smt (verit, best) bij_betwE bij_betw_inv_into bij_betw_inv_into_right calculation comp_apply)
qed
  let ?gyr_inv = "(\<lambda>x. (if x \<in>dom then gyroinv x else undefined))"
  let ?gyr_gyr = "\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)"
  let ?gyr_scale = "\<lambda> r a. (if a \<in>dom then ((1 / \<alpha>) \<otimes>
             (r \<otimes> ( \<alpha> \<otimes> a))) else undefined)"
  let ?gyr_norm = "\<lambda>x. (if x\<in>dom then  norm' ( \<alpha> \<otimes> x) else undefined)"
  have "\<forall>x\<in>dom. ?gyr_inv x = gyroinv x"
    by fastforce
  have "\<forall>x\<in>dom. ?fi x = (scale (1/ \<alpha>) x) "
    by force
  have "\<forall>a\<in>dom. \<forall>b\<in>dom. \<forall>c\<in>dom. ?gyr_gyr a b c =  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c))"
    by force
  moreover have *:"fi_iso2 dom gyrozero gyroplus gyroinv gyr scale ?fi norm' f"
    by (smt (verit, ccfv_threshold) bij_betw_imp_inj_on calculation(1) fi_iso.intro fi_iso2_def fi_iso_axioms_def gyrolinear_space_axioms normed_gyrolinear_space_axioms)
  moreover have **:"fi_iso dom gyrozero gyroplus gyroinv gyr scale ?fi"
    using "*" fi_iso2_def by force
 
  moreover have NGS_main: "normed_gyrolinear_space dom gyrozero \<alpha>_plus ?gyr_inv ?gyr_gyr ?gyr_scale ?gyr_norm f"
    using  fi_iso2.normed_gyrolin_I[of  dom gyrozero gyroplus gyroinv gyr scale ?fi norm' f, OF *]

   proof-
 
   have *:"fi_iso2 dom gyrozero gyroplus gyroinv gyr scale ?fi norm' f"
    by (smt (verit, ccfv_threshold) bij_betw_imp_inj_on calculation(1) fi_iso.intro fi_iso2_def fi_iso_axioms_def gyrolinear_space_axioms normed_gyrolinear_space_axioms)
  moreover have **:"fi_iso dom gyrozero gyroplus gyroinv gyr scale ?fi"
    using "*" fi_iso2_def by force
 (*moreover have "gyrolinear_space dom gyrozero \<alpha>_plus ?gyr_inv ?gyr_gyr ?gyr_scale"
    using fi_iso.gyrolin_I[of  dom gyrozero gyroplus gyroinv gyr scale, OF **]
  proof-*)
     have "(\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom = dom"
       using \<open>bij_betw (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) dom dom\<close> bij_betw_imp_surj_on by blast
    moreover have " (if 0\<^sub>g \<in> dom then (1 / \<alpha>) \<otimes> 0\<^sub>g else undefined) = gyrozero"
      by (smt (verit, del_insts) gyro_left_cancel' gyro_left_inv mult_cancel_right1 scale_assoc scale_closed scale_distrib zero_in_dom)
    moreover have "(fi_iso.fi_plus dom (\<oplus>) (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)) = \<alpha>_plus"
      using fi_iso.fi_plus_def[OF **]
    proof-
      {fix a b
      assume "a\<in>dom\<and> b\<in>dom"
      moreover have "(fi_iso.fi_plus dom (\<oplus>) (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)
             a b = (1 / \<alpha>) \<otimes>(
               ((inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)) a) \<oplus>
                (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)) b))"
        by (metis (no_types, lifting) \<open>(\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom = dom\<close> \<open>\<And>b a. fi_iso.fi_plus dom (\<oplus>) (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a b = (if a \<in> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom \<and> b \<in> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom then if inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a \<oplus> inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b \<in> dom then (1 / \<alpha>) \<otimes> (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a \<oplus> inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b) else undefined else undefined)\<close> calculation gyroplus_closed inv_into_into)
      ultimately have "fi_iso.fi_plus dom (\<oplus>) (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)
             a b = \<alpha>_plus a b"
        by (simp add: \<open>\<forall>x\<in>dom. inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) x = (if x \<in> dom then \<alpha> \<otimes> x else undefined)\<close> assms(2))
    }
    then have "\<forall>a\<in>dom.\<forall>b\<in>dom. (fi_iso.fi_plus dom (\<oplus>) (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)
             a b = \<alpha>_plus a b)"
      by blast
    then have "\<forall>a.\<forall>b. (\<not>(a\<in>dom\<and>b\<in>dom) \<longrightarrow> fi_iso.fi_plus dom (\<oplus>) (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)
             a b = undefined)"
   
      using \<open>\<And>b a. fi_iso.fi_plus dom (\<oplus>) (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a b = (if a \<in> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom \<and> b \<in> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom then if inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a \<oplus> inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b \<in> dom then (1 / \<alpha>) \<otimes> (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a \<oplus> inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b) else undefined else undefined)\<close> calculation(2) by presburger

    then have "\<forall>a.\<forall>b. (\<not>(a\<in>dom\<and>b\<in>dom) \<longrightarrow> \<alpha>_plus a b = undefined)"  

      using assms(2) by presburger
    then show ?thesis 
      using \<open>\<forall>a b. \<not> (a \<in> dom \<and> b \<in> dom) \<longrightarrow> fi_iso.fi_plus dom (\<oplus>) (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a b = undefined\<close> \<open>\<forall>a\<in>dom. \<forall>b\<in>dom. fi_iso.fi_plus dom (\<oplus>) (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a b = \<alpha>_plus a b\<close> by fastforce
  qed
  moreover have "(fi_iso.fi_inv dom \<ominus> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined))
    = ?gyr_inv"
    using fi_iso.fi_inv_def[OF **]
     proof-
       {fix a   
       assume "a\<in>dom"
      moreover have "(fi_iso.fi_inv dom \<ominus> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)) a =
            (if \<ominus> (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a)
           \<in> dom
        then (1 / \<alpha>) \<otimes>
             \<ominus> (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a)
        else undefined)"
        using \<open>(\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom = dom\<close> \<open>\<And>b. fi_iso.fi_inv dom \<ominus> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b = (if b \<in> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom then if \<ominus> (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b) \<in> dom then (1 / \<alpha>) \<otimes> \<ominus> (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b) else undefined else undefined)\<close> calculation by presburger
      moreover have "(fi_iso.fi_inv dom \<ominus> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)) a
      = (1 / \<alpha>) \<otimes>
             \<ominus> (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a)"
        by (simp add: \<open>\<forall>x\<in>dom. inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) x = (if x \<in> dom then \<alpha> \<otimes> x else undefined)\<close> ax1 calculation(1) calculation(2) scale_closed)
     moreover have "(fi_iso.fi_inv dom \<ominus> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)) a
      = (1 / \<alpha>) \<otimes>
             \<ominus> ( \<alpha> \<otimes>  a)"
       by (simp add: \<open>\<forall>x\<in>dom. inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) x = (if x \<in> dom then \<alpha> \<otimes> x else undefined)\<close> calculation(1) calculation(3))
     moreover have "?gyr_inv a =  \<ominus>  a"
       using calculation(1) by auto
     moreover have "(1 / \<alpha>) \<otimes>
             \<ominus> ( \<alpha> \<otimes>  a) =  \<ominus>  a "
     proof-
       have "  \<ominus> ( \<alpha> \<otimes>  a) = (-1) \<otimes> (\<alpha>  \<otimes>  a)"
       proof -
         have "0\<^sub>g = (1 + - 1) \<otimes> (\<alpha> \<otimes> a)"
           by (metis add.right_inverse add.right_neutral calculation(1) gyro_left_cancel gyro_left_inv oplus_ominus_cancel scale_closed scale_distrib zero_in_dom)
         then show ?thesis
           by (metis ax1 calculation(1) gyro_left_cancel gyro_left_inv mult_1 oplus_ominus_cancel scale_assoc scale_closed scale_distrib)
       qed
       moreover have "(-1) \<otimes> (\<alpha>  \<otimes>  a) = ((-\<alpha>)  \<otimes>  a)"
         by (metis \<open>a \<in> dom\<close> mult_minus1 scale_assoc)
       moreover have "(1 / \<alpha>) \<otimes>((-\<alpha>)  \<otimes>  a) = (-1)  \<otimes>  a"
            by (metis \<open>a \<in> dom\<close> assms(1) calculation(2) mult.commute nonzero_eq_divide_eq scale_1 scale_assoc scale_closed)
          ultimately show ?thesis 
            by (metis \<open>a \<in> dom\<close> add.right_inverse ax1 gyro_left_cancel' gyro_rigth_inv scale_1 scale_closed scale_distrib)
        qed
     ultimately have "(fi_iso.fi_inv dom \<ominus> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)) a =
         ?gyr_inv a"
       by argo
    }
    then have "\<forall>a\<in>dom. (fi_iso.fi_inv dom \<ominus> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)) a =
         ?gyr_inv a"
      by blast
    then have "\<forall>a.(\<not>(a\<in>dom) \<longrightarrow> (fi_iso.fi_inv dom \<ominus> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)) a
             = undefined)"
      using \<open>\<And>b. fi_iso.fi_inv dom \<ominus> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b = (if b \<in> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom then if \<ominus> (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b) \<in> dom then (1 / \<alpha>) \<otimes> \<ominus> (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b) else undefined else undefined)\<close> calculation(2) by presburger
      
    then have "\<forall>a. (\<not>(a\<in>dom) \<longrightarrow> ?gyr_inv a  = undefined)"  

      using assms(2) by presburger
    then show ?thesis 
      using \<open>\<forall>a. a \<notin> dom \<longrightarrow> fi_iso.fi_inv dom \<ominus> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a = undefined\<close> \<open>\<forall>a\<in>dom. fi_iso.fi_inv dom \<ominus> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a = (if a \<in> dom then \<ominus> a else undefined)\<close> by fastforce
  qed
  moreover have "fi_iso.fi_gyr dom gyr (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) =
    ?gyr_gyr"
    using fi_iso.fi_gyr_def[OF **]
  proof-
    {
      fix a b c
      assume "a\<in>dom\<and>b\<in>dom\<and>c\<in>dom"
      have " fi_iso.fi_gyr dom gyr (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a b c=
       (1 / \<alpha>) \<otimes>
             gyr (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a)
              (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b)
              (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) c) "
        by (smt (z3) \<open>\<And>c b a. fi_iso.fi_gyr dom gyr (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a b c = (if a \<in> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom \<and> b \<in> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom \<and> c \<in> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom then if gyr (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a) (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b) (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) c) \<in> dom then (1 / \<alpha>) \<otimes> gyr (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a) (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b) (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) c) else undefined else undefined)\<close> \<open>a \<in> dom \<and> b \<in> dom \<and> c \<in> dom\<close> calculation(2) gyrogroup_axioms gyrogroup_axioms_def gyrogroup_def inv_into_into)
      
      moreover have "(1 / \<alpha>) \<otimes>
             gyr (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a)
              (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b)
              (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) c) =
       (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c))"
        by (simp add: \<open>\<forall>x\<in>dom. inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) x = (if x \<in> dom then \<alpha> \<otimes> x else undefined)\<close> \<open>a \<in> dom \<and> b \<in> dom \<and> c \<in> dom\<close>)
      moreover have " ?gyr_gyr a b c =  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c))"
        by (simp add: \<open>a \<in> dom \<and> b \<in> dom \<and> c \<in> dom\<close>)
      ultimately have "fi_iso.fi_gyr dom gyr (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a b c = ?gyr_gyr a b c"
        by argo
    }
    moreover have "\<forall>a\<in>dom.\<forall>b\<in>dom.\<forall>c\<in>dom. (
  fi_iso.fi_gyr dom gyr (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a b c = ?gyr_gyr a b c)"
      using calculation by blast
    ultimately show ?thesis 
      using \<open>(\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom = dom\<close> \<open>\<And>c b a. fi_iso.fi_gyr dom gyr (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a b c = (if a \<in> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom \<and> b \<in> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom \<and> c \<in> (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) ` dom then if gyr (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a) (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b) (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) c) \<in> dom then (1 / \<alpha>) \<otimes> gyr (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) a) (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) b) (inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) c) else undefined else undefined)\<close> by fastforce
  qed
  moreover have "(fi_iso.fi_scale dom (\<otimes>) (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined)) = ?gyr_scale"
    using fi_iso.fi_scale_def[OF **]
    using \<open>\<forall>x\<in>dom. inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) x = (if x \<in> dom then \<alpha> \<otimes> x else undefined)\<close> calculation(1) scale_closed 

    using calculation(2) by fastforce
  
  moreover have "  (fi_iso2.fi_norm dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) norm') =
   ?gyr_norm "
       using fi_iso2.fi_norm_def[OF *]

       using \<open>\<forall>x\<in>dom. inv_into dom (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) x = (if x \<in> dom then \<alpha> \<otimes> x else undefined)\<close> \<open>bij_betw (\<lambda>x. if x \<in> dom then (1 / \<alpha>) \<otimes> x else undefined) dom dom\<close> bij_betw_imp_surj_on by fastforce
     
     ultimately show ?thesis 
        using  fi_iso2.normed_gyrolin_I[of  dom gyrozero gyroplus gyroinv gyr scale ?fi norm' f, OF *]
        by argo
    qed
    moreover have NGS: "normed_gyrolinear_space dom gyrozero gyroplus gyroinv gyr scale norm' f"
      using normed_gyrolinear_space_axioms by blast
  moreover have ngs_main_help1: "(\<lambda>x. if x \<in>dom then (inv_into (norm'`dom) f) (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined)

   = (\<lambda>x. if x \<in> dom then norm' (\<alpha> \<otimes> x) else undefined)"
   
  proof-
    {
      fix x
      assume "x\<in>dom"
      have "(\<lambda>x. if x \<in>dom then inv f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined)x
      = inv f (\<bar>\<alpha>\<bar> * f (norm' x))"
        using \<open>x \<in> dom\<close> by presburger
      moreover have "(\<lambda>x. if x \<in> dom then norm' (\<alpha> \<otimes> x) else undefined)x = norm' (\<alpha> \<otimes> x)"
        using \<open>x \<in> dom\<close> by presburger
      moreover have " f(norm' (\<alpha> \<otimes> x)) = \<bar>\<alpha>\<bar> * f (norm' x)"
        by (smt (verit, ccfv_threshold) \<open>x \<in> dom\<close> normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def)
      moreover have "(inv_into (norm'`dom) f ) (f (norm' (\<alpha> \<otimes> x))) = norm' (\<alpha> \<otimes> x)"
        by (meson \<open>x \<in> dom\<close> bij_betw_def f_bij image_eqI inv_into_f_eq scale_closed)
      moreover have "(inv_into (norm'`dom) f) (\<bar>\<alpha>\<bar> * f (norm' x)) = norm' (\<alpha> \<otimes> x)"
        using calculation(3) calculation(4) by presburger
      ultimately have "(\<lambda>x. if x \<in>dom then (inv_into (norm'`dom) f) (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined)x
   = (\<lambda>x. if x \<in> dom then norm' (\<alpha> \<otimes> x) else undefined)x"
        by presburger
    }
    moreover have "\<forall>y\<in>dom. ((\<lambda>x. if x \<in>dom then (inv_into (norm'`dom) f) (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined)y

   = (\<lambda>x. if x \<in> dom then norm' (\<alpha> \<otimes> x) else undefined)y)"
      using calculation by blast
    ultimately show ?thesis 
      by meson
  qed
  moreover have  ngs_main_help2: "(\<lambda>r a. if a \<in> dom then (1 / \<alpha>) \<otimes> (r \<otimes> (\<alpha> \<otimes> a)) else undefined)
  = (\<lambda>r a. if a \<in> dom then  (r \<otimes> a) else undefined)"
  proof-
    {
      fix r a
      assume "a\<in>dom"
      moreover have "(\<lambda>r a. if a \<in> dom then (1 / \<alpha>) \<otimes> (r \<otimes> (\<alpha> \<otimes> a)) else undefined) r a =
          (1 / \<alpha>) \<otimes> (r \<otimes> (\<alpha> \<otimes> a))"
        using calculation by presburger
      moreover have " (1 / \<alpha>) \<otimes> (r \<otimes> (\<alpha> \<otimes> a)) = r\<otimes>a"
        by (metis assms(1) calculation(1) mult.commute nonzero_eq_divide_eq scale_1 scale_assoc times_divide_eq_left)
      moreover have "(\<lambda>r a. if a \<in> dom then  (r \<otimes> a) else undefined) r a = r\<otimes>a"
        using calculation(1) by auto
      ultimately have "(\<lambda>r a. if a \<in> dom then (1 / \<alpha>) \<otimes> (r \<otimes> (\<alpha> \<otimes> a)) else undefined) r a
  = (\<lambda>r a. if a \<in> dom then  (r \<otimes> a) else undefined) r a"
        by presburger
    }
    moreover have "\<forall>r.\<forall>a\<in>dom. (\<lambda>r a. if a \<in> dom then (1 / \<alpha>) \<otimes> (r \<otimes> (\<alpha> \<otimes> a)) else undefined) r a
  = (\<lambda>r a. if a \<in> dom then  (r \<otimes> a) else undefined) r a"
      using calculation by blast
    ultimately show ?thesis 
      by fastforce
  qed
  ultimately show ?thesis 
    using NGS_main ngs_main_help1 ngs_main_help2 
    by argo
qed
(*
lemma proposition_3_4:
  fixes h::"real\<Rightarrow>real"
  assumes "h 0 = 0" "inj_on h {x::real. x\<ge>0}" "\<forall>x. (x\<ge>0\<longrightarrow>(h x)\<ge>0)" 
    "\<forall>x. \<forall>y. ((x > y \<and>  y\<ge>0) \<longrightarrow> (h x) > (h y))"
  shows "normed_gyrolinear_space dom gyrozero gyroplus gyroinv gyr scale
         (h \<circ> norm') (f \<circ> (inv_into ( norm' ` dom) h))"
*)

(*"normed_gyrolinear_space dom gyrozero \<alpha>_plus (\<lambda>x. (if x \<in>dom then gyroinv x else undefined))
 (\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)
 )  (\<lambda>r a. if a \<in> dom then r \<otimes> a else undefined)
(\<lambda>x. if x \<in> dom then norm' x
          else undefined) (\<lambda>a. if a\<in>((\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
          else undefined)) `dom then (f a) else undefined)"*)

lemma proposition_3_11:
  fixes \<alpha>::real
  fixes \<alpha>_plus::"'a\<Rightarrow>'a \<Rightarrow>'a"
  assumes "\<alpha> \<noteq> 0"
  "\<forall>a.\<forall>b. \<alpha>_plus a b =  (if (a\<in>dom \<and> b\<in>dom) then scale (1/\<alpha>) (gyroplus (scale \<alpha> a) (scale \<alpha> b))
    else undefined)"
shows "normed_gyrolinear_space dom gyrozero \<alpha>_plus (\<lambda>x. (if x \<in>dom then gyroinv x else undefined))
 (\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)
 )  (\<lambda>r a. if a \<in> dom then r \<otimes> a else undefined)
(\<lambda>x. if x \<in> dom then norm' x
          else undefined) (\<lambda>x. if x \<in> norm' ` dom then \<bar>\<alpha>\<bar> * f x else undefined)"
proof-
  let ?h = "\<lambda>a. (if (a\<in> norm'`dom) then (inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f a))
    else undefined)"
  let ?norm'' = "(\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
          else undefined)"
  have ngs:"normed_gyrolinear_space dom gyrozero \<alpha>_plus (\<lambda>x. (if x \<in>dom then gyroinv x else undefined))
 (\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)
 )  (\<lambda>r a. if a \<in> dom then r \<otimes> a else undefined)
 ?norm'' f"
    using assms(1) assms(2) proposition_3_10 by blast
  moreover have H1:"?h 0 = 0"
  proof-
    have "gyrozero \<in> dom"
      by (simp add: zero_in_dom)
    moreover have "0\<in> (norm'`dom)"
      by (smt (verit) image_iff normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def zero_in_dom)
    moreover have "?h 0 = (inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f 0))"
      using calculation(2) by presburger
    ultimately show ?thesis
      using bij_betw_inv_into_left gyro_left_id mult_cancel_right1 normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def scale_1 scale_distrib
      by (smt (verit))
  qed
  moreover have H2:"inj_on ?h (norm'` dom) "
  proof-
    {
      fix a b
      assume *: "a\<in>norm'`dom \<and> b\<in>norm'`dom \<and> ?h a = ?h b"
      have " ?h a  = (inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f a))"
        using "*" by presburger
      moreover have "?h b = (inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f b))"
        using "*" by presburger
      moreover have " (inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f a)) =  (inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f b))"
        using "*" by presburger
      moreover have "f ((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f a))) = f ((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f b)))"
        using calculation(3) by presburger
      moreover have "f ((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f a))) =  (\<bar>1/\<alpha>\<bar>*(f a))"
        by (metis "*" abs_ge_zero bij_betw_inv_into_right f_bij f_pos mem_Collect_eq split_mult_pos_le)
      moreover have "f ((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f b))) =  (\<bar>1/\<alpha>\<bar>*(f b))"
        by (metis "*" abs_ge_zero bij_betw_inv_into_right f_bij f_pos mem_Collect_eq split_mult_pos_le)
      moreover have " (\<bar>1/\<alpha>\<bar>*(f a)) =  (\<bar>1/\<alpha>\<bar>*(f b))"
        using calculation(3) calculation(5) calculation(6) by presburger
      ultimately have "a=b"
        by (smt (verit, ccfv_threshold) "*" assms(1) f_mon mult_cancel_left one_divide_eq_0_iff)
    }
    moreover have "\<forall>a\<in>(norm'`dom).\<forall>b\<in>(norm'`dom). ((?h a) = (?h b) \<longrightarrow> a= b)"
      using calculation by blast
    ultimately show ?thesis 
      using inj_on_def by blast
  qed
  moreover have H3:"\<forall>x\<in>(norm'`dom). ((?h x)\<ge>0)"
    by (smt (z3) bij_betw_def f_bij image_iff inv_into_into mem_Collect_eq norm_pos split_mult_pos_le)
  moreover have H4:"\<forall>x\<in>(norm'`dom). \<forall>y\<in>(norm'`dom). (x > y \<longrightarrow> (?h x) > (?h y))"
  proof-
    {fix x y
    assume *:"x\<in>(norm'`dom) \<and> y\<in> (norm'`dom) \<and> x>y"
    have "?h x = ((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f x)))"
      using \<open>x \<in> norm' ` dom \<and> y \<in> norm' ` dom \<and> y < x\<close> by presburger
    moreover have "?h y=((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f y)))"
      using \<open>x \<in> norm' ` dom \<and> y \<in> norm' ` dom \<and> y < x\<close> by presburger
    moreover have "(\<bar>1/\<alpha>\<bar>*(f x)) > (\<bar>1/\<alpha>\<bar>*(f y))"
      by (meson \<open>x \<in> norm' ` dom \<and> y \<in> norm' ` dom \<and> y < x\<close> abs_le_zero_iff assms(1) f_mon mult_less_cancel_left one_divide_eq_0_iff)
    moreover have " ((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f x))) >  ((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f y)))"
    proof(rule ccontr)
      assume "\<not>( ((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f x))) >  ((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f y))))"
      then have " ((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f x))) \<le>  ((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f y)))"
        using linorder_not_less by blast
      let ?left = "((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f x)))"
      let ?right = "((inv_into (norm'`dom) f) (\<bar>1/\<alpha>\<bar>*(f y)))"
      have "?left < ?right \<or> ?left = ?right"
        using \<open>inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f x) \<le> inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f y)\<close> by argo
      moreover {
        assume "?left < ?right"
        then have "f ?left < f ?right"
          by (metis \<open>x \<in> norm' ` dom \<and> y \<in> norm' ` dom \<and> y < x\<close> abs_ge_zero bij_betw_imp_surj_on f_bij f_mon f_pos inv_into_into mem_Collect_eq split_mult_pos_le)
        moreover have "f ?left =  (\<bar>1/\<alpha>\<bar>*(f x))"
        by (metis "*" abs_ge_zero bij_betw_inv_into_right f_bij f_pos mem_Collect_eq split_mult_pos_le)
        moreover have "f ?right =  (\<bar>1/\<alpha>\<bar>*(f y))"
        by (metis "*" abs_ge_zero bij_betw_inv_into_right f_bij f_pos mem_Collect_eq split_mult_pos_le)
      moreover have " (\<bar>1/\<alpha>\<bar>*(f x)) <  (\<bar>1/\<alpha>\<bar>*(f y))"
        using calculation(1) calculation(2) calculation(3) by linarith
      moreover have "x<y"
        using \<open>\<bar>1 / \<alpha>\<bar> * f y < \<bar>1 / \<alpha>\<bar> * f x\<close> calculation(4) by argo
      ultimately have False
        using \<open>\<bar>1 / \<alpha>\<bar> * f y < \<bar>1 / \<alpha>\<bar> * f x\<close> by argo
    }
      moreover {
        assume "?left = ?right"
        then have "f ?left = f ?right"
          by presburger
        moreover have "f ?left =  (\<bar>1/\<alpha>\<bar>*(f x))"
        by (metis "*" abs_ge_zero bij_betw_inv_into_right f_bij f_pos mem_Collect_eq split_mult_pos_le)
        moreover have "f ?right =  (\<bar>1/\<alpha>\<bar>*(f y))"
        by (metis "*" abs_ge_zero bij_betw_inv_into_right f_bij f_pos mem_Collect_eq split_mult_pos_le)
      moreover have " (\<bar>1/\<alpha>\<bar>*(f x)) = (\<bar>1/\<alpha>\<bar>*(f y))"
        using calculation(1) calculation(2) calculation(3) by linarith
      moreover have "x=y"
        using \<open>\<bar>1 / \<alpha>\<bar> * f y < \<bar>1 / \<alpha>\<bar> * f x\<close> calculation(4) by argo
      ultimately have False
        using \<open>\<bar>1 / \<alpha>\<bar> * f y < \<bar>1 / \<alpha>\<bar> * f x\<close> by argo
    }
    ultimately show False by blast
  qed
  ultimately have "?h x > ?h y"
    by presburger
}
  then show ?thesis 
    by blast
qed

  moreover have "norm' ` dom \<subseteq> (\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
          else undefined) `
    dom"
  proof
    fix x
    assume "x\<in>norm'`dom"
    show "x\<in>(\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
          else undefined) `
    dom"
    proof-
      have "\<forall>x\<in>dom.   (\<bar>\<alpha>\<bar> * f (norm' x)) = f(norm' (\<alpha> \<otimes>x))"
        by (smt (verit, best) normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def)
      moreover have "\<forall>x\<in>dom. inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) = norm' (\<alpha> \<otimes> x)"
        by (metis bij_betw_def calculation f_bij image_eqI inv_into_f_eq scale_closed)
      moreover obtain "y" where "y\<in>dom \<and> x=norm' y"
        using \<open>x \<in> norm' ` dom\<close> by blast
      moreover obtain "y'" where "y'\<in>dom \<and> y = \<alpha> \<otimes> y'"
        by (metis assms(1) calculation(3) mult.commute nonzero_eq_divide_eq scale_1 scale_assoc scale_closed)
      moreover have "norm' (\<alpha>\<otimes>y') =  inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' y'))"
        by (simp add: calculation(2) calculation(4))
      ultimately show ?thesis 
        by force
    qed
  qed
  moreover have  " (\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
          else undefined) `
    dom
    \<subseteq> norm' ` dom"
    proof-
      have "\<And>x. x \<in> (\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                  else undefined) `
             dom \<Longrightarrow>
         x \<in> norm' ` dom"
      proof-
        fix x 
        assume "x\<in>(\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                  else undefined) `
             dom"
        obtain "y" where "y\<in>dom \<and> x = inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' y))"
          using \<open>x \<in> (\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined) ` dom\<close> by auto
        then show "x\<in> norm'`dom"
          by (smt (verit, del_insts) bij_betw_def f_bij image_eqI inv_into_into mem_Collect_eq split_mult_pos_le)
      qed
      then show ?thesis 
        by blast 
    qed
    moreover have "(\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
          else undefined) `
    dom
    = norm' ` dom "
      using calculation(6) calculation(7) by force
    
    moreover have "normed_gyrolinear_space dom gyrozero \<alpha>_plus (\<lambda>x. (if x \<in>dom then gyroinv x else undefined))
 (\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)
 )  (\<lambda>r a. if a \<in> dom then r \<otimes> a else undefined)
(\<lambda>x. if x\<in>dom then (?h \<circ> ?norm'') x else undefined) 
(\<lambda>x. if x\<in>(?h`?norm''`dom) then (f \<circ> inv_into (?norm''`dom) ?h)x else undefined)"
      using normed_gyrolinear_space.proposition_3_4[OF ngs, of ?h] H1 H2 H3 H4
      by (smt (z3) calculation(8))
  
    moreover  have "(\<lambda>x. if x \<in> dom
           then ((\<lambda>a. if a \<in> norm' ` dom
                       then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                       else undefined) \<circ>
                 (\<lambda>x. if x \<in> dom
                       then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                       else undefined))
                 x
           else undefined) =(\<lambda>x. if x \<in> dom then norm' x else undefined)"
    proof-
      {
      fix x 
      assume "x\<in>dom"
      have "((\<lambda>a. if a \<in> norm' ` dom
                       then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                       else undefined) \<circ>
                 (\<lambda>x. if x \<in> dom
                       then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                       else undefined))
                 x =  inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f (inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))))"
        using \<open>x \<in> dom\<close> calculation(7) by auto
      moreover have " inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f (inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)))) = 
inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> *  (\<bar>\<alpha>\<bar> * f (norm' x)))"
        by (smt (verit, ccfv_SIG) \<open>x \<in> dom\<close> bij_betw_imp_surj_on f_bij f_inv_into_f image_eqI mem_Collect_eq mult_nonneg_nonneg)
      moreover have "inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> *  (\<bar>\<alpha>\<bar> * f (norm' x))) = inv_into (norm' ` dom) f ( f (norm' x))"
        by (simp add: assms(1))
      moreover have " inv_into (norm' ` dom) f ( f (norm' x)) = norm' x"
        by (meson \<open>x \<in> dom\<close> bij_betw_imp_inj_on f_bij image_eqI inv_into_f_eq)
      ultimately have "((\<lambda>a. if a \<in> norm' ` dom
                       then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                       else undefined) \<circ>
                 (\<lambda>x. if x \<in> dom
                       then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                       else undefined))
                 x = norm' x"
        by presburger
    } then show ?thesis
      by meson
  qed
  moreover have "(\<lambda>x. if x \<in> (\<lambda>a. if a \<in> norm' ` dom
                       then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                       else undefined) `
                  norm' ` dom
           then (f \<circ>
                 inv_into (norm' ` dom)
                  (\<lambda>a. if a \<in> norm' ` dom
                        then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                        else undefined))
                 x
           else undefined) = (\<lambda>x. if x\<in> ?norm''`dom then (f x) * \<bar>\<alpha>\<bar> else undefined)" 
  proof-
    {
      fix x 
      assume " x \<in> (\<lambda>a. if a \<in> norm' ` dom
                       then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                       else undefined) `
                  norm' ` dom"
      obtain "y" where "y\<in>norm'`dom \<and> x = inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f y)"
        using \<open>x \<in> (\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined) ` norm' ` dom\<close> by auto
      moreover have "x\<in>?norm''`dom"
        by (metis \<open>(\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined) ` dom = norm' ` dom\<close> abs_ge_zero bij_betw_imp_surj_on calculation f_bij f_pos inv_into_into mem_Collect_eq split_mult_pos_le)
        
      moreover have "(f \<circ>
                 inv_into (norm' ` dom)
                  (\<lambda>a. if a \<in> norm' ` dom
                        then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                        else undefined))
                 x = (f \<circ>
                 inv_into (norm' ` dom)
                  (\<lambda>a. if a \<in> norm' ` dom
                        then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                        else undefined))
                 (inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f y))"
        using calculation by force
      moreover have " (f \<circ>
                 inv_into (norm' ` dom)
                  (\<lambda>a. if a \<in> norm' ` dom
                        then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                        else undefined))
                 (inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f y)) = f y"
        using \<open>inj_on (\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined) (norm' ` dom)\<close> calculation(1) inv_into_f_eq by fastforce
      moreover have " y = inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f x)"
        by (smt (verit, del_insts) \<open>(\<lambda>x. if x \<in> dom then ((\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined) \<circ> (\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined)) x else undefined) = (\<lambda>x. if x \<in> dom then norm' x else undefined)\<close> \<open>(\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined) ` dom = norm' ` dom\<close> calculation(1) comp_apply f_inv_into_f inv_into_into)
      moreover have "(\<lambda>x. if x\<in> ?norm''`dom then (f x) * \<bar>\<alpha>\<bar> else undefined)x = f y"
        by (smt (verit, ccfv_SIG) bij_betw_imp_surj_on calculation(1) calculation(2) calculation(5) f_bij f_inv_into_f f_pos mem_Collect_eq mult.commute split_mult_pos_le)
      ultimately have "(\<lambda>x. if x \<in> (\<lambda>a. if a \<in> norm' ` dom
                       then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                       else undefined) `
                  norm' ` dom
           then (f \<circ>
                 inv_into (norm' ` dom)
                  (\<lambda>a. if a \<in> norm' ` dom
                        then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                        else undefined))
                 x
           else undefined)x = (\<lambda>x. if x\<in> ?norm''`dom then (f x) * \<bar>\<alpha>\<bar> else undefined)x"
        using \<open>x \<in> (\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined) ` norm' ` dom\<close> by presburger
    }
    moreover have "\<forall>x. (\<not>(x
  \<in> (\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
          else undefined) `
     norm' ` dom)  \<longrightarrow> \<not>(x\<in> ?norm''`dom))"
      by (metis (no_types, lifting) \<open>(\<lambda>x. if x \<in> dom then ((\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined) \<circ> (\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined)) x else undefined) = (\<lambda>x. if x \<in> dom then norm' x else undefined)\<close> \<open>(\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined) ` dom = norm' ` dom\<close> f_inv_into_f image_comp image_eqI inv_into_into)
    ultimately show ?thesis
      by meson
  qed
  moreover have " (\<lambda>x. if x \<in> (\<lambda>a. if a \<in> norm' ` dom
                       then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                       else undefined) `
                  (\<lambda>x. if x \<in> dom
                        then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                        else undefined) `
                  dom
           then (f \<circ>
                 inv_into
                  ((\<lambda>x. if x \<in> dom
                         then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                         else undefined) `
                   dom)
                  (\<lambda>a. if a \<in> norm' ` dom
                        then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                        else undefined))
                 x
           else undefined) = (\<lambda>x. if x\<in>norm'`dom then \<bar>\<alpha>\<bar>*f x else undefined)"
  proof-
    {
      fix x 
      assume "x \<in> (\<lambda>a. if a \<in> norm' ` dom
                       then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                       else undefined) `
                  (\<lambda>x. if x \<in> dom
                        then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                        else undefined) `
                  dom"
      then have "x\<in>norm'`dom"
        by (smt (verit, ccfv_threshold) bij_betw_def calculation(8) comp_def f_bij image_iff inv_into_f_f inv_into_into mem_Collect_eq split_mult_pos_le)
      moreover obtain "y" where "y\<in>dom \<and> x = norm' y"
        using calculation by blast
      moreover have "(inv_into
                  ((\<lambda>x. if x \<in> dom
                         then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                         else undefined) `
                   dom)
                  (\<lambda>a. if a \<in> norm' ` dom
                        then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                        else undefined))
                 x = ?norm'' y"
        by (smt (verit, del_insts) \<open>(\<lambda>x. if x \<in> (\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined) ` norm' ` dom then (f \<circ> inv_into (norm' ` dom) (\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined)) x else undefined) = (\<lambda>x. if x \<in> (\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined) ` dom then f x * \<bar>\<alpha>\<bar> else undefined)\<close> \<open>(\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined) ` dom = norm' ` dom\<close> \<open>x \<in> (\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined) ` (\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined) ` dom\<close> bij_betw_inv_into_left calculation(1) calculation(2) comp_apply f_bij inv_into_into mult.commute)
      moreover have " (f \<circ>
                 inv_into
                  ((\<lambda>x. if x \<in> dom
                         then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                         else undefined) `
                   dom)
                  (\<lambda>a. if a \<in> norm' ` dom
                        then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                        else undefined))
                 x = (f \<circ> ?norm'') y"
        using calculation(3) by auto
      moreover have "(f \<circ> ?norm'') y = \<bar>\<alpha>\<bar> * (f x)"
        by (metis (no_types, lifting) \<open>(\<lambda>x. if x \<in> (\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined) ` norm' ` dom then (f \<circ> inv_into (norm' ` dom) (\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined)) x else undefined) = (\<lambda>x. if x \<in> (\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined) ` dom then f x * \<bar>\<alpha>\<bar> else undefined)\<close> \<open>(\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined) ` dom = norm' ` dom\<close> \<open>x \<in> (\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined) ` (\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined) ` dom\<close> calculation(1) calculation(4) mult.commute)
      ultimately have "(\<lambda>x. if x \<in> (\<lambda>a. if a \<in> norm' ` dom
                       then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                       else undefined) `
                  (\<lambda>x. if x \<in> dom
                        then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                        else undefined) `
                  dom
           then (f \<circ>
                 inv_into
                  ((\<lambda>x. if x \<in> dom
                         then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                         else undefined) `
                   dom)
                  (\<lambda>a. if a \<in> norm' ` dom
                        then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                        else undefined))
                 x
           else undefined) x= (\<lambda>x. if x\<in>norm'`dom then \<bar>\<alpha>\<bar>*f x else undefined)x"
        by (metis \<open>x \<in> (\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined) ` (\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined) ` dom\<close>)
    }
    moreover have "\<forall>x. (\<not>x \<in> (\<lambda>a. if a \<in> norm' ` dom
                       then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a)
                       else undefined) `
                  (\<lambda>x. if x \<in> dom
                        then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x))
                        else undefined) `
                  dom \<longrightarrow> \<not>x\<in>norm'`dom)"
      by (metis (no_types, lifting) \<open>(\<lambda>x. if x \<in> dom then ((\<lambda>a. if a \<in> norm' ` dom then inv_into (norm' ` dom) f (\<bar>1 / \<alpha>\<bar> * f a) else undefined) \<circ> (\<lambda>x. if x \<in> dom then inv_into (norm' ` dom) f (\<bar>\<alpha>\<bar> * f (norm' x)) else undefined)) x else undefined) = (\<lambda>x. if x \<in> dom then norm' x else undefined)\<close> image_comp image_iff)
    ultimately show ?thesis 
      by meson
  qed
  (*moreover have " (\<lambda>x. if x\<in>norm'`dom then \<bar>\<alpha>\<bar>*f x else undefined) =  (\<lambda>x. if x\<in>norm'`dom then f x else undefined)"
  proof
    {
      fix x 
      assume "x\<in>norm'`dom"
      then obtain "y" where "y\<in>dom \<and> x= norm' y"
        by blast
      moreover have "\<bar>\<alpha>\<bar>*f x = f (norm' (\<alpha> \<otimes> y))"
        by (smt (verit, ccfv_threshold) calculation normed_gyrolinear_space.axioms(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_axioms_def)
      
    }
qed*)
  ultimately show ?thesis 
    by argo
qed



end

context normed_gyrolinear_space''
begin
lemma is_normed_gyrolinear_space:
  assumes "\<exists>x. (x\<in>norms_all \<and> x\<noteq>0)
  \<and> (bij_betw f norms {x::real. x\<ge>0})
\<and>  (\<forall>y::real. \<forall>z::real. (( y\<in> norms \<and>
z\<in>  norms \<and> y>z)\<longrightarrow> (f y) > (f z)))
  \<and> (\<forall>x\<in>dom. \<forall>y\<in>dom. f(norm' (x \<oplus> y)) \<le> (f (norm' x)) + (f (norm' y)))
\<and> (\<forall>r::real. (\<forall>x\<in>dom. (f (norm' (r \<otimes> x)) = \<bar>r\<bar> * (f (norm' x)))))"
  shows "normed_gyrolinear_space dom gyrozero gyroplus gyroinv gyr scale norm' f"
proof
  show " \<forall>a\<in>dom. 0 \<le> norm' a"
    using norm_pos by blast
next
  show " \<forall>y. y \<in> norm' ` dom \<longrightarrow> 0 \<le> f y"
    by (metis assms bij_betw_iff_bijections mem_Collect_eq norms_def)
next
  show "bij_betw f (norm' ` dom) {x. 0 \<le> x}"
    by (metis assms norms_def)
next
  show "\<forall>y z. y \<in> norm' ` dom \<and> z \<in> norm' ` dom \<and> z < y \<longrightarrow> f z < f y"
    using assms norms_def by blast
next
  show " \<forall>x\<in>dom. \<forall>y\<in>dom. f (norm' (x \<oplus> y)) \<le> f (norm' x) + f (norm' y)"
    using assms by blast
next
  show " \<forall>r. \<forall>x\<in>dom. f (norm' (r \<otimes> x)) = \<bar>r\<bar> * f (norm' x)"
    using assms by blast
next
  show " \<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>x\<in>dom. norm' (gyr u v x) = norm' x"
    using norm_gyr by fastforce
next
  show "\<forall>x\<in>dom. (norm' x = 0) = (x = 0\<^sub>g) "
    using local.norm_zero by blast
qed

end



(*
context gyrovector_space
begin
end*)

locale gyro_iso = normed_gyrolinear_space +
  fixes fi::"'a\<Rightarrow>'b::real_inner" 
  assumes norm'_d: "\<forall>a\<in>dom. norm' a = (\<lambda>x. (norm (fi x))) a"
begin 


definition f'::"(real\<Rightarrow>real)" where
 "f'= (\<lambda>x. (if x \<in> (norm'`dom) then (f x) else 
(if x\<in> ( (\<lambda>x. - 1 * norm' x)`dom) then (-f (-x)) else undefined)))"


definition oplus'::"real \<Rightarrow> real \<Rightarrow> real" (infixl " \<oplus>\<^sub>f" 105)
  where "a \<oplus>\<^sub>f b = (if (a\<in>norms_all \<and> b\<in>norms_all) then (inv_into norms_all f') ((f' a) + (f' b))
else undefined)"


definition smult'::"real \<Rightarrow> real \<Rightarrow> real" (infixl "\<otimes>\<^sub>f" 105)
  where "r \<otimes>\<^sub>f a = (if (a\<in>norms_all) then (inv_into norms_all f') (r * (f' a))
else undefined)"

lemma f''_bij:
  shows "bij_betw f' norms_all UNIV"
  using norms_all_def norms_def norms_neg_def
  normed_gyrolinear_space'.f'_bij f'_def
  using is_normed_gyrolinear_space' by fastforce




lemma space_otimes'_otimes':
  fixes \<alpha>::real
  assumes  "\<alpha> \<noteq> 0" "a\<in>dom" "b\<in>dom"
 "ggv_space dom gyrozero gyroplus gyroinv gyr scale oplus' smult' fi 0"
  shows "smult' (1/\<alpha>) (smult'  \<alpha> (oplus' (norm' a) (norm' b)))
  = oplus' (norm' a) (norm' b)" 
  by (smt (verit, ccfv_SIG) assms(1) bij_betw_imp_surj_on bij_betw_inv_into bij_betw_inv_into_left f''_bij mult_cancel_right2 nonzero_mult_div_cancel_left oplus'_def rangeI range_mult smult'_def times_divide_eq_left)

lemma space_otimes'_mon:
  assumes "\<alpha> > 0" "a\<le>b" "a\<in>norms_all" 
  "b\<in>norms_all" 
  shows "smult' \<alpha> a \<le> smult' \<alpha> b"
proof-
  have "smult' \<alpha> a = (inv_into norms_all f') (\<alpha> * (f' a))"
    by (simp add: assms(3) smult'_def)
  moreover have "smult' \<alpha> b = (inv_into norms_all f') (\<alpha> * (f' b))"
    using assms(4) smult'_def by force
  moreover have "f' a \<le> f' b"
    by (smt (verit, ccfv_SIG) assms(2) assms(3) assms(4) f'_def is_normed_gyrolinear_space' normed_gyrolinear_space'.f'_mon normed_gyrolinear_space.norms_neg_def normed_gyrolinear_space_axioms norms_all_def norms_def)
  moreover have "\<alpha> * (f' a) \<le> \<alpha> * (f' b)"
    using assms(1) calculation(3) by auto
  moreover have " (inv_into norms_all f') (\<alpha> * (f' a)) \<le>  (inv_into norms_all f') (\<alpha> * (f' b))"
    by (smt (verit, best) f''_bij assms(1) bij_betw_def calculation(4) f_inv_into_f gyro_iso.f'_def gyro_iso_axioms inv_into_into normed_gyrolinear_space'.f'_mon normed_gyrolinear_space.is_normed_gyrolinear_space' normed_gyrolinear_space.norms_neg_def normed_gyrolinear_space_axioms norms_all_def norms_def rangeI range_mult)
  ultimately show ?thesis 
    by linarith
qed

lemma space_otimes'_mon2:
  assumes "\<alpha> > 0" "a\<le>b" "a\<in>norms_all" 
  "b\<in>norms_all" 
shows "smult' (1/\<alpha>) a \<le> smult' (1/\<alpha>) b"
  by (simp add: assms(1) assms(2) assms(3) assms(4) space_otimes'_mon)
lemma oplus_smult_con1:
 fixes \<alpha>::real
  fixes \<alpha>_plus::"'a \<Rightarrow> 'a \<Rightarrow>'a" 
  assumes "ggv_space dom gyrozero gyroplus gyroinv gyr scale oplus' smult' fi 0"
 "\<alpha> > 0" "a\<in>dom" "b\<in>dom"
 "\<forall>a.\<forall>b. \<alpha>_plus a b =  (if (a\<in>dom \<and> b\<in>dom) then scale (1/\<alpha>) (gyroplus (scale \<alpha> a) (scale \<alpha> b))
    else undefined)"
shows 
    "oplus' (smult' \<alpha> (norm' a)) (smult' \<alpha> (norm' b))
    = smult' \<alpha>  (oplus' (norm' a) (norm' b))
"    using oplus'_def smult'_def
        proof-
          have *:"(smult' \<alpha> (norm' a)) = inv_into norms_all f'  (\<alpha> * (f' (norm' a)))"
            by (simp add: assms(3) norms_all_def norms_def smult'_def)
          moreover have **:"(smult' \<alpha> (norm' b)) = inv_into norms_all f'  (\<alpha> * (f' (norm' b)))"
            by (simp add: assms(4) norms_all_def norms_def smult'_def)
          moreover have a1:"  (smult' \<alpha> (norm' a)) \<in> norms_all "
            using *
            by (metis UNIV_I bij_betw_imp_surj_on f''_bij inv_into_into)
           moreover have a2:"  (smult' \<alpha> (norm' b)) \<in> norms_all "
            using **
            by (metis UNIV_I bij_betw_imp_surj_on f''_bij inv_into_into)      
          moreover have  " oplus' (smult' \<alpha> (norm' a)) (smult' \<alpha> (norm' b))
= inv_into norms_all f' ( f'( (smult' \<alpha> (norm' a)))  + 
 f'( (smult' \<alpha> (norm' b))))"
            using oplus'_def
   a1 a2
            by auto
          moreover  have " oplus' (smult' \<alpha> (norm' a)) (smult' \<alpha> (norm' b))
= inv_into norms_all f' ( f'(( inv_into norms_all f')(\<alpha> * (f' (norm' a)))) + 
f'(( inv_into norms_all f')(\<alpha>* (f' (norm' b)))))"
            using "*" "**" calculation(5) by presburger
          moreover have " oplus' (smult' \<alpha> (norm' a)) (smult' \<alpha> (norm' b))
= inv_into norms_all f' (\<alpha> * (f' (norm' a)) +(\<alpha> * (f' (norm' b))))"
            using f''_bij bij_betw_inv_into_right calculation(6) by fastforce
          moreover have "oplus' (smult' \<alpha> (norm' a)) (smult' \<alpha> (norm' b))
= inv_into norms_all f' (\<alpha> * (f' (norm' a) + (f' (norm' b))))"
            using add_divide_distrib calculation(7)
            by argo
          moreover have "oplus' (smult' \<alpha> (norm' a)) (smult' \<alpha> (norm' b))
= inv_into norms_all f' (\<alpha> * f' ( (inv_into norms_all f') 
(f' (norm' a) + (f' (norm' b)))))"
            using f''_bij bij_betw_inv_into_right calculation(8) by fastforce
          moreover have "oplus' (smult' \<alpha> (norm' a)) (smult' \<alpha> (norm' b))
= inv_into norms_all f' (\<alpha> *  
(f' (norm' a) + (f' (norm' b))))"
            using calculation(8) by blast
          ultimately show ?thesis
            by (smt (verit, ccfv_SIG) Un_iff assms(3) assms(4) bij_betw_imp_surj_on bij_betw_inv_into f''_bij image_eqI norms_all_def norms_def oplus'_def rangeI smult'_def)
        qed
      



lemma  space_ax12: 
  fixes \<alpha>::real
  fixes \<alpha>_plus::"'a \<Rightarrow> 'a \<Rightarrow>'a"
  assumes "ggv_space dom gyrozero gyroplus gyroinv gyr scale oplus' smult' fi 0"
 "\<alpha> > 0"
  "\<forall>a.\<forall>b. \<alpha>_plus a b =  (if (a\<in>dom \<and> b\<in>dom) then scale (1/\<alpha>) (gyroplus (scale \<alpha> a) (scale \<alpha> b))
    else undefined)"
shows "\<forall>a\<in>dom. \<forall>b\<in>dom. norm (fi (\<alpha>_plus a b)) \<le> oplus' (norm (fi a)) (norm (fi b))"
proof
  fix a
  assume "a\<in>dom"
  show "\<forall>b\<in>dom. norm (fi (\<alpha>_plus a b)) \<le> oplus' (norm (fi a)) (norm (fi b))"
  proof
    fix b
    assume "b\<in>dom"
    show " norm (fi (\<alpha>_plus a b)) \<le> oplus' (norm (fi a)) (norm (fi b))" 
    proof-
      
      have "\<alpha>_plus a b =  scale (1/\<alpha>) (gyroplus (scale \<alpha> a) (scale \<alpha> b))"
        using \<open>a \<in> dom\<close> \<open>b \<in> dom\<close> assms(3) by presburger
      moreover have *:"(gyroplus (scale \<alpha> a) (scale \<alpha> b)) \<in> dom"
        by (simp add: \<open>a \<in> dom\<close> \<open>b \<in> dom\<close> gyroplus_closed scale_closed)
      moreover have A1:"norm' (\<alpha>_plus a b) = smult' (1 / \<alpha>) (norm' ((gyroplus (scale  \<alpha> a) (scale  \<alpha> b))))"
      proof-
        have "(\<alpha>_plus a b) \<in> dom"
          by (simp add: "*" calculation(1) scale_closed)
        moreover have "(gyroplus (scale  \<alpha> a) (scale  \<alpha> b)) \<in>dom"
          using "*" by blast
        ultimately show ?thesis 
          using  norm'_d assms(1) ggv_space_def
          ggv_space_axioms_def[of dom gyrozero gyroplus gyr scale oplus']
           using \<open>\<alpha>_plus a b = (1 / \<alpha>) \<otimes> (\<alpha> \<otimes> a \<oplus> \<alpha> \<otimes> b)\<close> assms(2) divide_nonneg_pos
           by (smt (verit) ggv_intro.norm_smult'_ggv)
          (*using  norm'_d
        

  ggv_space_def[of dom gyrozero gyroplus gyr scale oplus' smult' fi]
        using assms(1) gyrovector_space_def 
        using \<open>\<alpha>_plus a b = (1 / \<alpha>) \<otimes> (\<alpha> \<otimes> a \<oplus> \<alpha> \<otimes> b)\<close> assms(2) divide_nonneg_pos
        by (smt (verit, ccfv_threshold))*)
    qed
        moreover have "norm' ((gyroplus (scale \<alpha> a) (scale \<alpha> b))) \<le>
        oplus' (norm' (scale \<alpha> a)) (norm' (scale \<alpha> b))"
        proof-
          have "gyroplus (scale \<alpha> a) (scale \<alpha> b)\<in>dom"
            using "*" by force
          moreover have "scale \<alpha> b \<in> dom"
            using \<open>b \<in> dom\<close> scale_closed by blast
        moreover have "scale \<alpha> a \<in> dom"
            using \<open>a \<in> dom\<close> scale_closed by blast
          ultimately show ?thesis
        using  norm'_d
   ggv_space_axioms_def[of dom gyrozero gyroplus gyr scale oplus']
        \<open>a \<in> dom\<close> \<open>b \<in> dom\<close> assms(1) 
        by (simp add: ggv_space.norm_triangle_ineq_ggv)
    qed
     
      
        (*by (smt (verit, del_insts))*)
     moreover have " smult' (1/ \<alpha>) (oplus' (norm' (scale  \<alpha> a)) (norm' (scale \<alpha> b)))
        = oplus'  (norm' a)  (norm' b)"
      proof-
        have "(oplus' (norm' (scale \<alpha> a)) (norm' (scale \<alpha> b))) =
      oplus' (smult' \<alpha> (norm' a)) (smult' \<alpha> (norm' b))"
          using ggv_space_axioms_def[of dom gyrozero gyroplus gyr scale oplus' fi]
ggv_intro_axioms_def[of dom gyroplus scale oplus' smult' fi]
          using \<open>a \<in> dom\<close> \<open>b \<in> dom\<close> assms(1) assms(2) ggv_space_def norm'_d 
           ggv_intro.norm_smult'_ggv scale_closed
          by (smt (verit, del_insts))
      moreover have "oplus' (smult' \<alpha> (norm' a)) (smult' \<alpha> (norm' b))
    = smult' \<alpha>  (oplus' (norm' a) (norm' b))"
        using \<open>a \<in> dom\<close> \<open>b \<in> dom\<close> assms(1) assms(2) assms(3)  oplus_smult_con1 by blast
       moreover have " smult' (1/ \<alpha>)
     (oplus' (norm' (scale \<alpha> a)) (norm' (scale \<alpha> b))) =
smult' (1/ \<alpha>) ( smult' \<alpha> (oplus' (norm' a) (norm' b)))"
         by (simp add: calculation(1) calculation(2))
       ultimately show ?thesis 
        using ggv_space_axioms_def[of dom gyrozero gyroplus gyr scale oplus' fi]
        using \<open>a \<in> dom\<close> \<open>b \<in> dom\<close> space_otimes'_otimes' 
        using assms(1) assms(2) by auto
 qed
 moreover have A2: "smult' (1/ \<alpha>) (norm' ((gyroplus (scale \<alpha> a) (scale \<alpha> b)))) \<le>
  smult' (1/ \<alpha>) 
        (oplus' (norm' (scale \<alpha> a)) (norm' (scale \<alpha> b)))"
 
 proof-
   have "(norm' ((gyroplus (scale \<alpha> a) (scale \<alpha> b))))\<in> norms_all"
     by (simp add: "*" norms_all_def norms_def)
   moreover have " (oplus' (norm' (scale \<alpha> a)) (norm' (scale \<alpha> b))) \<in> norms_all"
     by (metis UnI1 \<open>a \<in> dom\<close> \<open>b \<in> dom\<close> bij_betw_imp_surj_on bij_betw_inv_into f''_bij image_eqI norms_all_def norms_def oplus'_def rangeI scale_closed)
   moreover have "(norm' ((gyroplus (scale \<alpha> a) (scale \<alpha> b))))
\<le>  (oplus' (norm' (scale \<alpha> a)) (norm' (scale \<alpha> b)))"
     using \<open>norm' (\<alpha> \<otimes> a \<oplus> \<alpha> \<otimes> b) \<le> norm' (\<alpha> \<otimes> a) \<oplus>\<^sub>f norm' (\<alpha> \<otimes> b)\<close> by fastforce
   ultimately show ?thesis using   space_otimes'_mon2
     using assms(2) by blast
 qed
  ultimately show ?thesis 
  proof-
       have "gyroplus (scale \<alpha> a) (scale \<alpha> b)\<in>dom"
            using "*" by force
          moreover have "scale \<alpha> b \<in> dom"
            using \<open>b \<in> dom\<close> scale_closed by blast
        moreover have "scale \<alpha> a \<in> dom"
          using \<open>a \<in> dom\<close> scale_closed by blast
        ultimately show ?thesis
          using A1 A2 
          using \<open>(1 / \<alpha>) \<otimes>\<^sub>f (norm' (\<alpha> \<otimes> a) \<oplus>\<^sub>f norm' (\<alpha> \<otimes> b)) = norm' a \<oplus>\<^sub>f norm' b\<close> \<open>\<alpha>_plus a b = (1 / \<alpha>) \<otimes> (\<alpha> \<otimes> a \<oplus> \<alpha> \<otimes> b)\<close> \<open>a \<in> dom\<close> \<open>b \<in> dom\<close> norm'_d scale_closed by force
         (* by (simp add: norm'_d)*)
      qed
    qed
  qed
qed


lemma space_ax13:
 fixes \<alpha>::real
  fixes \<alpha>_plus::"'a \<Rightarrow> 'a \<Rightarrow>'a"
  assumes "ggv_space dom gyrozero gyroplus gyroinv gyr scale oplus' smult' fi 0"
 "\<alpha> > 0"
  "\<forall>a.\<forall>b. \<alpha>_plus a b =  (if (a\<in>dom \<and> b\<in>dom) then scale (1/\<alpha>) (gyroplus (scale \<alpha> a) (scale \<alpha> b))
    else undefined)"
"\<forall>u. \<forall>v. \<forall>w. gyr_o' u v w = (if u\<in>dom\<and>v\<in>dom\<and>w\<in>dom then scale (1/ \<alpha>)  (gyr (scale \<alpha> u) (scale \<alpha> v) (scale \<alpha>  w))
else undefined)"
  shows "\<forall>u\<in>dom.\<forall>v\<in>dom.\<forall>a\<in>dom. norm ((fi (gyr_o' u v a))) = norm (fi a)"
(* \<forall>u\<in>dom.\<forall>v\<in>dom.\<forall>a\<in>dom.\<forall>b\<in>dom. inner (fi (gyr_o' u v a))  (fi (gyr_o' u v b))
 = inner (fi a) (fi b)"*)
proof
  fix u
  assume "u\<in>dom"
    show "\<forall>v\<in>dom.\<forall>a\<in>dom.
 norm ((fi (gyr_o' u v a))) = norm (fi a)"
  proof
    fix v 
    assume "v\<in>dom"
    show "\<forall>a\<in>dom.
  norm ((fi (gyr_o' u v a))) = norm (fi a)"
    proof
      fix a
      assume "a\<in>dom"
    show " norm ((fi (gyr_o' u v a))) = norm (fi a)"
      
    proof-
      have " (gyr_o' u v a) = scale (1/ \<alpha>)  (gyr (scale \<alpha> u) (scale \<alpha> v) (scale \<alpha>  a))"
        by (simp add: \<open>a \<in> dom\<close> \<open>u \<in> dom\<close> \<open>v \<in> dom\<close> assms(4))

      moreover have "(gyr_o' u v a) = (gyr (scale \<alpha> u) (scale \<alpha> v) (scale (1/ \<alpha>) (scale \<alpha> a)))"

        by (simp add: \<open>a \<in> dom\<close> \<open>u \<in> dom\<close> \<open>v \<in> dom\<close> calculation gyroauto_property scale_closed)
      moreover have "(gyr_o' u v a) = (gyr (scale \<alpha> u) (scale \<alpha> v) a)"
        by (metis \<open>a \<in> dom\<close> assms(2) calculation(2) comm_monoid_mult_class.mult_1 divide_self less_numeral_extra(3) scale_1 scale_assoc times_divide_eq_left)
      ultimately show ?thesis 
        by (metis \<open>a \<in> dom\<close> \<open>u \<in> dom\<close> \<open>v \<in> dom\<close> assms(1) ggv_space.ax_norm_ggv
            scale_closed)
    qed     
  qed
qed
qed

lemma proposition_3_11_gyrogroupoid:
  fixes \<alpha>::real
  fixes \<alpha>_plus::"'a\<Rightarrow>'a \<Rightarrow>'a"
  assumes "\<alpha> > 0"
  "\<forall>a.\<forall>b. \<alpha>_plus a b =  (if (a\<in>dom \<and> b\<in>dom) then scale (1/\<alpha>) (gyroplus (scale \<alpha> a) (scale \<alpha> b))
    else undefined)"
"ggv_space dom gyrozero gyroplus gyroinv gyr scale oplus' smult' fi 0"
shows  "gyrogroupoid dom gyrozero \<alpha>_plus"
proof
show "0\<^sub>g \<in> dom"
    using zero_in_dom by blast
next
  show "\<And>a b. a \<in> dom \<and> b \<in> dom \<longrightarrow> \<alpha>_plus a b \<in> dom"
    by (simp add: assms(2) gyroplus_closed scale_closed)
next
  show "\<exists>a. a \<in> dom \<and> a \<noteq> 0\<^sub>g"
    using non_trivial_dom by blast
qed

lemma proposition_3_11_gyrocommutative_gyrogroup:
  fixes \<alpha>::real
  fixes \<alpha>_plus::"'a\<Rightarrow>'a \<Rightarrow>'a"
  assumes "\<alpha> > 0"
  "\<forall>a.\<forall>b. \<alpha>_plus a b =  (if (a\<in>dom \<and> b\<in>dom) then scale (1/\<alpha>) (gyroplus (scale \<alpha> a) (scale \<alpha> b))
    else undefined)"
shows "gyrocommutative_gyrogroup dom gyrozero  \<alpha>_plus (\<lambda>x. (if x \<in>dom then gyroinv x else undefined))
 (\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)
 ) "
proof-
  have "normed_gyrolinear_space dom gyrozero \<alpha>_plus (\<lambda>x. (if x \<in>dom then gyroinv x else undefined))
 (\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)
 )  (\<lambda>r a. if a \<in> dom then r \<otimes> a else undefined)
(\<lambda>x. if x \<in> dom then norm' x
          else undefined) (\<lambda>x. if x \<in> norm' ` dom then \<bar>\<alpha>\<bar> * f x else undefined)"
    using assms(1) assms(2) proposition_3_11 by auto
  then show ?thesis 
    by (simp add: gyrolinear_space_def normed_gyrolinear_space_def)
qed


(*
  assumes scale_closed: "\<forall>r::real. (\<forall>x\<in>dom. ((scale r x) \<in> dom))"
  assumes scale_1:"\<forall>a\<in>dom. scale 1 a = a"
  assumes  scale_distrib: "\<forall>r1::real. \<forall>r2::real. \<forall>a\<in>dom. scale (r1+r2) a = (scale r1 a) \<oplus> (scale r2 a)"
  assumes  scale_assoc:"\<forall>r1::real. \<forall>r2::real. \<forall>a\<in>dom. scale (r1*r2) a = scale r1 (scale r2 a)"
  assumes scale_prop1:"\<forall>a\<in>dom. \<forall>r::real. ((a\<noteq>gyrozero \<and> r\<noteq>0)\<longrightarrow> (fi (scale \<bar>r\<bar> a)) /\<^sub>R (norm (fi (scale r a))) = (fi a) /\<^sub>R (norm (fi a)))"
  assumes "\<forall>r::real. \<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>a\<in>dom. gyr u v (scale r a) = scale r (gyr u v a)"
  assumes "\<forall>r1::real. \<forall>r2::real. \<forall>v\<in>dom. \<forall>x\<in>dom. (gyr (scale r1 v) (scale r2 v) x = x)"
*)

definition scale'::"real\<Rightarrow>'a\<Rightarrow>'a" where 
  "scale' =  (\<lambda>r a. if a \<in> dom then r \<otimes> a else undefined)"
lemma space_ax3:
  shows "\<forall>r::real. (\<forall>x\<in>dom. ((scale' r x) \<in> dom))"
  using scale'_def scale_closed by auto
lemma space_ax4:
  shows "\<forall>a\<in>dom. scale' 1 a = a"
  using scale'_def scale_1 by auto
lemma space_ax5:
 fixes \<alpha>::real
  fixes \<alpha>_plus::"'a\<Rightarrow>'a \<Rightarrow>'a"
  assumes "\<alpha> > 0"
  "\<forall>a.\<forall>b. \<alpha>_plus a b =  (if (a\<in>dom \<and> b\<in>dom) then scale (1/\<alpha>) (gyroplus (scale \<alpha> a) (scale \<alpha> b))
    else undefined)"
  shows "\<forall>r1::real. \<forall>r2::real. \<forall>a\<in>dom. scale' (r1+r2) a = \<alpha>_plus (scale' r1 a)  (scale' r2 a)"
proof
  fix r1 
  show "\<forall>r2::real. \<forall>a\<in>dom. scale' (r1+r2) a = \<alpha>_plus (scale' r1 a)  (scale' r2 a)"
  proof
    fix r2
    show "\<forall>a\<in>dom. scale' (r1+r2) a = \<alpha>_plus (scale' r1 a)  (scale' r2 a)"
    proof
      fix a
      assume "a\<in>dom"
      show " scale' (r1+r2) a = \<alpha>_plus (scale' r1 a)  (scale' r2 a)"
      proof-
        have "\<alpha>_plus (scale' r1 a)  (scale' r2 a) =  scale (1/\<alpha>) (gyroplus (scale \<alpha> (scale' r1 a)) (scale \<alpha> (scale' r2 a)))"
          by (simp add: \<open>a \<in> dom\<close> assms(2) space_ax3)
        moreover have " scale (1/\<alpha>) (gyroplus (scale \<alpha> (scale' r1 a)) (scale \<alpha> (scale' r2 a))) = scale (1/ \<alpha>) (scale \<alpha> (gyroplus (scale' r1 a) (scale' r2 a)))"
          by (metis \<open>a \<in> dom\<close> ring_class.ring_distribs(1) scale'_def scale_assoc scale_distrib)
        moreover have " (1 / \<alpha>) \<otimes> (\<alpha> \<otimes> (scale' r1 a \<oplus> scale' r2 a)) = scale' r1 a \<oplus> scale' r2 a"
          by (metis \<open>a \<in> dom\<close> assms(1) gyroplus_closed mult_cancel_right1 nonzero_divide_eq_eq not_real_square_gt_zero scale_1 scale_assoc space_ax3)
        ultimately show ?thesis
          by (simp add: \<open>a \<in> dom\<close> scale'_def scale_distrib)
      qed
    qed
  qed
qed
  
lemma space_ax6:
  shows "\<forall>r1::real. \<forall>r2::real. \<forall>a\<in>dom. scale' (r1*r2) a = scale' r1 (scale' r2 a)"
  using scale'_def scale_assoc space_ax3 by auto
lemma space_ax7:
  assumes "ggv_space dom gyrozero gyroplus gyroinv gyr scale oplus' smult' fi 0"
  shows "\<forall>a\<in>dom. \<forall>r::real. ((a\<noteq>gyrozero \<and> r\<noteq>0)\<longrightarrow> (fi (scale' \<bar>r\<bar> a)) /\<^sub>R (norm (fi (scale' r a))) = (fi a) /\<^sub>R (norm (fi a)))"
  by (metis assms ggv_space.scale_prop1_ggv scale'_def)
lemma space_ax8:
 assumes  "ggv_space dom gyrozero gyroplus gyroinv gyr scale oplus' smult' fi 0"
  shows "\<forall>r::real. \<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>a\<in>dom. gyr u v (scale' r a) = scale' r (gyr u v a)"
  by (metis bij_betw_iff_bijections gyr_gyroaut gyroaut_def gyroauto_property scale'_def)

lemma space_ax9:
 assumes  "ggv_space dom gyrozero gyroplus gyroinv gyr scale oplus' smult' fi 0"
 shows "\<forall>r1::real. \<forall>r2::real. \<forall>v\<in>dom. \<forall>x\<in>dom. (gyr (scale' r1 v) (scale' r2 v) x = x)"
  using gyroauto_id scale'_def by force


lemma space_ax10:
 assumes  "ggv_space dom gyrozero gyroplus gyroinv gyr scale oplus' smult' fi 0"
  shows "one_dim_vector_space_with_domain {x.\<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} oplus' 0 smult'"
  using norm'_d
  using assms ggv_intro.one_dim_vs_ggv ggv_space_def by fastforce


lemma space_ax11:
 assumes  "ggv_space dom gyrozero gyroplus gyroinv gyr scale oplus' smult' fi 0"
  shows "\<forall>r::real.\<forall>a\<in>dom. norm (fi (scale' r a)) = smult' \<bar>r\<bar> (norm (fi a))"
  by (metis assms ggv_intro.norm_smult'_ggv ggv_space_def scale'_def)

lemma proposition_3_11_gyrospace:
  fixes \<alpha>::real
  fixes \<alpha>_plus::"'a\<Rightarrow>'a \<Rightarrow>'a"
  assumes "\<alpha> > 0"
  "\<forall>a.\<forall>b. \<alpha>_plus a b =  (if (a\<in>dom \<and> b\<in>dom) then scale (1/\<alpha>) (gyroplus (scale \<alpha> a) (scale \<alpha> b))
    else undefined)"
 "ggv_space dom gyrozero gyroplus gyroinv gyr scale oplus' smult' fi 0"
shows "ggv_space dom gyrozero \<alpha>_plus   (\<lambda>x. (if x \<in>dom then gyroinv x else undefined))
 (\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)
 )  (\<lambda>r a. if a \<in> dom then r \<otimes> a else undefined)
oplus' smult' fi 0"
proof
  show "0\<^sub>g \<in> dom"
    by (simp add: zero_in_dom)
next
  show "\<And>a b. a \<in> dom \<and> b \<in> dom \<longrightarrow> \<alpha>_plus a b \<in> dom"
    by (simp add: assms(2) gyroplus_closed scale_closed)
next
  show "\<exists>a. a \<in> dom \<and> a \<noteq> 0\<^sub>g"
    using non_trivial_dom by blast
next
  show "\<And>a. a \<in> dom \<longrightarrow> (if a \<in> dom then \<ominus> a else undefined) \<in> dom"
    using ax1 by auto
next
  show "\<And>a b c.
       a \<in> dom \<and> b \<in> dom \<and> c \<in> dom \<longrightarrow>
       (if a \<in> dom \<and> b \<in> dom \<and> c \<in> dom
        then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> a) (\<alpha> \<otimes> b) (\<alpha> \<otimes> c) else undefined)
       \<in> dom"
  by (smt (z3) gyrogroup_axioms gyrogroup_axioms_def gyrogroup_def scale_closed)
next
  show "\<And>a. a \<in> dom \<longrightarrow> \<alpha>_plus 0\<^sub>g a = a"
    using proposition_3_11_gyrocommutative_gyrogroup[OF assms(1) assms(2)]
    by (meson gyrocommutative_gyrogroup_def gyrogroup.gyro_left_id)
next
  show "\<And>a. a \<in> dom \<longrightarrow> \<alpha>_plus (if a \<in> dom then \<ominus> a else undefined) a = 0\<^sub>g"
    using proposition_3_11_gyrocommutative_gyrogroup[OF assms(1) assms(2)]
    by (meson gyrocommutative_gyrogroup.axioms(1) gyrogroup.gyro_left_inv)
next
  show "\<And>a b z.
       a \<in> dom \<and> b \<in> dom \<and> z \<in> dom \<longrightarrow>
       \<alpha>_plus a (\<alpha>_plus b z) =
       \<alpha>_plus (\<alpha>_plus a b)
        (if a \<in> dom \<and> b \<in> dom \<and> z \<in> dom
         then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> a) (\<alpha> \<otimes> b) (\<alpha> \<otimes> z) else undefined)"
    using proposition_3_11_gyrocommutative_gyrogroup[OF assms(1) assms(2)]
      gyrogroup_axioms_def[of dom gyrozero \<alpha>_plus  "(\<lambda>x. (if x \<in>dom then gyroinv x else undefined))"
 "(\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)
 )" ]
    using gyrocommutative_gyrogroup.axioms(1) gyrogroup.axioms(2) by fastforce
next
  show " \<And>a b. a \<in> dom \<and> b \<in> dom \<longrightarrow>
           (\<forall>x\<in>dom.
               (if a \<in> dom \<and> b \<in> dom \<and> x \<in> dom
                then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> a) (\<alpha> \<otimes> b) (\<alpha> \<otimes> x) else undefined) =
               (if \<alpha>_plus a b \<in> dom \<and> b \<in> dom \<and> x \<in> dom
                then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> \<alpha>_plus a b) (\<alpha> \<otimes> b) (\<alpha> \<otimes> x)
                else undefined))"
  using proposition_3_11_gyrocommutative_gyrogroup[OF assms(1) assms(2)]
      gyrogroup_axioms_def[of dom gyrozero \<alpha>_plus  "(\<lambda>x. (if x \<in>dom then gyroinv x else undefined))"
 "(\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)
 )" ]
  using gyrocommutative_gyrogroup.axioms(1) gyrogroup.axioms(2) by fastforce
next
  show "\<And>x y. x \<in> dom \<and> y \<in> dom \<longrightarrow>
           gyrogroupoid.gyroaut dom \<alpha>_plus
            (\<lambda>c. if x \<in> dom \<and> y \<in> dom \<and> c \<in> dom
                  then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> x) (\<alpha> \<otimes> y) (\<alpha> \<otimes> c) else undefined)"
    using proposition_3_11_gyrocommutative_gyrogroup[OF assms(1) assms(2)]
      gyrogroup_axioms_def[of dom gyrozero \<alpha>_plus  "(\<lambda>x. (if x \<in>dom then gyroinv x else undefined))"
 "(\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)
 )" ]
    using gyrocommutative_gyrogroup.axioms(1) gyrogroup.axioms(2) by fastforce
next
  show "\<forall>a\<in>dom.
       \<forall>b\<in>dom.
          \<alpha>_plus a b =
          (if a \<in> dom \<and> b \<in> dom \<and> \<alpha>_plus b a \<in> dom
           then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> a) (\<alpha> \<otimes> b) (\<alpha> \<otimes> \<alpha>_plus b a) else undefined)"
    using proposition_3_11_gyrocommutative_gyrogroup[OF assms(1) assms(2)]
    using  gyrocommutative_gyrogroup_axioms_def[of dom \<alpha>_plus 
"(\<lambda> a b c. (if (a\<in>dom\<and>b\<in>dom\<and>c\<in>dom) then  (1 / \<alpha>) \<otimes> (gyr  ( \<alpha> \<otimes> a) ( \<alpha> \<otimes> b) (\<alpha> \<otimes> c)) else undefined)
 )"]
    by (simp add: gyrocommutative_gyrogroup_def)
next
  show "inj_on fi dom"
    by (meson assms(3) ggv_intro.fi_inj ggv_space_def)


next
  show "\<forall>r. \<forall>x\<in>dom. (if x \<in> dom then r \<otimes> x else undefined) \<in> dom"
    by (simp add: scale_closed)
next
  show "\<forall>a\<in>dom. (if a \<in> dom then 1 \<otimes> a else undefined) = a"
    using scale_1 by fastforce
next
  show " \<forall>r1 r2.
       \<forall>a\<in>dom.
          (if a \<in> dom then (r1 + r2) \<otimes> a else undefined) =
          \<alpha>_plus (if a \<in> dom then r1 \<otimes> a else undefined)
           (if a \<in> dom then r2 \<otimes> a else undefined)"
using space_ax5[OF assms(1) assms(2)] scale'_def 
  by auto
next
  show "\<forall>r1 r2.
       \<forall>a\<in>dom.
          (if a \<in> dom then (r1 * r2) \<otimes> a else undefined) =
          (if (if a \<in> dom then r2 \<otimes> a else undefined) \<in> dom
           then r1 \<otimes> (if a \<in> dom then r2 \<otimes> a else undefined) else undefined)"
    by (simp add: scale_assoc scale_closed)
next
  show "\<forall>a\<in>dom.
       \<forall>r. a \<noteq> 0\<^sub>g \<and> r \<noteq> 0 \<longrightarrow>
           fi (if a \<in> dom then \<bar>r\<bar> \<otimes> a else undefined) /\<^sub>R
           norm (fi (if a \<in> dom then r \<otimes> a else undefined)) =
           fi a /\<^sub>R norm (fi a)"
    using assms(3) ggv_space.scale_prop1_ggv by force
next
  show " \<forall>r. \<forall>u\<in>dom.
           \<forall>v\<in>dom.
              \<forall>a\<in>dom.
                 (if u \<in> dom \<and>
                     v \<in> dom \<and> (if a \<in> dom then r \<otimes> a else undefined) \<in> dom
                  then (1 / \<alpha>) \<otimes>
                       gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v)
                        (\<alpha> \<otimes> (if a \<in> dom then r \<otimes> a else undefined))
                  else undefined) =
                 (if (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                      then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a)
                      else undefined)
                     \<in> dom
                  then r \<otimes>
                       (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                        then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a)
                        else undefined)
                  else undefined)"
  proof
    fix r
    show " \<forall>u\<in>dom.
           \<forall>v\<in>dom.
              \<forall>a\<in>dom.
                 (if u \<in> dom \<and>
                     v \<in> dom \<and> (if a \<in> dom then r \<otimes> a else undefined) \<in> dom
                  then (1 / \<alpha>) \<otimes>
                       gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v)
                        (\<alpha> \<otimes> (if a \<in> dom then r \<otimes> a else undefined))
                  else undefined) =
                 (if (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                      then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a)
                      else undefined)
                     \<in> dom
                  then r \<otimes>
                       (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                        then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a)
                        else undefined)
                  else undefined)"
    proof
      fix u
      assume "u\<in>dom"
      show "\<forall>v\<in>dom.
              \<forall>a\<in>dom.
                 (if u \<in> dom \<and>
                     v \<in> dom \<and> (if a \<in> dom then r \<otimes> a else undefined) \<in> dom
                  then (1 / \<alpha>) \<otimes>
                       gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v)
                        (\<alpha> \<otimes> (if a \<in> dom then r \<otimes> a else undefined))
                  else undefined) =
                 (if (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                      then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a)
                      else undefined)
                     \<in> dom
                  then r \<otimes>
                       (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                        then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a)
                        else undefined)
                  else undefined)"
      proof
        fix v
        assume "v\<in>dom"
        show "
              \<forall>a\<in>dom.
                 (if u \<in> dom \<and>
                     v \<in> dom \<and> (if a \<in> dom then r \<otimes> a else undefined) \<in> dom
                  then (1 / \<alpha>) \<otimes>
                       gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v)
                        (\<alpha> \<otimes> (if a \<in> dom then r \<otimes> a else undefined))
                  else undefined) =
                 (if (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                      then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a)
                      else undefined)
                     \<in> dom
                  then r \<otimes>
                       (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                        then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a)
                        else undefined)
                  else undefined)"
        proof
          fix a
          assume "a\<in>dom"
          show "
                 (if u \<in> dom \<and>
                     v \<in> dom \<and> (if a \<in> dom then r \<otimes> a else undefined) \<in> dom
                  then (1 / \<alpha>) \<otimes>
                       gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v)
                        (\<alpha> \<otimes> (if a \<in> dom then r \<otimes> a else undefined))
                  else undefined) =
                 (if (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                      then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a)
                      else undefined)
                     \<in> dom
                  then r \<otimes>
                       (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                        then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a)
                        else undefined)
                  else undefined)"
          proof-
            have "(if u \<in> dom \<and>
                     v \<in> dom \<and> (if a \<in> dom then r \<otimes> a else undefined) \<in> dom
                  then (1 / \<alpha>) \<otimes>
                       gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v)
                        (\<alpha> \<otimes> (if a \<in> dom then r \<otimes> a else undefined))
                  else undefined) =  (1 / \<alpha>) \<otimes>
                       gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v)
                        (\<alpha> \<otimes> (r \<otimes> a))"
              by (simp add: \<open>a \<in> dom\<close> \<open>u \<in> dom\<close> \<open>v \<in> dom\<close> scale_closed)
            moreover have " (if (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                      then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a)
                      else undefined)
                     \<in> dom
                  then r \<otimes>
                       (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                        then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a)
                        else undefined)
                  else undefined) =  r \<otimes> ((1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a))"
              by (simp add: \<open>a \<in> dom\<close> \<open>u \<in> dom\<close> \<open>v \<in> dom\<close> ax1 gyr_def gyroplus_closed scale_closed)
            moreover have " (1 / \<alpha>) \<otimes>
                       gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v)
                        (\<alpha> \<otimes> (r \<otimes> a)) =  r \<otimes> ((1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a))"
              by (smt (z3) \<open>a \<in> dom\<close> \<open>u \<in> dom\<close> \<open>v \<in> dom\<close> divide_divide_eq_right gyroauto_property nonzero_mult_div_cancel_left scale_assoc scale_closed times_divide_eq_left)
            ultimately show ?thesis 
              by presburger
          qed
        qed
      qed
    qed
  qed
next
  show "\<forall>r1 r2.
       \<forall>v\<in>dom.
          \<forall>x\<in>dom.
             (if (if v \<in> dom then r1 \<otimes> v else undefined) \<in> dom \<and>
                 (if v \<in> dom then r2 \<otimes> v else undefined) \<in> dom \<and> x \<in> dom
              then (1 / \<alpha>) \<otimes>
                   gyr (\<alpha> \<otimes> (if v \<in> dom then r1 \<otimes> v else undefined))
                    (\<alpha> \<otimes> (if v \<in> dom then r2 \<otimes> v else undefined)) (\<alpha> \<otimes> x)
              else undefined) =
             x"
    by (smt (verit, ccfv_threshold) assms(1) divide_self gyroauto_id scale_1 scale_assoc scale_closed times_divide_eq_left times_divide_eq_right)
next
  show "\<And>x y. x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
           y \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
           x  \<oplus>\<^sub>f y \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}"
    using space_ax10[OF assms(3)] vector_space_with_domain_def
    by (smt (z3) one_dim_vector_space_with_domain_def)
next
  show "0 \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}"
   using space_ax10[OF assms(3)] vector_space_with_domain_def
   by (smt (z3) one_dim_vector_space_with_domain_def)
next
  show " \<And>x y z.
       x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
       y \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
       z \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
       x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z)"
   using space_ax10[OF assms(3)] vector_space_with_domain_def
   by (smt (z3) one_dim_vector_space_with_domain_def)
next
  show " \<And>x y. x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
           y \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
           x  \<oplus>\<^sub>f y = y  \<oplus>\<^sub>f x"
  using space_ax10[OF assms(3)] vector_space_with_domain_def
  by (smt (z3) one_dim_vector_space_with_domain_def)
next
  show "\<And>x. x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow> x  \<oplus>\<^sub>f 0 = x"
   using space_ax10[OF assms(3)] vector_space_with_domain_def
   by (smt (z3) one_dim_vector_space_with_domain_def)
next
  show " \<And>x. x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
         \<exists>y\<in>{x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}. x  \<oplus>\<^sub>f y = 0"
   using space_ax10[OF assms(3)] vector_space_with_domain_def
   by (smt (z3) one_dim_vector_space_with_domain_def)
next
  show "\<And>x a. x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
           a \<otimes>\<^sub>f x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)}"
  using space_ax10[OF assms(3)] vector_space_with_domain_def
  by (smt (z3) one_dim_vector_space_with_domain_def)
next
  show "\<And>x a b.
       x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
       (a + b) \<otimes>\<^sub>f x = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (b \<otimes>\<^sub>f x)"
 using space_ax10[OF assms(3)] vector_space_with_domain_def
  by (smt (z3) one_dim_vector_space_with_domain_def)
next
  show " \<And>x a b.
       x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
       a \<otimes>\<^sub>f (b \<otimes>\<^sub>f x) = (a * b) \<otimes>\<^sub>f x"
using space_ax10[OF assms(3)] vector_space_with_domain_def
  by (smt (z3) one_dim_vector_space_with_domain_def)
next
  show "\<And>x. x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow> 1 \<otimes>\<^sub>f x = x"
  using space_ax10[OF assms(3)] vector_space_with_domain_def
  by (smt (z3) one_dim_vector_space_with_domain_def)
next
  show " \<forall>y x. y \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<and>
          x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<and> x \<noteq> 0 \<longrightarrow>
          (\<exists>!r. y = r \<otimes>\<^sub>f x)"
using space_ax10[OF assms(3)] vector_space_with_domain_def
   one_dim_vector_space_with_domain_def
one_dim_vector_space_with_domain_axioms_def  
  by (smt (z3))
next
  show "\<forall>r. \<forall>a\<in>dom.
           norm (fi (if a \<in> dom then r \<otimes> a else undefined)) =
           \<bar>r\<bar> \<otimes>\<^sub>f norm (fi a)"
    using assms(3) scale'_def space_ax11 by presburger
next
  show "\<forall>a\<in>dom. \<forall>b\<in>dom. norm (fi (\<alpha>_plus a b)) \<le> norm (fi a)  \<oplus>\<^sub>f norm (fi b)"
    using space_ax12[OF assms(3) assms(1) assms(2)]
    by meson

next
  show "\<And>x y a.
       x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
       y \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
       a \<otimes>\<^sub>f (x  \<oplus>\<^sub>f y) = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (a \<otimes>\<^sub>f y)"
  proof-
    fix x y a
    show "  x \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
       y \<in> {x. \<exists>a\<in>dom. x = norm (fi a) \<or> x = - norm (fi a)} \<Longrightarrow>
       a \<otimes>\<^sub>f (x  \<oplus>\<^sub>f y) = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (a \<otimes>\<^sub>f y)"
 using space_ax10[OF assms(3)] vector_space_with_domain_def
      by (smt (z3) one_dim_vector_space_with_domain_def)
  qed
next
  show "\<forall>u\<in>dom.
       \<forall>v\<in>dom.
          \<forall>a\<in>dom.
             norm
              (fi (if u \<in> dom \<and> v \<in> dom \<and> a \<in> dom
                   then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> a) else undefined)) =
             norm (fi a)"
 using space_ax13[OF assms(3) assms(1) assms(2), of "\<lambda>u v w. (if u \<in> dom \<and> v \<in> dom \<and> w \<in> dom
                      then (1 / \<alpha>) \<otimes> gyr (\<alpha> \<otimes> u) (\<alpha> \<otimes> v) (\<alpha> \<otimes> w)
                      else undefined)"] 
    by presburger
qed


end

context normed_gyrolinear_space''
begin

definition isgyrometric::"('a\<Rightarrow>'a\<Rightarrow>real) \<Rightarrow> bool" where
  "isgyrometric f \<longleftrightarrow> 
(\<forall>a b.(if  a \<in> dom \<and> b\<in>dom then f a b=norm' (a \<oplus> (\<ominus>b)) else f a b =undefined))"

lemma gyrom_id:
  assumes "x\<in>dom" "isgyrometric f"
  shows "f x x = 0"
  using assms(1,2) isgyrometric_def local.norm_zero zero_in_dom by force

lemma gyrom_id2:
  assumes "x\<in>dom" "y\<in>dom" "isgyrometric f" "f x y = 0"
  shows "x=y"
  using isgyrometric_def
  by (metis assms(1,2,3,4) ax1 gyro_inv_idem gyro_rigth_inv gyroplus_closed
      local.norm_zero oplus_ominus_cancel)

lemma proposition15_hatori_abe:
  assumes "isgyrometric q" "a\<in> dom"  "b\<in>dom" "x\<in>dom"
  shows "q a b = q (x\<oplus>a) (x\<oplus>b)"
  by (smt (verit, del_insts) assms(1,2,3,4) ax1 gyr_commute_misc_3
      gyroautomorphic_inverse gyrominus_def gyroplus_closed isgyrometric_def norm_gyr
      oplus_ominus_cancel)

definition gyromid::"'a\<Rightarrow>'a\<Rightarrow>'a" where
  "gyromid a b = (if a \<in> dom \<and> b\<in>dom then (1/2)\<otimes>(a \<oplus>\<^sub>c b) else undefined)"

lemma otimes'_1:
  assumes "a\<in>dom"
  shows "otimes' 1 (norm' a) = norm' a"
  by (metis abs_one assms norm_scale scale_1)

lemma eq_3_hatori_abe:
  assumes "a\<in>dom" "b\<in>dom"
  shows "gyromid a b = a \<oplus> (1/2)\<otimes>((\<ominus>a) \<oplus> b)"
proof-
  have "2\<otimes> (a \<oplus> (1/2)\<otimes>((\<ominus>a) \<oplus> b)) = a\<oplus>((\<ominus>a\<oplus>b)\<oplus>a)"
  proof-
    have "2\<otimes> (a \<oplus> (1/2)\<otimes>((\<ominus>a) \<oplus> b)) = a \<oplus> (2 \<otimes> ((1/2)\<otimes>((\<ominus>a) \<oplus> b))\<oplus>a)"
      by (simp add: assms(1,2) ax1 gyroplus_closed scale_closed two_sum)
    then show ?thesis 
      by (smt (verit, ccfv_threshold) assms(1,2) ax1 field_sum_of_halves gyroplus_closed
          mult.commute scale_1 scale_assoc times_divide_eq_right)
  qed
  moreover have "a\<oplus>((\<ominus>a\<oplus>b)\<oplus>a) = (a\<oplus>(\<ominus>a\<oplus>b))\<oplus>(gyr a  (\<ominus>a\<oplus>b) a)"
    using assms(1,2) ax1 gyro_left_assoc gyroplus_closed by presburger
  moreover have "(a\<oplus>(\<ominus>a\<oplus>b))\<oplus>(gyr a  (\<ominus>a\<oplus>b) a) = b\<oplus>gyr b (\<ominus>a) a"
    using assms(1,2) calculation(2) cogyro_commute cogyro_plus_def cogyroplus_def
    by force
  moreover have "b\<oplus>gyr b (\<ominus>a) a = b\<oplus>\<^sub>c a"
    using cogyroplus_def by auto
  moreover have " b\<oplus>\<^sub>c a =  a\<oplus>\<^sub>c b"
    using assms(1,2) cogyro_commute by blast
  moreover have "2\<otimes> (a \<oplus> (1/2)\<otimes>((\<ominus>a) \<oplus> b))  =a\<oplus>\<^sub>c b"
    using calculation(1,2,3,4,5) by argo
  moreover have "2 \<otimes> ((1/2) \<otimes> (a\<oplus>\<^sub>c b)) = a\<oplus>\<^sub>c b"
    by (metis (no_types, lifting) assms(1,2) ax1 calculation(4,5) distrib_right
        field_sum_of_halves gyr_def_closed gyroplus_closed one_add_one scale_1 scale_assoc
        times_divide_eq_right)
  moreover have "2 \<otimes> (gyromid a b) = 2\<otimes> (a \<oplus> (1/2)\<otimes>((\<ominus>a) \<oplus> b)) "
    using assms(1,2) calculation(6,7) gyromid_def by presburger
  moreover have "(1/2)\<otimes>(2 \<otimes> (gyromid a b)) =(1/2)\<otimes>( 2\<otimes> (a \<oplus> (1/2)\<otimes>((\<ominus>a) \<oplus> b)))"
    using calculation(8) by presburger
  moreover have "(1/2)\<otimes>(2 \<otimes> (gyromid a b)) = (1/2 * 2)  \<otimes> (gyromid a b)"
     using scale_assoc
     by (metis assms(1,2) cogyroplus_closed gyromid_def scale_closed)
   moreover have "(1/2)\<otimes>( 2\<otimes> (a \<oplus> (1/2)\<otimes>((\<ominus>a) \<oplus> b))) = (1/2 * 2)  \<otimes>  (a \<oplus> (1/2)\<otimes>((\<ominus>a) \<oplus> b))"
      using scale_assoc
      by (metis assms(1,2) ax1 gyroplus_closed scale_closed)
  ultimately show ?thesis
    by (simp add: assms(1,2) ax1 gyromid_def gyroplus_closed scale_1 scale_closed)
qed


lemma gyromid_minus_sym:
  assumes "a\<in>dom" "b\<in>dom" "isgyrometric q"
  shows "q a b = q (\<ominus>a) (\<ominus>b)"
proof-
  have "q a b = norm' (a \<oplus> (\<ominus>b))"
    using assms(1,2,3) isgyrometric_def by force
  moreover have "\<ominus> (a \<oplus> (\<ominus>b)) = (\<ominus>a) \<oplus> (\<ominus> (\<ominus>b))"
    using assms(1,2) ax1 gyroautomorphic_inverse gyrominus_def by presburger
  moreover have "\<forall>x\<in>dom. norm' x = norm' (\<ominus>x)"
  proof
    fix x
    assume "x\<in>dom"
    show "norm' x = norm' (\<ominus>x)"
    proof-
      have "norm' (\<ominus>x) = norm' ((-1::real) \<otimes> x)"
        by (simp add: \<open>x \<in> dom\<close> scale_minus1_inv)
      then show ?thesis 
        by (simp add: \<open>x \<in> dom\<close> norm_scale otimes'_1)   
    qed
  qed
  ultimately show ?thesis 
    by (metis (full_types) assms(1,3) ax1 gyroplus_closed isgyrometric_def)
qed

lemma proposition15_hatori_abe_2_help:
  assumes "isgyrometric q" "a\<in> dom"  "b\<in>dom"
  shows "q a (gyromid a b) = otimes' (1/2) (q a b)"
proof-
  have "gyromid a b = (1/2)\<otimes>(a \<oplus>\<^sub>c b)"
    using assms(2,3) gyromid_def by force
  moreover have "q a (gyromid a b) = q (\<ominus>a) (\<ominus> (gyromid a b))"
    by (simp add: assms(1,2,3) calculation cogyroplus_closed gyromid_minus_sym
        scale_closed)
  moreover have " q (\<ominus>a) (\<ominus> (gyromid a b)) = norm' (\<ominus>a \<oplus> (gyromid a b))"
    using assms(1,2,3) ax1 calculation(1) cogyroplus_closed isgyrometric_def scale_closed
    by auto
  moreover have "norm' (\<ominus>a \<oplus> (gyromid a b)) = norm' ((1/2) \<otimes> (\<ominus>a \<oplus> b))"
    by (metis assms(2,3) ax1 eq_3_hatori_abe gyro_inv_idem gyroplus_closed
        oplus_ominus_cancel scale_closed)
  moreover have "otimes' (1/2) (norm' (\<ominus>a \<oplus> b)) =  norm' ((1/2) \<otimes> (\<ominus>a \<oplus> b))"
    by (simp add: assms(2,3) ax1 gyroplus_closed norm_scale)
  moreover have "q a (gyromid a b) = otimes' (1/2) (q (\<ominus>a) (\<ominus>b))"
    using assms(1,2,3) ax1 calculation(2,3,4,5) isgyrometric_def by fastforce
  moreover have "q a (gyromid a b) =  otimes' (1/2) (q a b)"
    by (simp add: assms(1,2,3) calculation(6) gyromid_minus_sym)
  ultimately show ?thesis 
    by meson
qed

lemma gyrometric_sym:
  assumes "isgyrometric q" "a\<in> dom"  "b\<in>dom" 
  shows "q a b = q b a"
by (smt (verit, ccfv_threshold) assms(1) gyro_commute gyro_inv_idem gyromid_minus_sym
        gyroplus_closed normed_gyrolinear_space''.isgyrometric_def
        normed_gyrolinear_space''.norm_gyr normed_gyrolinear_space''_axioms)

lemma proposition15_hatori_abe_2:
  assumes "isgyrometric q" "a\<in> dom"  "b\<in>dom" 
  shows "q a (gyromid a b) = q b (gyromid a b)"
proof-
  have "q a (gyromid a b) =  otimes' (1/2) (q a b)"
    by (simp add: assms(1,2,3) proposition15_hatori_abe_2_help)
  moreover have "q b (gyromid a b) = q b (gyromid b a)"
    by (simp add: cogyro_commute gyromid_def)
  moreover have " q b (gyromid b a) =  otimes' (1/2) (q b a)"
    by (simp add: assms(1,2,3) proposition15_hatori_abe_2_help)
  moreover have "q b a = q a b"
    by (simp add: assms(1,2,3) gyrometric_sym)
  ultimately show ?thesis 
    by presburger
qed

lemma gyrometric_triangle:
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom" "isgyrometric q"
  shows "q a c \<le> oplus' (q a b) (q b c)"
proof-
  have "q a c = q (\<ominus>a) (\<ominus>c) "
    using assms(1,3,4) gyromid_minus_sym by auto
  moreover have " q (\<ominus>a) (\<ominus>c) =  q (b\<oplus> (\<ominus>a)) (b\<oplus>(\<ominus>c))"
    by (simp add: assms(1,2,3,4) ax1 proposition15_hatori_abe)
  moreover have " q (b\<oplus> (\<ominus>a)) (b\<oplus>(\<ominus>c)) = norm' ((b\<oplus> (\<ominus>a)) \<oplus> (\<ominus>( (b\<oplus>(\<ominus>c)))))"
    using assms(1,2,3,4) ax1 gyroplus_closed isgyrometric_def by force
  moreover have " norm' ((b\<oplus> (\<ominus>a)) \<oplus> (\<ominus>( (b\<oplus>(\<ominus>c))))) \<le>oplus' (norm' (b\<oplus> (\<ominus>a))) (norm' ( (\<ominus>( (b\<oplus>(\<ominus>c))))))"
    using assms(1,2,3) ax1 gyroplus_closed norm_ineq by force
  ultimately show ?thesis
    using assms(1,2,3,4) ax1 gyroautomorphic_inverse gyrometric_sym gyromid_minus_sym
      gyrominus_def isgyrometric_def by force
qed

lemma proposition16_hatori_abe_bij:
  assumes  "z\<in>dom" 
    "fi z = (\<lambda>x. (if x \<in>dom then 2 \<otimes> z \<oplus> (\<ominus> x) else undefined))"
  shows "bij_betw (fi z) dom dom"
proof-
  have "inj_on (fi z) dom"
    by (smt (verit) assms(1,2) ax1 gyro_inv_idem gyro_left_cancel inj_onI
        scale_closed)
  moreover have "(fi z) ` dom = dom"
  proof
    show "fi z ` dom \<subseteq> dom"
      by (simp add: assms(1,2) ax1 gyroplus_closed image_subsetI scale_closed)
  next
    show " dom \<subseteq> fi z ` dom "
    proof
      fix x
      assume "x\<in>dom"
      show "x\<in>fi z ` dom"
        by (smt (verit, del_insts) \<open>x \<in> dom\<close> assms(1,2) ax1 gyro_right_id
            gyroautomorphic_inverse gyrominus_def gyroplus_closed oplus_ominus_cancel
            rev_image_eqI scale_closed zero_in_dom)
      
    qed
  qed
  ultimately show ?thesis 
    by (simp add: bij_betw_def)
qed

lemma gyromid_in_domain:
  assumes "a\<in>dom" "b\<in>dom"
  shows "gyromid a b \<in> dom"
  by (simp add: assms(1,2) cogyroplus_closed gyromid_def scale_closed)
lemma proposition16_hatori_abe_p1:
  assumes "z\<in>dom" 
    "fi z = (\<lambda>x. (if x \<in>dom then 2 \<otimes> z \<oplus> (\<ominus> x) else undefined))"
  shows "\<forall>t\<in>dom. (inv_into dom (fi z) t = fi z t)"
proof
  fix t
  assume "t\<in>dom"
  show "inv_into dom (fi z) t = fi z t"
  proof-
    have "(fi z) ((fi z) t)  = 2 \<otimes> z \<oplus> (\<ominus> (2 \<otimes> z \<oplus> (\<ominus> t)))"
      by (simp add: \<open>t \<in> dom\<close> assms(1,2) ax1 gyroplus_closed scale_closed)
    moreover have "(fi z) ((fi z) t) = t"
      by (simp add: \<open>t \<in> dom\<close> assms(1) ax1 calculation gyro_equation_right
          gyroautomorphic_inverse gyrominus_def gyroplus_closed scale_closed)
    ultimately show ?thesis 
      using proposition16_hatori_abe_bij
    proof -
      have f1: "fi z = (\<lambda>a. if a \<in> dom then 2 \<otimes> z \<oplus> \<ominus> a else undefined)"
        using assms(2) by force
      then have f2: "\<forall>f. bij_betw f dom dom \<or> f \<noteq> fi z"
        by (meson assms(1) proposition16_hatori_abe_bij)
      have "fi z t \<in> dom"
        using f1 by (simp add: \<open>t \<in> dom\<close> assms(1) ax1 gyroplus_closed scale_closed)
      then show ?thesis
        using f2 by (metis (no_types) \<open>fi z (fi z t) = t\<close> bij_betw_inv_into_left)
    qed
  qed
qed

lemma proposition16_hatori_abe_p1_v2:
  assumes "z\<in>dom" 
    "fi z = (\<lambda>x. (if x \<in>dom then 2 \<otimes> z \<oplus> (\<ominus> x) else undefined))"
  shows "\<forall>t\<in>dom. (fi z \<circ> fi z) t = t"
   using proposition16_hatori_abe_p1[OF assms(1) ]
   assms(1,2) ax1 comp_apply gyro_equation_right gyro_inv_idem
      gyroautomorphic_inverse gyrominus_def gyroplus_closed scale_1
      scale_distrib
   using scale_closed by fastforce

lemma proposition16_hatori_abe_p2:
  assumes "z\<in>dom" 
    "fi z = (\<lambda>x. (if x \<in>dom then 2 \<otimes> z \<oplus> (\<ominus> x) else undefined))"
    "isgyrometric q" "a\<in>dom" "b\<in>dom"
  shows "q ((fi z) a) ((fi z) b) = q a b"
  by (metis (full_types) assms(1,2,3,4,5) ax1 gyromid_minus_sym proposition15_hatori_abe
      scale_closed)

lemma help_ha_p3:
  assumes "a\<in>dom"
  "a=\<ominus>a"
shows "a=0\<^sub>g"
proof-
  have "a\<oplus>a = 2\<otimes>a"
    by (metis assms(1) one_add_one scale_1 scale_distrib)
  moreover have "2\<otimes>a = 0\<^sub>g"
    using assms(1,2) calculation gyro_rigth_inv by fastforce
  moreover have "norm' (2\<otimes>a) = 0"
    using assms(1) calculation(2) local.norm_zero scale_closed by blast
  moreover have "norm' (2\<otimes>a)  = 2 * norm' a"
    by (metis add_cancel_left_right assms(1,2) calculation(2,3) eq_3_hatori_abe
        gyro_left_id gyro_right_id gyromid_def mult_not_zero scale_assoc scale_closed
        scale_distrib two_sum two_sum2)
  ultimately show ?thesis
    using assms(1) local.norm_zero by fastforce
qed

lemma proposition16_hatori_abe_p3:
  assumes "z\<in>dom" 
    "fi z = (\<lambda>x. (if x \<in>dom then 2 \<otimes> z \<oplus> (\<ominus> x) else undefined))"
  "a\<in>dom"
shows "(fi z) a = a \<longleftrightarrow> z = a"
proof
  show "fi z a = a \<Longrightarrow> z = a"
  proof-
    assume "fi z a = a"
    show "z = a"
    proof-
      have "\<ominus>z \<oplus> a = \<ominus>z \<oplus> (fi z) (a)"
        using \<open>fi z a = a\<close> by auto
      moreover have "\<ominus>z \<oplus> (fi z) (a) = \<ominus>z \<oplus> (z \<oplus> (z \<oplus> \<ominus> a)) "
        by (smt (verit, ccfv_threshold) assms(1,2,3) ax1 gyr_id gyro_left_assoc scale_1
            scale_distrib)
      moreover have "\<ominus>z \<oplus> a = \<ominus>(\<ominus>z \<oplus> a)"
        using \<open>fi z a = a\<close> assms(1,3) ax1 calculation(2) gyroautomorphic_inverse gyrominus_def
          gyroplus_closed by auto
      moreover have "\<ominus>z \<oplus> a = 0\<^sub>g"
        using assms(1,3) ax1 calculation(3) gyroplus_closed help_ha_p3 by presburger
      ultimately show ?thesis
        by (metis assms(1,3) gyro_right_id oplus_ominus_cancel)
    qed
  qed
next
  show "z = a \<Longrightarrow> fi z a = a"
    by (smt (verit) assms(2,3) scale_1 scale_distrib scale_minus1_inv)
qed

lemma proposition16_hatori_abe_p4:
  assumes "z\<in>dom" 
    "fi z = (\<lambda>x. (if x \<in>dom then 2 \<otimes> z \<oplus> (\<ominus> x) else undefined))"
  "a\<in>dom" "b\<in>dom" "z=gyromid a b"
shows "(fi z) a = b \<and> (fi z) b = a"
proof
  show " fi z a = b"
  proof-
    have "fi z a = 2 \<otimes> z \<oplus> (\<ominus> a)"
      using assms(2,3) by presburger
    moreover have "fi z a = (a \<oplus>\<^sub>c b) \<oplus> \<ominus> a"
    proof-
      have "gyromid a b =  (1/2)\<otimes>(a \<oplus>\<^sub>c b)"
        by (simp add: assms(3,4) gyromid_def)
      moreover have " 2 \<otimes> z \<oplus> (\<ominus> a) = 2\<otimes> ( (1/2)\<otimes>(a \<oplus>\<^sub>c b))  \<oplus> \<ominus> a"
        using assms(5) calculation by presburger
      moreover have "2\<otimes> ( (1/2)\<otimes>(a \<oplus>\<^sub>c b))  = (a \<oplus>\<^sub>c b)"
        by (metis assms(1,3,4,5) ax1 calculation(1) cogyroplus_def field_sum_of_halves
            gyr_def_closed gyroplus_closed mult_1 mult_2_right scale_1 scale_distrib)
      ultimately show ?thesis
        using \<open>fi z a = 2 \<otimes> z \<oplus> \<ominus> a\<close> by argo
    qed
    moreover have "fi z a =(b \<oplus>\<^sub>c a) \<oplus> \<ominus> a"
      using assms(3,4) calculation(2) cogyro_commute by presburger
    moreover have "fi z a = b"
      by (simp add: assms(3,4) ax1 calculation(3) gyr_id_3 mixed_gyroassoc_law)
    ultimately show ?thesis 
      by linarith
  qed
next
  show "fi z b = a"
  proof-
    have "fi z b =  2\<otimes> ( (1/2)\<otimes>(a \<oplus>\<^sub>c b)) \<oplus> \<ominus>b"
      using assms(2,3,4,5) gyromid_def by auto
    moreover have "2\<otimes> ( (1/2)\<otimes>(a \<oplus>\<^sub>c b))  = (a \<oplus>\<^sub>c b)"
       using assms(1,3,4,5) ax1 cogyroplus_def field_sum_of_halves
            gyr_def_closed gyroplus_closed mult_1 mult_2_right scale_1 scale_distrib
       by (smt (verit, del_insts) div_by_1 divide_divide_eq_right scale_assoc
           times_divide_eq_right)
     ultimately show ?thesis 
       by (simp add: assms(3,4) ax1 gyr_id_3 mixed_gyroassoc_law)
  qed
qed

lemma proposition16_hatori_abe_p5:
  assumes "z\<in>dom" 
    "fi z = (\<lambda>x. (if x \<in>dom then 2 \<otimes> z \<oplus> (\<ominus> x) else undefined))"
  "a\<in>dom" "isgyrometric q" 
shows "q ((fi z) (a)) a = otimes' 2 (q a z)"
proof-
  have "(1/2) \<otimes> ((fi z) (a) \<oplus>\<^sub>c a) = (1/2) \<otimes> ((2 \<otimes> z \<oplus> (\<ominus> a))\<oplus>\<^sub>c a)"
    using assms(2,3) by presburger
  moreover have " (1/2) \<otimes> ((2 \<otimes> z \<oplus> (\<ominus> a))\<oplus>\<^sub>c a) = z"
    by (smt (verit, ccfv_threshold) add_divide_distrib assms(1,3) ax1 cogyro_commute
        cogyro_plus_def div_by_1 divide_divide_eq_right field_sum_of_halves gyroplus_closed
        one_add_one oplus_ominus_cancel scale_1 scale_assoc scale_closed two_sum)
  moreover have "gyromid a (fi z a) = z"
    using assms(1,2,3) calculation(2) cogyro_commute gyromid_def gyrominus_closed
      gyrominus_def scale_closed by force
  moreover have "norm' (a\<oplus> \<ominus>z) = otimes' (1/2)  (norm' (a\<oplus> (\<ominus> (fi z a))))"
    by (metis (full_types) assms(1,2,3,4) ax1 calculation(2) cogyro_commute gyroplus_closed
        isgyrometric_def normed_gyrolinear_space''.gyromid_def
        normed_gyrolinear_space''_axioms proposition15_hatori_abe_2_help
        scale_closed)
  ultimately show ?thesis 
    by (smt (verit, del_insts) assms(1,2,3,4) ax1 gyr_commute_misc_3 gyro_inv_idem
        gyromid_minus_sym gyroplus_closed isgyrometric_def norm_gyr norm_scale scale_closed
        two_sum)
qed


end


lemma Sup_image_mono_isCont:
  fixes X :: "real set" and f :: "real \<Rightarrow> real"
  assumes Xne: "X \<noteq> {}" and bdd: "bdd_above X"
  assumes mono: "\<And>x y. ((x::real) \<le> (y::real)) \<Longrightarrow> f x \<le> f y"
  assumes cont: "continuous (at (Sup X)) f"
  shows "Sup (f ` X) = f (Sup X)"
proof (rule antisym)
  (*  Sup (f`X) \<le> f (Sup X)  *)
  have ubX: "\<And>x. x \<in> X \<Longrightarrow> f x \<le> f (Sup X)"
  proof -
    fix x assume "x \<in> X"
    hence "x \<le> Sup X" using Xne bdd
      using cSup_upper by blast
    with mono show "f x \<le> f (Sup X)" 
      by blast
  qed
  have fX_ne: "f ` X \<noteq> {}" using Xne by auto
  have bdd_fX: "bdd_above (f ` X)"
    by (rule bdd_aboveI[of _ "f (Sup X)"]) (use ubX in auto)            (* :contentReference[oaicite:1]{index=1} *)
  have "Sup (f ` X) \<le> f (Sup X)"
    using fX_ne bdd_fX ubX by (simp add: cSup_le_iff image_iff)         (* :contentReference[oaicite:2]{index=2} *)
  thus "Sup (f ` X) \<le> f (Sup X)" .

  (*  f (Sup X) \<le> Sup (f`X)  *)
  have "f (Sup X) \<le> Sup (f ` X)"
    
  proof -                (* :contentReference[oaicite:3]{index=3} *)
    
    {
      fix y 
      assume ylt: "y < f (Sup X)"
    define \<epsilon> where "\<epsilon> = f (Sup X) - y"
    have "\<epsilon> > 0" using ylt by (simp add: \<epsilon>_def)
    from cont have contE:
      "\<forall>e>0. \<exists>\<delta>>0. \<forall>t. dist t (Sup X) < \<delta> \<longrightarrow> dist (f t) (f (Sup X)) < e"
      (*using continuous_at_eps_delta*)
      by (metis LIM_def dist_self isCont_def)
         (* :contentReference[oaicite:4]{index=4} *)
    obtain \<delta> where \<delta>pos: "\<delta>>0" and \<delta>: "\<forall>t. dist t (Sup X) < \<delta> \<longrightarrow> dist (f t) (f (Sup X)) < \<epsilon>"
      using contE `\<epsilon>>0` by blast
    (* by definition of Sup there is x\<in>X with Sup X - \<delta> < x *)
    have "Sup X - \<delta> < Sup X" using \<delta>pos by simp
    then obtain x where xX: "x \<in> X" and near: "Sup X - \<delta> < x"
      using Xne bdd le_cSup_iff[OF Xne bdd, of "Sup X"] 
      by blast
    have "dist x (Sup X) < \<delta>" using near \<delta>pos
      by (smt (verit) Xne bdd dist_norm le_cSup_iff real_norm_def xX)
    hence "dist (f x) (f (Sup X)) < \<epsilon>" using \<delta> by blast
    hence "y < f x"
      by (simp add: \<epsilon>_def dist_real_def abs_less_iff)
    then have  "\<exists>a\<in>f ` X. y < a" using xX 
      
      by auto
  } 
  then have "\<forall>y. y < f (Sup X) \<longrightarrow> (\<exists>a\<in>f ` X. y < a)"
    by fastforce
  then show ?thesis
    by (meson bdd_fX cSup_upper linorder_not_less)
  qed
  then show "f (Sup X) \<le> Sup (f ` X)" 
    by meson
qed


lemma mazur_ulam_inj:
  fixes dom1::"'a set" 
  fixes dom2::"'b set"
  fixes T::"'a\<Rightarrow>'b"
  assumes "normed_gyrolinear_space'' dom2 gyrozero2 gyroplus2 gyroinv2 gyr2 scale2 norm'2 oplus'2 otimes'2"
  "normed_gyrolinear_space'' dom1 gyrozero1 gyroplus1 gyroinv1 gyr1 scale1 norm'1 oplus'1 otimes'1"
   "T ` dom1 = dom2" 
  "normed_gyrolinear_space''.isgyrometric dom2 gyroplus2 gyroinv2 norm'2  q2"
  "normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1  q1"
  "\<forall>a\<in>dom1. \<forall>b\<in>dom1. q2 (T a) (T b) = q1 a b"
  "\<exists>x\<in>dom1. x\<noteq>gyrozero1"
"(\<forall>y\<in>dom2. \<exists>x\<in>dom1. T x = y)"
shows  "inj_on T dom1"
proof-
     have "\<forall>x\<in>dom1. \<forall>y\<in>dom1. (T x = T y \<longrightarrow> x=y)"
     proof
                       fix x
                       assume "x\<in>dom1"
                       show " \<forall>y\<in>dom1. (T x = T y \<longrightarrow> x=y)"
                       proof
                         fix y
                         assume "y\<in>dom1"
                         show " T x = T y \<longrightarrow> x=y"
                         proof-
                           { assume "T x = T y"
                             have "x=y"
                           proof-
                             have "q2 (T x) (T y) = q1 x y"
                               using \<open>x \<in> dom1\<close> \<open>y \<in> dom1\<close> assms(6) by fastforce
                             moreover have "q2 (T x) (T y) = 0"
                               using normed_gyrolinear_space''.gyrom_id[OF assms(1)]
                               
                               by (metis \<open>T x = T y\<close> \<open>x \<in> dom1\<close> assms(2,5,6)
                                   normed_gyrolinear_space''.gyrom_id)
                             ultimately show ?thesis 
                               using normed_gyrolinear_space''.gyrom_id2[OF assms(2)]
                            
                               using \<open>x \<in> dom1\<close> \<open>y \<in> dom1\<close> assms(5) by presburger
                               
                           qed} then have " T x = T y \<Longrightarrow> x = y "
                          
                           by fastforce
 then show ?thesis 
   by blast
qed
qed
qed
  then show ?thesis 
    by (simp add: inj_on_def)
qed




lemma mazur_ulam_help1:
  fixes dom1::"'a set" 
  fixes dom2::"'b set"
  fixes T::"'a\<Rightarrow>'b"
  fixes a::'a
  fixes b::'a
  assumes "normed_gyrolinear_space'' dom2 gyrozero2 gyroplus2 gyroinv2 gyr2 scale2 norm'2 oplus'2 otimes'2"
  "normed_gyrolinear_space'' dom1 gyrozero1 gyroplus1 gyroinv1 gyr1 scale1 norm'1 oplus'1 otimes'1"
   "T ` dom1 = dom2" 
  "normed_gyrolinear_space''.isgyrometric dom2 gyroplus2 gyroinv2 norm'2  q2"
  "normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1  q1"
  "a\<in>dom1" "b\<in>dom1"
  "\<forall>a\<in>dom1. \<forall>b\<in>dom1. q2 (T a) (T b) = q1 a b"
  "\<exists>x\<in>dom2. x\<noteq>gyrozero2"
"(\<forall>y\<in>dom2. \<exists>x\<in>dom1. T x = y)"
"p = normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b"
  " p' = normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a)
             (T b)"
   "phi_p = (\<lambda>x. (if x \<in> dom1 then gyroplus1 (scale1 2 p) (gyroinv1 x) else undefined))"
    "phi_p' = (\<lambda>x. (if x \<in> dom2 then gyroplus2 (scale2 2 p') (gyroinv2 x) else undefined))"
     "S = (phi_p \<circ>(inv_into dom1 T)\<circ>phi_p' \<circ> T)"
   shows  "S ` dom1 = dom1 \<and> (phi_p' \<circ> T) ` dom1 = dom2 \<and> ((inv_into dom1 T)\<circ> phi_p' \<circ> T) ` dom1 = dom1"
proof-
  have "inj_on T dom1"
    
   
    by (metis (mono_tags, opaque_lifting) assms(2,5,8) inj_onCI
        normed_gyrolinear_space''.gyrom_id normed_gyrolinear_space''.gyrom_id2)
  moreover    have " T ` dom1 = dom2 "
          using assms(3) by blast
        moreover have "(phi_p' \<circ> T) ` dom1 = dom2"
        proof-
          have "\<forall>x\<in>dom1. ((phi_p' \<circ> T) x) \<in> dom2"
          proof
            fix x 
            assume "x\<in>dom1"
            show "((phi_p' \<circ> T) x) \<in> dom2"
            proof-
              have "T x \<in> dom2"
                using \<open>x \<in> dom1\<close> calculation by blast
              moreover have "phi_p' (T x) \<in> dom2"
              proof-
                have "phi_p' (T x) = gyroplus2 (scale2 2 p') (gyroinv2 (T x))"
                  
                
                  using assms(14) calculation by presburger
                moreover have "(gyroinv2 (T x))\<in>dom2"
                  
                  by (metis \<open>T x \<in> dom2\<close> assms(1) gyrolinear_space.scale_closed
                      gyrolinear_space.scale_minus1_inv normed_gyrolinear_space''_def)
                moreover have "p'\<in>dom2"
                  
                  by (metis assms(1,12,3,6,7) imageI normed_gyrolinear_space''.gyromid_in_domain)
                moreover have "(scale2 (2::real) p')\<in>dom2"
                  
                  by (meson assms(1) calculation(3) gyrolinear_space.scale_closed
                      normed_gyrolinear_space''_def)
                ultimately show ?thesis
                  
                  by (metis assms(1) gyrocommutative_gyrogroup_def gyrogroup_def
                      gyrogroupoid.gyroplus_closed gyrolinear_space_def
                      normed_gyrolinear_space''_def)
              qed
              ultimately show ?thesis
                by fastforce
            qed
          qed
          moreover have "\<forall>x\<in>dom2. \<exists>y\<in>dom1. ((phi_p' \<circ> T) y) = x"
          proof
            fix x
            assume "x\<in>dom2"
            show " \<exists>y\<in>dom1. ((phi_p' \<circ> T) y) = x"
            proof-
              obtain "y" where "y = ((inv_into dom1 T) \<circ> phi_p') x "
                by blast
              moreover have " ((phi_p' \<circ> T) y) =  ((phi_p' \<circ> T) (((inv_into dom1 T) \<circ> phi_p') x))"
                using calculation by force
              moreover have "(T \<circ> (inv_into dom1 T)) (phi_p' x) = (phi_p' x)"
                
                by (metis \<open>\<forall>x\<in>dom1. (phi_p' \<circ> T) x \<in> dom2\<close> \<open>x \<in> dom2\<close> assms(10,3) comp_apply
                    f_inv_into_f)
               
               moreover have "p' \<in>dom2"
            
              
                 by (metis assms(1,12,3,6,7) imageI normed_gyrolinear_space''.gyromid_in_domain)
                  moreover have "\<forall>z\<in>dom2. (phi_p' \<circ> phi_p') z = z"
                  proof 
                    fix z
                    assume "z\<in>dom2"
                    show "(phi_p' \<circ> phi_p') z = z"
                      using normed_gyrolinear_space''.proposition16_hatori_abe_p1_v2[OF assms(1) `p' \<in>dom2`]
                
                      
                      by (simp add: \<open>z \<in> dom2\<close> assms(14))
                    
                   
                
                  qed
              moreover have "phi_p' (phi_p' x) = x"
             
                using \<open>x \<in> dom2\<close> calculation(5) by fastforce
              ultimately show ?thesis 
                
                by (metis \<open>\<forall>x\<in>dom1. (phi_p' \<circ> T) x \<in> dom2\<close> \<open>x \<in> dom2\<close> assms(10) comp_apply)
              
            qed
          qed 
          moreover have "(phi_p' \<circ> T) ` dom1 \<subseteq> dom2"
          
            using calculation(1) by blast
          moreover have "dom2 \<subseteq>(phi_p' \<circ> T) ` dom1 "
            
            using calculation(2) by fastforce
          ultimately show ?thesis by fastforce
        qed
          moreover have "((inv_into dom1 T)\<circ> phi_p' \<circ> T) ` dom1 = dom1"
          proof-
               have *:"\<forall>x\<in>dom1. ((inv_into dom1 T)\<circ>phi_p' \<circ> T) x\<in> dom1"
             
                 by (metis calculation(2,3) comp_apply imageI inv_into_into)
              
               moreover have "\<forall>x\<in>dom1. \<exists>y\<in>dom1. (((inv_into dom1 T)\<circ> phi_p' \<circ> T) y) = x"
                 
          
                 by (metis \<open>(phi_p' \<circ> T) ` dom1 = dom2\<close> \<open>inj_on T dom1\<close> assms(3) image_comp image_iff
                     inv_into_f_f)
              
               moreover have "((inv_into dom1 T)\<circ> phi_p' \<circ> T) ` dom1 \<subseteq> dom1"
                 using calculation(1) by blast
               moreover have "dom1 \<subseteq> ((inv_into dom1 T)\<circ> phi_p' \<circ> T) ` dom1"
               
                 using calculation(2) by fastforce
               ultimately show ?thesis 
                 by fastforce
             qed
             moreover have "( phi_p \<circ> (inv_into dom1 T)\<circ> phi_p' \<circ> T) ` dom1 = dom1"
             proof-
               have "\<forall>x\<in>dom1. ( phi_p \<circ> (inv_into dom1 T)\<circ> phi_p' \<circ> T) x \<in> dom1"
               proof
                 fix x 
                 assume "x\<in>dom1"
                 show " ( phi_p \<circ> (inv_into dom1 T)\<circ> phi_p' \<circ> T) x \<in> dom1"
                 proof-
                   have "  ((inv_into dom1 T)\<circ> phi_p' \<circ> T) x \<in> dom1"
                    
                     
                     
                     using \<open>x \<in> dom1\<close> calculation(4) by blast
                   moreover have "phi_p ( ((inv_into dom1 T)\<circ> phi_p' \<circ> T) x) =
   gyroplus1 (scale1 2 p) (gyroinv1 ( ((inv_into dom1 T)\<circ> phi_p' \<circ> T) x))"
                     
                     
                     using assms(13) calculation by presburger
                   moreover have "(gyroinv1 ( ((inv_into dom1 T)\<circ> phi_p' \<circ> T) x))\<in>dom1"
                   
                     by (metis (no_types, lifting) assms(2) calculation(1) gyrolinear_space.scale_closed
                         gyrolinear_space.scale_minus1_inv normed_gyrolinear_space''_def)
                   moreover have "(scale1 2 p)\<in>dom1"
               
                     
                     by (metis assms(11,2,6,7) gyrolinear_space.scale_closed
                         normed_gyrolinear_space''.gyromid_in_domain normed_gyrolinear_space''_def)
                   moreover have "gyroplus1 (scale1 2 p) (gyroinv1 ( ((inv_into dom1 T)\<circ> phi_p' \<circ> T) x))\<in>dom1"
                 
                     using assms(2) calculation(3,4) gyrocommutative_gyrogroup_def gyrogroup_def
                       gyrogroupoid.gyroplus_closed gyrolinear_space_def normed_gyrolinear_space''_def
                     by fastforce
                   ultimately show ?thesis 
                     by auto
                     
                 qed
               qed
               moreover  have "\<forall>x\<in>dom1. \<exists>y\<in>dom1. ((phi_p\<circ>(inv_into dom1 T)\<circ> phi_p' \<circ> T) y) = x"
               proof
                 fix x 
                 assume "x\<in>dom1"
                 show "\<exists>y\<in>dom1. ((phi_p\<circ>(inv_into dom1 T)\<circ> phi_p' \<circ> T) y) = x"
                 proof-
                     have "\<forall>x\<in>dom1. \<exists>y\<in>dom1. (((inv_into dom1 T)\<circ> phi_p' \<circ> T) y) = x"
                    
                       by (metis \<open>(inv_into dom1 T \<circ> phi_p' \<circ> T) ` dom1 = dom1\<close> image_iff)
               moreover obtain "t" where "t=phi_p x"
               
                 by auto
               moreover obtain "t2" where "((inv_into dom1 T)\<circ> phi_p' \<circ> T)  t2 = phi_p x"
                 
                 
                 by (metis \<open>\<forall>x\<in>dom1. (phi_p \<circ> inv_into dom1 T \<circ> phi_p' \<circ> T) x \<in> dom1\<close> \<open>x \<in> dom1\<close>
                     calculation(1) comp_eq_dest_lhs)
                 moreover have "p \<in>dom1"
            
        
                  
                   by (metis assms(11,2,6,7) normed_gyrolinear_space''.gyromid_in_domain)
                 moreover have "\<forall>z\<in>dom1. (phi_p \<circ> phi_p) z = z"
                   
                  proof 
                    fix z
                    assume "z\<in>dom1"
                    show "(phi_p \<circ> phi_p) z = z"
                      using normed_gyrolinear_space''.proposition16_hatori_abe_p1_v2[OF assms(2) `p\<in>dom1`]
                
                   
                      by (simp add: \<open>z \<in> dom1\<close> assms(13))
                    
                   
                
                  qed
                  ultimately show ?thesis
                    
                    by (metis \<open>\<forall>x\<in>dom1. (phi_p \<circ> inv_into dom1 T \<circ> phi_p' \<circ> T) x \<in> dom1\<close> \<open>x \<in> dom1\<close>
                        comp_apply)
                qed
              qed
              moreover have "( phi_p \<circ> (inv_into dom1 T)\<circ> phi_p' \<circ> T) ` dom1 \<subseteq> dom1"
               
                using calculation(1) by blast
              moreover have "dom1 \<subseteq>( phi_p \<circ> (inv_into dom1 T)\<circ> phi_p' \<circ> T) ` dom1 "
                
                using calculation(2) by fastforce
              ultimately show ?thesis 
                by fastforce
             qed
                  
         
           ultimately show ?thesis 
            
            
             using assms(15) by fastforce
qed

lemma mazur_ulam_help1_1:
  fixes dom1::"'a set" 
  fixes dom2::"'b set"
  fixes T::"'a\<Rightarrow>'b"
  fixes a::'a
  fixes b::'a
  assumes "normed_gyrolinear_space'' dom2 gyrozero2 gyroplus2 gyroinv2 gyr2 scale2 norm'2 oplus'2 otimes'2"
  "normed_gyrolinear_space'' dom1 gyrozero1 gyroplus1 gyroinv1 gyr1 scale1 norm'1 oplus'1 otimes'1"
   "T ` dom1 = dom2" 
  "normed_gyrolinear_space''.isgyrometric dom2 gyroplus2 gyroinv2 norm'2  q2"
  "normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1  q1"
  "a\<in>dom1" "b\<in>dom1"
  "\<forall>a\<in>dom1. \<forall>b\<in>dom1. q2 (T a) (T b) = q1 a b"
  "\<exists>x\<in>dom2. x\<noteq>gyrozero2"
"(\<forall>y\<in>dom2. \<exists>x\<in>dom1. T x = y)"
"p = normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b"
  " p' = normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a)
             (T b)"
   "phi_p = (\<lambda>x. (if x \<in> dom1 then gyroplus1 (scale1 2 p) (gyroinv1 x) else undefined))"
    "phi_p' = (\<lambda>x. (if x \<in> dom2 then gyroplus2 (scale2 2 p') (gyroinv2 x) else undefined))"
     "S = (phi_p \<circ>(inv_into dom1 T)\<circ>phi_p' \<circ> T)"
   shows  "(\<forall>x\<in>dom1. S x \<in> dom1)
 \<and> (\<forall>x\<in>dom1. (phi_p' \<circ> T) x \<in> dom2)
 \<and> (\<forall>x\<in>dom1. ((inv_into dom1 T)\<circ> phi_p' \<circ> T) x\<in> dom1)"
  using mazur_ulam_help1[OF assms]
  by blast
lemma mazur_ulam_help2:
  fixes dom1::"'a set" 
  fixes dom2::"'b set"
  fixes T::"'a\<Rightarrow>'b"
  fixes a::'a
  fixes b::'a
  assumes "normed_gyrolinear_space'' dom2 gyrozero2 gyroplus2 gyroinv2 gyr2 scale2 norm'2 oplus'2 otimes'2"
  "normed_gyrolinear_space'' dom1 gyrozero1 gyroplus1 gyroinv1 gyr1 scale1 norm'1 oplus'1 otimes'1"
   "T ` dom1 = dom2" 
  "normed_gyrolinear_space''.isgyrometric dom2 gyroplus2 gyroinv2 norm'2  q2"
  "normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1  q1"
  "a\<in>dom1" "b\<in>dom1"
  "\<forall>a\<in>dom1. \<forall>b\<in>dom1. q2 (T a) (T b) = q1 a b"
  "\<exists>x\<in>dom2. x\<noteq>gyrozero2"
"(\<forall>y\<in>dom2. \<exists>x\<in>dom1. T x = y)"
"p = normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b"
  " p' = normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a)
             (T b)"
   "phi_p = (\<lambda>x. (if x \<in> dom1 then gyroplus1 (scale1 2 p) (gyroinv1 x) else undefined))"
    "phi_p' = (\<lambda>x. (if x \<in> dom2 then gyroplus2 (scale2 2 p') (gyroinv2 x) else undefined))"
     "S = (phi_p \<circ>(inv_into dom1 T)\<circ>phi_p' \<circ> T)"
   shows "\<forall>n::nat. \<forall>x\<in>dom1. (S^^n) x \<in> dom1"
proof
  fix n 
  show " \<forall>x\<in>dom1. (S^^n) x \<in> dom1"
  proof (induction n)
    case 0
    then show ?case 
      by force
  next
    case (Suc n)
    moreover have " \<forall>x\<in>dom1. (S ^^ (n+1)) x = S ((S^^n) x)"
      by fastforce
    moreover have " \<forall>x\<in>dom1. ((S^^n) x) \<in> dom1"
      using Suc by blast
    moreover have "S ` dom1 = dom1"
      using mazur_ulam_help1[OF assms]
      by meson
    moreover have "\<forall>y\<in>dom1. S y \<in> dom1"
      using calculation(4) by blast
    ultimately show ?case 
      by fastforce
  qed
qed



lemma mazur_ulam_help3:
  fixes dom1::"'a set" 
  fixes dom2::"'b set"
  fixes T::"'a\<Rightarrow>'b"
  fixes a::'a
  fixes b::'a
  assumes "normed_gyrolinear_space'' dom2 gyrozero2 gyroplus2 gyroinv2 gyr2 scale2 norm'2 oplus'2 otimes'2"
  "normed_gyrolinear_space'' dom1 gyrozero1 gyroplus1 gyroinv1 gyr1 scale1 norm'1 oplus'1 otimes'1"
   "T ` dom1 = dom2" 
  "normed_gyrolinear_space''.isgyrometric dom2 gyroplus2 gyroinv2 norm'2  q2"
  "normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1  q1"
  "a\<in>dom1" "b\<in>dom1"
  "\<forall>a\<in>dom1. \<forall>b\<in>dom1. q2 (T a) (T b) = q1 a b"
  "\<exists>x\<in>dom2. x\<noteq>gyrozero2"
"(\<forall>y\<in>dom2. \<exists>x\<in>dom1. T x = y)"
"p = normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b"
  " p' = normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a)
             (T b)"
   "phi_p = (\<lambda>x. (if x \<in> dom1 then gyroplus1 (scale1 2 p) (gyroinv1 x) else undefined))"
    "phi_p' = (\<lambda>x. (if x \<in> dom2 then gyroplus2 (scale2 2 p') (gyroinv2 x) else undefined))"
     "S = (phi_p \<circ>(inv_into dom1 T)\<circ>phi_p' \<circ> T)"
   shows "S a = a \<and> S b = b "
proof-
  have "inj_on T dom1"
 
    by (metis (mono_tags, opaque_lifting) assms(2,5,8) inj_onI
        normed_gyrolinear_space''.gyrom_id normed_gyrolinear_space''.gyrom_id2)
 
  moreover     have "S a = a"
        proof-
          have "p' \<in> dom2"
         
            by (metis assms(1,12,3,6,7) imageI normed_gyrolinear_space''.gyromid_in_domain)
          moreover have "phi_p' (T a)  = (T b)"
            using normed_gyrolinear_space''.proposition16_hatori_abe_p4[OF assms(1) `p'\<in>dom2`]
          
            using assms(12,14,3,6,7) by fastforce
          moreover have "(inv_into dom1 T) (phi_p' (T a)) =  (inv_into dom1 T) (T b)"
            using calculation(2) by argo
          moreover have "(inv_into dom1 T) (phi_p' (T a)) = b"
            by (simp add: \<open>b \<in> dom1\<close> \<open>inj_on T dom1\<close> calculation(2))
          moreover have "p \<in> dom1"
            
            by (metis assms(11,2,6,7) normed_gyrolinear_space''.gyromid_in_domain)
          moreover have "phi_p b = a"
    using normed_gyrolinear_space''.proposition16_hatori_abe_p4[OF assms(2) `p\<in>dom1`]
            
            by (simp add: assms(11,13,6,7))
          ultimately show ?thesis 
            
            using assms(15) by force
        qed
        moreover have "S b = b"
        proof-
          have "p' \<in> dom2"
          
            by (metis assms(1,12,3,6,7) imageI normed_gyrolinear_space''.gyromid_in_domain)
          moreover have "phi_p' (T b)  = (T a)"
            using normed_gyrolinear_space''.proposition16_hatori_abe_p4[OF assms(1) `p'\<in>dom2`]
       
            using assms(12,14,3,6,7) by fastforce
          moreover have "(inv_into dom1 T) (phi_p' (T b)) =  (inv_into dom1 T) (T a)"
            using calculation(2) by argo
          moreover have "(inv_into dom1 T) (phi_p' (T b)) = a"
            by (simp add: \<open>a \<in> dom1\<close> \<open>inj_on T dom1\<close> calculation(2))
          moreover have "p \<in> dom1"
         
            by (metis assms(11,2,6,7) normed_gyrolinear_space''.gyromid_in_domain)
          moreover have "phi_p a = b"
            using normed_gyrolinear_space''.proposition16_hatori_abe_p4[OF assms(2) `p\<in>dom1`]
            
            by (simp add: assms(11,13,6,7))
          ultimately show ?thesis 
         
            using assms(15) by force
        qed
      
        ultimately show ?thesis 
          
          by fastforce
      qed



lemma mazur_ulam_help3_1:
  fixes dom1::"'a set" 
  fixes dom2::"'b set"
  fixes T::"'a\<Rightarrow>'b"
  fixes a::'a
  fixes b::'a
  assumes "normed_gyrolinear_space'' dom2 gyrozero2 gyroplus2 gyroinv2 gyr2 scale2 norm'2 oplus'2 otimes'2"
  "normed_gyrolinear_space'' dom1 gyrozero1 gyroplus1 gyroinv1 gyr1 scale1 norm'1 oplus'1 otimes'1"
   "T ` dom1 = dom2" 
  "normed_gyrolinear_space''.isgyrometric dom2 gyroplus2 gyroinv2 norm'2  q2"
  "normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1  q1"
  "a\<in>dom1" "b\<in>dom1"
  "\<forall>a\<in>dom1. \<forall>b\<in>dom1. q2 (T a) (T b) = q1 a b"
  "\<exists>x\<in>dom2. x\<noteq>gyrozero2"
"(\<forall>y\<in>dom2. \<exists>x\<in>dom1. T x = y)"
"p = normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b"
  " p' = normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a)
             (T b)"
   "phi_p = (\<lambda>x. (if x \<in> dom1 then gyroplus1 (scale1 2 p) (gyroinv1 x) else undefined))"
    "phi_p' = (\<lambda>x. (if x \<in> dom2 then gyroplus2 (scale2 2 p') (gyroinv2 x) else undefined))"
     "S = (phi_p \<circ>(inv_into dom1 T)\<circ>phi_p' \<circ> T)"
   shows "(\<forall>n::nat. (S^^n) a = a) \<and> (\<forall>n::nat. (S^^n) b = b) "
proof- 
  have "(\<forall>n::nat. (S^^n) a = a)"
proof
  fix n
  show " (S^^n) a = a "
  proof (induction n)
    case 0
    then show ?case 
      by auto
  next
    case (Suc n)
    moreover have "(S^^(n+1)) a = S ((S^^n) a)"
      
      by auto
    moreover have "((S^^n) a) = a"  
      using Suc by blast
    moreover have "S a = a"
      using  mazur_ulam_help3[OF assms]
      
      by blast
    ultimately show ?case 
      using Suc_eq_plus1 by presburger
  qed
qed
 moreover have "(\<forall>n::nat. (S^^n) b = b)"
proof
  fix n
  show " (S^^n) b = b "
  proof (induction n)
    case 0
    then show ?case 
      by auto
  next
    case (Suc n)
    moreover have "(S^^(n+1)) b = S ((S^^n) b)"
      
      by auto
    moreover have "((S^^n) b) = b"  
      using Suc by blast
    moreover have "S b = b"
      using  mazur_ulam_help3[OF assms]
      
      by blast
    ultimately show ?case 
      using Suc_eq_plus1 by presburger
  qed
qed
  ultimately show ?thesis 
    by blast
qed


lemma mazur_ulam_sameG_6_1:
  fixes dom1::"'a set" 
  fixes T::"'a\<Rightarrow>'a"
  fixes a::'a
  fixes b::'a
  assumes 
  "normed_gyrolinear_space'' dom1 gyrozero1 gyroplus1 gyroinv1 gyr1 scale1 norm'1 oplus'1 otimes'1"
   "T ` dom1 = dom1" 
  "normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1  q1"
  "\<forall>a\<in>dom1. \<forall>b\<in>dom1. q1 (T a) (T b) = q1 a b"
  "\<exists>x\<in>dom1. x\<noteq>gyrozero1"
"(\<forall>y\<in>dom1. \<exists>x\<in>dom1. T x = y)"
  "a\<in>dom1" "b\<in>dom1"
"p = normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b"
  " p' = normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a)
             (T b)"
   "phi_p = (\<lambda>x. (if x \<in> dom1 then gyroplus1 (scale1 2 p) (gyroinv1 x) else undefined))"
    "phi_p' = (\<lambda>x. (if x \<in> dom1 then gyroplus1 (scale1 2 p') (gyroinv1 x) else undefined))"
     "S = (phi_p \<circ>(inv_into dom1 T)\<circ>phi_p' \<circ> T)"
shows "\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((phi_p \<circ> S)x) y =  q1 (phi_p x) (S y)"
proof-
                have A1:"\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((phi_p \<circ> S)x) y = q1 (((inv_into dom1 T)\<circ>phi_p' \<circ> T) x) y"
                proof
                  fix x
                  assume "x\<in>dom1"
                  show  "\<forall>y\<in>dom1. q1 ((phi_p \<circ> S)x) y = q1 (((inv_into dom1 T)\<circ>phi_p' \<circ> T) x) y"
                  proof
                    fix y 
                    assume "y\<in>dom1"
                    show " q1 ((phi_p \<circ> S)x) y = q1 (((inv_into dom1 T)\<circ>phi_p' \<circ> T) x) y"
                  proof-
                  have " phi_p = (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 p) (gyroinv1 x) else undefined)"
                    
                    by (simp add: assms(11))
                  moreover have "p \<in>dom1"
                   
                    by (metis assms(1,7,8,9) normed_gyrolinear_space''.gyromid_in_domain)
                    
                  moreover have "\<forall>z\<in>dom1. (phi_p \<circ> phi_p) z = z"
                  proof 
                    fix z
                    assume "z\<in>dom1"
                    show "(phi_p \<circ> phi_p) z = z"
                      using normed_gyrolinear_space''.proposition16_hatori_abe_p1_v2[OF assms(1)]             
                
                      by (simp add: \<open>z \<in> dom1\<close> calculation(1,2))
                     
                  qed
                  moreover have "(((inv_into dom1 T)\<circ>phi_p' \<circ> T) x)\<in>dom1"
                    using mazur_ulam_help1_1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of p p' phi_p phi_p' S, OF assms(9), OF assms(10) assms(11) assms(12)]
                    
                    using \<open>x \<in> dom1\<close> assms(13) by fastforce
                  ultimately show ?thesis 
                  
                  
                    by (simp add: assms(13) comp_def)
                qed
              qed
            qed
               moreover have A2:"\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 (((inv_into dom1 T)\<circ>phi_p' \<circ> T) x) y = q1 x (((inv_into dom1 T)\<circ>phi_p' \<circ> T) y)"
               proof
                 fix x
                 assume "x\<in>dom1"
                 show "\<forall>y\<in>dom1. q1 (((inv_into dom1 T)\<circ>phi_p' \<circ> T) x) y = q1 x (((inv_into dom1 T)\<circ>phi_p' \<circ> T) y)"
                 proof
                   fix y
                   assume "y\<in>dom1"
                   show " q1 (((inv_into dom1 T)\<circ>phi_p' \<circ> T) x) y = q1 x (((inv_into dom1 T)\<circ>phi_p' \<circ> T) y)"
                   proof-
                    have "(((inv_into dom1 T)\<circ>phi_p' \<circ> T) x)\<in>dom1"
                    using mazur_ulam_help1_1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of p p' phi_p]
                 
                    by (simp add: \<open>x \<in> dom1\<close> assms(10,11,12,9))
                     have "q1 (((inv_into dom1 T)\<circ>phi_p' \<circ> T) x) y  = q1 (T(((inv_into dom1 T)\<circ>phi_p' \<circ> T) x)) (T y)"
                       using assms
                       
                       
                       using \<open>(inv_into dom1 T \<circ> phi_p' \<circ> T) x \<in> dom1\<close> \<open>y \<in> dom1\<close> by force
                     moreover have "inj_on T dom1"
                     by (metis (mono_tags, opaque_lifting) assms(1,3,4) inj_onCI
                           normed_gyrolinear_space''.gyrom_id normed_gyrolinear_space''.gyrom_id2)
                     moreover have "((phi_p' \<circ> T) x)\<in>dom1"
                       using mazur_ulam_help1_1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of p p' phi_p]
                       
                       using \<open>x \<in> dom1\<close> assms(10,11,12,9) by blast
                       moreover have " q1 (T(((inv_into dom1 T)\<circ>phi_p' \<circ> T) x)) (T y) =  q1 ((phi_p' \<circ> T) x) (T y)"
                         
                         by (metis (lifting) assms(2) calculation(3) comp_apply f_inv_into_f)
                         
                        (* by (smt (verit) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> \<open>x \<in> dom1\<close> assms(1,3) comp_apply f_inv_into_f
                             gyrocommutative_gyrogroup_def gyrogroup.ax1 gyrogroup_def gyrogroupoid.gyroplus_closed
                             gyrolinear_space.scale_closed gyrolinear_space_def imageI
                             normed_gyrolinear_space''.gyromid_in_domain normed_gyrolinear_space''_def)
                   *)
                  moreover have "p' \<in> dom1"
                 
                    by (metis assms(1,10,2,7,8) imageI normed_gyrolinear_space''.gyromid_in_domain)
                  moreover have "T y \<in>dom1"
                  
                    using \<open>y \<in> dom1\<close> assms(2) by blast
                  moreover have " q1 ((phi_p' \<circ> T) x) (T y) =  q1 ((phi_p'\<circ>(phi_p' \<circ> T)) x) ((phi_p' \<circ> T) y)"
                    using normed_gyrolinear_space''.proposition16_hatori_abe_p2[OF assms(1) `p' \<in>dom1`, of "\<lambda>y. (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 y) (gyroinv1 x) else undefined)"]
                   `((phi_p' \<circ> T) x)\<in>dom1` `T y \<in>dom1`
                    
                    using assms(12,3) by force
                  moreover have " q1 ((phi_p'\<circ>(phi_p' \<circ> T)) x) ((phi_p' \<circ> T) y) = q1 (((inv_into dom1 T)\<circ> T)x) (((inv_into dom1 T)\<circ>(phi_p' \<circ> T)) y)"
                    
                  proof-

                  have "p' \<in>dom1"
                    
                    using calculation(5) by force
                  moreover have "\<forall>z\<in>dom1. (phi_p' \<circ> phi_p') z = z"
                   proof 
                    fix z
                    assume "z\<in>dom1"
                    show "(phi_p' \<circ> phi_p') z = z"
                      using normed_gyrolinear_space''.proposition16_hatori_abe_p1_v2[OF assms(1)     `p'\<in>dom1`  ]             
                  
                    
                      by (simp add: \<open>z \<in> dom1\<close> assms(12))
                     
                
                  qed
                   moreover have "((phi_p'\<circ>(phi_p' \<circ> T)) x) = T x"
                 
                     using \<open>x \<in> dom1\<close> assms(2) calculation(2) by auto

                   moreover have "q1 ((phi_p'\<circ>(phi_p' \<circ> T)) x) ((phi_p' \<circ> T) y) = q1 (T x) ((phi_p' \<circ> T) y)"
                     using calculation(3) by presburger
                   moreover have "inj_on T dom1"
                     using mazur_ulam_inj
                    
                     using \<open>inj_on T dom1\<close> by force
                   moreover have "((inv_into dom1 T) \<circ> T) x = x"
                
                     by (simp add: \<open>x \<in> dom1\<close> calculation(5))
                   moreover have "q1 (T x) ((phi_p' \<circ> T) y) = q1 ((inv_into dom1 T) (T x)) ((inv_into dom1 T)(((phi_p' \<circ> T) y)))"
                   proof-
                     have "(inv_into dom1 T) (T x)\<in> dom1"
                     
                       using \<open>x \<in> dom1\<close> calculation(6) by fastforce
                     moreover have "(inv_into dom1 T)(((phi_p' \<circ> T) y))\<in>dom1"
using mazur_ulam_help1_1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of p p' phi_p]
                 
                       
                       by (simp add: \<open>y \<in> dom1\<close> assms(10,11,12,9))
                     
                     have "q1 ((inv_into dom1 T) (T x)) ((inv_into dom1 T)(((phi_p' \<circ> T) y))) =
                  q1 (T((inv_into dom1 T) (T x))) (T((inv_into dom1 T)(((phi_p' \<circ> T) y))))"
                       using assms(4)
                       
                       using \<open>inv_into dom1 T ((phi_p' \<circ> T) y) \<in> dom1\<close> calculation by force
                     moreover have    "p \<in> dom1"
                     
                       by (metis assms(1,7,8,9) normed_gyrolinear_space''.gyromid_in_domain)
                     ultimately show ?thesis
                     proof-
                       have "q1 (inv_into dom1 T (T x)) (inv_into dom1 T ((phi_p' \<circ> T) y)) = q1 (T ((inv_into dom1 T (T x)) )) (T((inv_into dom1 T ((phi_p' \<circ> T) y))))"
                      
                         using
                           \<open>q1 (inv_into dom1 T (T x)) (inv_into dom1 T ((phi_p' \<circ> T) y)) = q1 (T (inv_into dom1 T (T x))) (T (inv_into dom1 T ((phi_p' \<circ> T) y)))\<close>
                         by blast
                       moreover have "(T (inv_into dom1 T (T x))) = T x"
                         
                         using \<open>(inv_into dom1 T \<circ> T) x = x\<close> by auto
                       moreover have "((phi_p' \<circ> T) y)\<in>dom1"
                         using mazur_ulam_help1_1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of p p' phi_p phi_p' S, OF assms(9) assms(10) assms(11) ]
                       
                       
                         using \<open>y \<in> dom1\<close> assms(12,13) by blast
                       moreover have " (T (inv_into dom1 T ((phi_p' \<circ> T) y))) =  ((phi_p' \<circ> T) y)"
                         
                         by (metis assms(2) calculation(3) f_inv_into_f)
                       ultimately show ?thesis
                       
                         by presburger
                     qed
                   qed
                   ultimately show ?thesis 
                  
                   
                     using \<open>x \<in> dom1\<close> \<open>y \<in> dom1\<close> assms(1,2,4) comp_apply f_inv_into_f
                         gyrocommutative_gyrogroup_def gyrogroup.ax1 gyrogroup_def gyrogroupoid.gyroplus_closed
                         gyrolinear_space.scale_closed gyrolinear_space_def imageI inv_into_into
                         normed_gyrolinear_space''_def
                    
                     by simp
                    
                 qed   
                 ultimately show ?thesis 
                 
                   by (simp add: \<open>x \<in> dom1\<close>)
               qed
             qed
           qed
         
                moreover have A3: "\<forall>x\<in>dom1.\<forall>y\<in>dom1. q1 (((inv_into dom1 T)\<circ> T)x) (((inv_into dom1 T)\<circ>(phi_p' \<circ> T)) y) = q1 (phi_p x) (S y)"
                 proof
                   fix x
                   assume "x\<in> dom1"
                   show "\<forall>y\<in>dom1.    q1 (((inv_into dom1 T)\<circ> T)x) (((inv_into dom1 T)\<circ>(phi_p' \<circ> T)) y) = q1 (phi_p x) (S y)"
                   proof
                     fix y
                     assume "y\<in>dom1"
                      

                     show " q1 (((inv_into dom1 T)\<circ> T)x) (((inv_into dom1 T)\<circ>(phi_p' \<circ> T)) y) = q1 (phi_p x) (S y)"
                 proof-
                have "inj_on T dom1"
              
                  by (metis (mono_tags, opaque_lifting) assms(1,3,4) inj_on_def
                      normed_gyrolinear_space''.gyrom_id normed_gyrolinear_space''.gyrom_id2)
                     
                   moreover have "((inv_into dom1 T) \<circ> T) x = x"
                    
                     by (simp add: \<open>x \<in> dom1\<close> calculation)
                   moreover have "p\<in>dom1"
                   
                    
                     by (metis assms(1,7,8,9) normed_gyrolinear_space''.gyromid_in_domain)
                   moreover have "((inv_into dom1 T)\<circ>(phi_p' \<circ> T)) y\<in> dom1"
                    
                     using mazur_ulam_help1_1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of p p' phi_p phi_p' S, OF assms(9) assms(10) assms(11)]
                     
                     using \<open>y \<in> dom1\<close> assms(12,13) by fastforce
                   ultimately show ?thesis 
                     using normed_gyrolinear_space''.proposition16_hatori_abe_p2[OF assms(1) `p \<in> dom1`, of  "\<lambda>y. (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 y) (gyroinv1 x) else undefined)"]
                     ` normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1 q1` 
                     
                     using \<open>x \<in> dom1\<close> assms(11,13) by fastforce
      
                     
                 qed
               qed
             qed
           
         moreover have ***:"\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((phi_p \<circ> S)x) y =  q1 (phi_p x) (S y)"
         proof
           fix x
           assume "x\<in>dom1"
           show " \<forall>y\<in>dom1. q1 ((phi_p \<circ> S)x) y =  q1 (phi_p x) (S y)"
           proof
             fix y 
             assume "y\<in>dom1"
             show " q1 ((phi_p \<circ> S)x) y =  q1 (phi_p x) (S y)"
               using A1 A2 A3
               
               by (smt (verit, ccfv_threshold) \<open>x \<in> dom1\<close> \<open>y \<in> dom1\<close> comp_apply f_inv_into_f imageI
                   inv_into_into)
           qed
         qed
         ultimately show ?thesis
           by blast
       qed
     
lemma mazur_ulam_sameG:
  fixes dom1::"'a set" 
  fixes T::"'a\<Rightarrow>'a"
  assumes 
  "normed_gyrolinear_space'' dom1 gyrozero1 gyroplus1 gyroinv1 gyr1 scale1 norm'1 oplus'1 otimes'1"
   "T ` dom1 = dom1" 
  "normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1  q1"
  "\<forall>a\<in>dom1. \<forall>b\<in>dom1. q1 (T a) (T b) = q1 a b"
  "\<exists>x\<in>dom1. x\<noteq>gyrozero1"
"(\<forall>y\<in>dom1. \<exists>x\<in>dom1. T x = y)"
shows "\<forall>a\<in>dom1. \<forall>b\<in>dom1. ((normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1  gyr1 scale1)
 (T a) (T b) = T ((normed_gyrolinear_space''.gyromid  dom1 gyroplus1 gyroinv1  gyr1 scale1) a b))"
  proof
fix a
  assume "a\<in>dom1"
  show "  \<forall>b\<in>dom1.
            normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a)
             (T b) =
            T (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)"
  proof
    fix b
    assume "b\<in>dom1"
    show  "normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a)
             (T b) =
            T (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)"
    proof-
      let ?p = "normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b"
      let ?p' = "normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a)
             (T b)"
      let ?norms2 = " norm'1 ` dom1 \<union> (\<lambda>x. - 1 * norm'1 x) ` dom1"
      have "
  \<exists>f. bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x} \<and>
        (\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and>
               z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow>
               f z < f y) \<and>
        (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y)) \<and>
        (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x))
"
       
      proof-

        have *:" \<exists>x. x \<in> normed_gyrolinear_space''.norms_all dom1 norm'1 \<and> x \<noteq> 0"
          using   normed_gyrolinear_space''.not_trivial_123[OF assms(1)]
     
          using assms(5) by blast
        then show ?thesis  using normed_gyrolinear_space''.existence_of_f[OF assms(1) *]
          by blast
      qed
      moreover obtain "f" where "bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x} \<and>
        (\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and>
               z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow>
               f z < f y) \<and>
        (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y)) \<and>
        (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x)) \<and>
     (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (oplus'1 (norm'1 x) (norm'1 y)) = f (norm'1 x) + f (norm'1 y)) \<and>
     (\<forall>r. \<forall>x\<in>dom1. f (otimes'1 \<bar>r\<bar> (norm'1 x)) = \<bar>r\<bar> * f (norm'1 x))"
        
        by (smt (verit, del_insts) assms(1,5) normed_gyrolinear_space''.existence_of_f
            normed_gyrolinear_space''.not_trivial_123)
      let ?d = "f (q1 (T(?p)) ?p')"
      let ?phi_p = "\<lambda>x. (if x \<in> dom1 then gyroplus1 (scale1 2 ?p) (gyroinv1 x) else undefined)"
      let ?phi_p' = "\<lambda>x. (if x \<in> dom1 then gyroplus1 (scale1 2 ?p') (gyroinv1 x) else undefined)"
      let ?S = "(?phi_p \<circ>(inv_into dom1 T)\<circ>?phi_p' \<circ> T)"
      have "?d=0"
      proof-
        have "\<forall>n::nat. (f (q1 ((?S^^ (2^n)) ?p) ?p) = (2^(n+1))*?d)"
        proof
          fix n 
          show "(f (q1 ((?S^^ (2^n)) ?p) ?p) = (2^(n+1))*?d)"
          proof (induction n)
            case 0
            then show ?case 
            proof-
              have "2^0 = 1"
                using power_0 
                by auto
              moreover have "(?S^^ (2^0)) ?p = ?S ?p"
                by simp
              moreover have "f (q1 (?S ?p) ?p) = 2*?d"
              proof-
                have A1:"\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> ?S)x) y = q1 (((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x) y"
                proof
                  fix x
                  assume "x\<in>dom1"
                  show  "\<forall>y\<in>dom1. q1 ((?phi_p \<circ> ?S)x) y = q1 (((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x) y"
                  proof
                    fix y 
                    assume "y\<in>dom1"
                    show " q1 ((?phi_p \<circ> ?S)x) y = q1 (((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x) y"
                  proof-
                  have " ?phi_p = (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 ?p) (gyroinv1 x) else undefined)"
                    by auto
                  moreover have "?p \<in>dom1"
             
                    by (meson \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1)
                        normed_gyrolinear_space''.gyromid_in_domain)
                  moreover have "\<forall>z\<in>dom1. (?phi_p \<circ> ?phi_p) z = z"
                  proof 
                    fix z
                    assume "z\<in>dom1"
                    show "(?phi_p \<circ> ?phi_p) z = z"
                      using normed_gyrolinear_space''.proposition16_hatori_abe_p1_v2[OF assms(1)]             
                    
                      by (simp add: \<open>z \<in> dom1\<close> calculation(2))
                
                  qed
                  moreover have "(((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x)\<in>dom1"
                    using mazur_ulam_help1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
                    
                    using \<open>x \<in> dom1\<close> by blast
                  ultimately show ?thesis 
                  
                    by auto
                qed
              qed
            qed
               moreover have A2:"\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 (((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x) y = q1 x (((inv_into dom1 T)\<circ>?phi_p' \<circ> T) y)"
               proof
                 fix x
                 assume "x\<in>dom1"
                 show "\<forall>y\<in>dom1. q1 (((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x) y = q1 x (((inv_into dom1 T)\<circ>?phi_p' \<circ> T) y)"
                 proof
                   fix y
                   assume "y\<in>dom1"
                   show " q1 (((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x) y = q1 x (((inv_into dom1 T)\<circ>?phi_p' \<circ> T) y)"
                   proof-
                    have "(((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x)\<in>dom1"
                    using mazur_ulam_help1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
                    
                    using \<open>x \<in> dom1\<close> by blast
                     have "q1 (((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x) y  = q1 (T(((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x)) (T y)"
                       using assms
                       
                       using
                         \<open>(inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) x \<in> dom1\<close>
                         \<open>y \<in> dom1\<close> by auto
                     moreover have "inj_on T dom1"
                     by (metis (mono_tags, opaque_lifting) assms(1,3,4) inj_onCI
                           normed_gyrolinear_space''.gyrom_id normed_gyrolinear_space''.gyrom_id2)
                     moreover have "((?phi_p' \<circ> T) x)\<in>dom1"
                       using mazur_ulam_help1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]

                      
                       using \<open>x \<in> dom1\<close> by blast
                       moreover have " q1 (T(((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x)) (T y) =  q1 ((?phi_p' \<circ> T) x) (T y)"
                         
                         by (metis (lifting) assms(2) calculation(3) comp_apply f_inv_into_f)
                         
                        (* by (smt (verit) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> \<open>x \<in> dom1\<close> assms(1,3) comp_apply f_inv_into_f
                             gyrocommutative_gyrogroup_def gyrogroup.ax1 gyrogroup_def gyrogroupoid.gyroplus_closed
                             gyrolinear_space.scale_closed gyrolinear_space_def imageI
                             normed_gyrolinear_space''.gyromid_in_domain normed_gyrolinear_space''_def)
                   *)
                  moreover have "?p' \<in> dom1"
                    
                    by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,2) imageI
                        normed_gyrolinear_space''.gyromid_in_domain)
                  moreover have " q1 ((?phi_p' \<circ> T) x) (T y) =  q1 ((?phi_p'\<circ>(?phi_p' \<circ> T)) x) ((?phi_p' \<circ> T) y)"
                    using normed_gyrolinear_space''.proposition16_hatori_abe_p2[OF assms(1)]
                    `?p' \<in>dom1`
                  
                    using \<open>y \<in> dom1\<close> assms(2,3) calculation(3) by fastforce
                  moreover have " q1 ((?phi_p'\<circ>(?phi_p' \<circ> T)) x) ((?phi_p' \<circ> T) y) = q1 (((inv_into dom1 T)\<circ> T)x) (((inv_into dom1 T)\<circ>(?phi_p' \<circ> T)) y)"
                    
                  proof-

                  have "?p' \<in>dom1"
                    
                    using calculation(5) by force
                  moreover have "\<forall>z\<in>dom1. (?phi_p' \<circ> ?phi_p') z = z"
                   proof 
                    fix z
                    assume "z\<in>dom1"
                    show "(?phi_p' \<circ> ?phi_p') z = z"
                      using normed_gyrolinear_space''.proposition16_hatori_abe_p1_v2[OF assms(1)]             
                   
                      by (simp add: \<open>z \<in> dom1\<close> calculation)
                
                  qed
                   moreover have "((?phi_p'\<circ>(?phi_p' \<circ> T)) x) = T x"
                 
                     using \<open>x \<in> dom1\<close> assms(2) calculation(2) by auto

                   moreover have "q1 ((?phi_p'\<circ>(?phi_p' \<circ> T)) x) ((?phi_p' \<circ> T) y) = q1 (T x) ((?phi_p' \<circ> T) y)"
                     using calculation(3) by presburger
                   moreover have "inj_on T dom1"
                     using mazur_ulam_inj
                    
                     using \<open>inj_on T dom1\<close> by force
                   moreover have "((inv_into dom1 T) \<circ> T) x = x"
                
                     by (simp add: \<open>x \<in> dom1\<close> calculation(5))
                   moreover have "q1 (T x) ((?phi_p' \<circ> T) y) = q1 ((inv_into dom1 T) (T x)) ((inv_into dom1 T)(((?phi_p' \<circ> T) y)))"
                   proof-
                     have "(inv_into dom1 T) (T x)\<in> dom1"
                     
                       using \<open>x \<in> dom1\<close> calculation(6) by fastforce
                     moreover have "(inv_into dom1 T)(((?phi_p' \<circ> T) y))\<in>dom1"
                      
                       by (smt (verit, ccfv_threshold)
                           \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b) \<in> dom1\<close>
                           \<open>y \<in> dom1\<close> assms(1,2) comp_apply gyrocommutative_gyrogroup_def gyrogroup.ax1
                           gyrogroup_def gyrogroupoid.gyroplus_closed gyrolinear_space.scale_closed
                           gyrolinear_space_def imageI inv_into_into normed_gyrolinear_space''_def)
                     have "q1 ((inv_into dom1 T) (T x)) ((inv_into dom1 T)(((?phi_p' \<circ> T) y))) =
                  q1 (T((inv_into dom1 T) (T x))) (T((inv_into dom1 T)(((?phi_p' \<circ> T) y))))"
                       using assms(4)
                       
                       using
                         \<open>inv_into dom1 T (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) y) \<in> dom1\<close>
                         calculation by auto
                     ultimately show ?thesis
                       by (smt (verit, ccfv_threshold) \<open>(inv_into dom1 T \<circ> T) x = x\<close>
                           \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b) \<in> dom1\<close>
                           \<open>y \<in> dom1\<close> assms(1,2) comp_apply f_inv_into_f gyrocommutative_gyrogroup_def
                           gyrogroup.ax1 gyrogroup_def gyrogroupoid.gyroplus_closed gyrolinear_space.scale_closed
                           gyrolinear_space_def imageI normed_gyrolinear_space''_def)
                   qed
                   ultimately show ?thesis 
                  
                   
                     using \<open>x \<in> dom1\<close> \<open>y \<in> dom1\<close> assms(1,2,4) comp_apply f_inv_into_f
                         gyrocommutative_gyrogroup_def gyrogroup.ax1 gyrogroup_def gyrogroupoid.gyroplus_closed
                         gyrolinear_space.scale_closed gyrolinear_space_def imageI inv_into_into
                         normed_gyrolinear_space''_def
                    
                     by simp
                    
                 qed   
                 ultimately show ?thesis 
                 
                   by (simp add: \<open>x \<in> dom1\<close>)
               qed
             qed
           qed
         
                moreover have A3: "\<forall>x\<in>dom1.\<forall>y\<in>dom1. q1 (((inv_into dom1 T)\<circ> T)x) (((inv_into dom1 T)\<circ>(?phi_p' \<circ> T)) y) = q1 (?phi_p x) (?S y)"
                 proof
                   fix x
                   assume "x\<in> dom1"
                   show "\<forall>y\<in>dom1.    q1 (((inv_into dom1 T)\<circ> T)x) (((inv_into dom1 T)\<circ>(?phi_p' \<circ> T)) y) = q1 (?phi_p x) (?S y)"
                   proof
                     fix y
                     assume "y\<in>dom1"
                      

                     show " q1 (((inv_into dom1 T)\<circ> T)x) (((inv_into dom1 T)\<circ>(?phi_p' \<circ> T)) y) = q1 (?phi_p x) (?S y)"
                 proof-
                have "inj_on T dom1"
              
                  by (metis (mono_tags, opaque_lifting) assms(1,3,4) inj_on_def
                      normed_gyrolinear_space''.gyrom_id normed_gyrolinear_space''.gyrom_id2)
                     
                   moreover have "((inv_into dom1 T) \<circ> T) x = x"
                    
                     by (simp add: \<open>x \<in> dom1\<close> calculation)
                   moreover have "?p\<in>dom1"
                   
                     by (meson \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1)
                         normed_gyrolinear_space''.gyromid_in_domain)
                   moreover have "((inv_into dom1 T)\<circ>(?phi_p' \<circ> T)) y\<in> dom1"
                    
                     using mazur_ulam_help1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
                    
                     by (metis (no_types, lifting) \<open>y \<in> dom1\<close> comp_assoc imageI)
                   ultimately show ?thesis 
                     using normed_gyrolinear_space''.proposition16_hatori_abe_p2[OF assms(1) `?p \<in> dom1`]
                     ` normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1 q1` 
                     using \<open>x \<in> dom1\<close> comp_apply by fastforce
      
                     
                 qed
               qed
             qed
           
         moreover have ***:"\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> ?S)x) y =  q1 (?phi_p x) (?S y)"
         proof
           fix x
           assume "x\<in>dom1"
           show " \<forall>y\<in>dom1. q1 ((?phi_p \<circ> ?S)x) y =  q1 (?phi_p x) (?S y)"
           proof
             fix y 
             assume "y\<in>dom1"
             show " q1 ((?phi_p \<circ> ?S)x) y =  q1 (?phi_p x) (?S y)"
               using A1 A2 A3
               
               by (smt (verit, ccfv_threshold) \<open>x \<in> dom1\<close> \<open>y \<in> dom1\<close> comp_apply f_inv_into_f imageI
                   inv_into_into)
           qed
         qed
         moreover have "\<forall>n::nat. \<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> (?S^^n))x) y =  q1 (?phi_p x) ((?S^^n) y)"
         proof
           fix n::nat
           show "\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> (?S^^n))x) y =  q1 (?phi_p x) ((?S^^n) y)"
           proof(induction n)
             case 0
             then show ?case 
               by force
           next
             case (Suc n)
             moreover have "\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> (?S^^(n+1)))x) y =  q1 ((?phi_p \<circ> (?S \<circ>(?S^^n)))x) y"
              
               by force
             moreover have "\<forall>n::nat.\<forall>x\<in>dom1. (?S^^n)x\<in>dom1"
 using mazur_ulam_help2[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
                 
               
               by presburger
             moreover have  "\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> (?S \<circ>(?S^^n)))x) y = q1 ((?phi_p \<circ> (?S^^n))x) (?S y)"
               using ***
               
               by (smt (verit, ccfv_SIG) calculation(3) comp_apply)

             ultimately show ?case
             proof -
               obtain aa :: 'a where
                 "(\<exists>v0. v0 \<in> dom1 \<and> (\<exists>v1. v1 \<in> dom1 \<and> q1 (((\<lambda>uu. if uu \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 uu) else undefined) \<circ> ((\<lambda>uu. if uu \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 uu) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>uu. if uu \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 uu) else undefined) \<circ> T) ^^ Suc n) v0) v1 \<noteq> q1 (if v0 \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 v0) else undefined) ((((\<lambda>uu. if uu \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 uu) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>uu. if uu \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 uu) else undefined) \<circ> T) ^^ Suc n) v1))) = (aa \<in> dom1 \<and> (\<exists>v1. v1 \<in> dom1 \<and> q1 (((\<lambda>uu. if uu \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 uu) else undefined) \<circ> ((\<lambda>uu. if uu \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 uu) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>uu. if uu \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 uu) else undefined) \<circ> T) ^^ Suc n) aa) v1 \<noteq> q1 (if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) ((((\<lambda>uu. if uu \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 uu) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>uu. if uu \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 uu) else undefined) \<circ> T) ^^ Suc n) v1)))"
                 by blast
               then obtain aaa :: 'a where
                 f1: "(\<exists>aa. aa \<in> dom1 \<and> (\<exists>ab. ab \<in> dom1 \<and> q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aa) ab \<noteq> q1 (if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) ab))) = (aa \<in> dom1 \<and> aaa \<in> dom1 \<and> q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aa) aaa \<noteq> q1 (if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aaa))"
                 by blast
               have f2: "\<forall>aa. aa \<in> dom1 \<longrightarrow> (\<forall>ab. ab \<in> dom1 \<longrightarrow> q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ n) aa) ab = q1 (if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ n) ab))"
                 using Suc by blast
               { assume "(((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ 1) aaa \<in> dom1"
                 then have "((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T)) aaa \<in> dom1"
                   by simp
                 moreover
                 { assume "if aa \<in> dom1 then q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ n) aa) (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T)) aaa) = q1 (gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa)) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ n) (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T)) aaa)) else q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ n) aa) (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T)) aaa) = q1 undefined ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ n) (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T)) aaa))"
                   moreover
                   { assume "q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ n) aa) (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T)) aaa) = q1 (gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa)) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ n) (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T)) aaa))"
                     moreover
                     { assume "aaa \<notin> dom1 \<or> q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aa) aaa = q1 (if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aaa)"
                       then have "aa \<notin> dom1 \<or> aaa \<notin> dom1 \<or> q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aa) aaa = q1 (if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aaa)"
                         by fastforce }
                     ultimately have "aa \<in> dom1 \<longrightarrow> (aa \<notin> dom1 \<or> aaa \<notin> dom1 \<or> q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aa) aaa = q1 (if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aaa)) \<or> aaa \<notin> dom1 \<or> q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aa) aaa = q1 (if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aaa)"
                       by (smt (z3) \<open>\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> ((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T \<circ> ((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ n)) x) y = q1 (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> ((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ n) x) (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) y)\<close> comp_apply funpow.simps(2) funpow_Suc_right) }
                   ultimately have "aa \<in> dom1 \<longrightarrow> (aa \<notin> dom1 \<or> aaa \<notin> dom1 \<or> q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aa) aaa = q1 (if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aaa)) \<or> aaa \<notin> dom1 \<or> q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aa) aaa = q1 (if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aaa)"
                     by presburger }
                 ultimately have "(aaa \<notin> dom1 \<or> q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aa) aaa = q1 (if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aaa)) \<or> aa \<notin> dom1 \<or> aaa \<notin> dom1 \<or> q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aa) aaa = q1 (if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc n) aaa)"
                   using f2 by presburger }
               then show ?thesis
                 using f1 \<open>\<forall>n. \<forall>x\<in>dom1. (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ n) x \<in> dom1\<close> by blast
             qed
           qed
         qed
       
         moreover have "?p \<in>dom1"
          
       
           by (meson \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1)
               normed_gyrolinear_space''.gyromid_in_domain)
         moreover have "  q1 (?phi_p ?p) (?S ?p) = q1 (?S ?p) ?p"
         proof-
           have "?phi_p ?p = ?p"
           using assms(2) calculation(6) normed_gyrolinear_space''.proposition16_hatori_abe_p3
         
           using assms(1) by fastforce
         then show ?thesis 
        
           by (smt (verit, best) assms(1,3) normed_gyrolinear_space''.gyrometric_sym
               normed_gyrolinear_space''.isgyrometric_def)
    
       qed
       moreover have " q1 (?S ?p) ?p =q1 ((?phi_p \<circ> ?S)?p) ?p"
         using calculation(4,5,6,7) by fastforce
       moreover have "q1 ((?phi_p \<circ> ?S)?p) ?p = q1 ((?phi_p' \<circ> T)?p) (T ?p)"
       proof-
         have "((?phi_p \<circ> ?S)?p) = (?phi_p \<circ> ((?phi_p \<circ>(inv_into dom1 T)\<circ>?phi_p' \<circ> T))) ?p"
           by meson
         moreover have "?p \<in> dom1"
         
           using
             \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b \<in> dom1\<close>
           by blast
         moreover have "((inv_into dom1 T)\<circ>?phi_p' \<circ> T) ?p\<in> dom1"
        
           using mazur_ulam_help1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
          
           using calculation(2) by blast
            moreover have "\<forall>z\<in>dom1. (?phi_p \<circ> ?phi_p) z = z"
                   proof 
                    fix z
                    assume "z\<in>dom1"
                    show "(?phi_p \<circ> ?phi_p) z = z"
                      using normed_gyrolinear_space''.proposition16_hatori_abe_p1_v2[OF assms(1)]             
                   
                      by (simp add: \<open>z \<in> dom1\<close> calculation)
                
                  qed
         moreover have "(?phi_p \<circ> ((?phi_p \<circ>(inv_into dom1 T)\<circ>?phi_p' \<circ> T))) ?p = ( (inv_into dom1 T)\<circ>?phi_p' \<circ> T) ?p"
           using  normed_gyrolinear_space''.proposition16_hatori_abe_p1[OF assms(1) `?p\<in>dom1`]
          `((inv_into dom1 T)\<circ>?phi_p' \<circ> T) ?p\<in> dom1`
           
           using calculation(4) comp_apply by auto
         moreover have "(?phi_p' \<circ> T) ?p\<in>dom1"
           using mazur_ulam_help1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
          
           using calculation(2) by blast
         moreover have "(T\<circ>(inv_into dom1 T)\<circ>?phi_p' \<circ> T) ?p  = (?phi_p' \<circ> T) ?p"
       
           by (smt (verit, best) assms(2) calculation(6) comp_eq_dest_lhs f_inv_into_f)
         ultimately show ?thesis
           using  assms(5)
           
           using assms(4) by auto  
       qed
       moreover have "?p'\<in>dom1"
        
         by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,2) imageI
             normed_gyrolinear_space''.gyromid_in_domain)
               moreover have " q1 ((?phi_p' \<circ> T)?p) (T ?p) = otimes'1 2 (q1 (T ?p) ?p')"
               proof-
                 have  "?p'\<in>dom1"
        
         by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,2) imageI
             normed_gyrolinear_space''.gyromid_in_domain)
       moreover have "T ?p\<in>dom1"
        
         using
           \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b \<in> dom1\<close>
           assms(2) by blast
           moreover have " q1 ((?phi_p' (T ?p))) (T ?p) = otimes'1 2 (q1 ?p' (T ?p))"
                 
                 using normed_gyrolinear_space''.proposition16_hatori_abe_p5[OF assms(1) `?p'\<in>dom1`]
      
       proof -
         obtain aa :: "'a \<Rightarrow> 'a" where
           f1: "\<forall>X7. aa X7 = (if X7 \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 X7) else undefined)"
           by moura
         then have "\<forall>f ab fa. \<not> normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1 fa \<or> fa (f ab) ab = otimes'1 2 (fa ab (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) \<or> f \<noteq> aa \<or> ab \<notin> dom1"
           using \<open>\<And>q fi aa. fi (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b)) = (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<Longrightarrow> aa \<in> dom1 \<Longrightarrow> normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1 q \<Longrightarrow> q (fi (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b)) aa) aa = otimes'1 2 (q aa (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b)))\<close> by force
         then show ?thesis
           using f1 by (smt (z3) assms(1,3) calculation(1,2) normed_gyrolinear_space''.gyrometric_sym)
       qed
       ultimately show ?thesis
        
         using assms(1,3) normed_gyrolinear_space''.gyrometric_sym by fastforce
     qed 
       moreover have "f(q1 (?S ?p) ?p) = f(otimes'1 2 (q1 (T ?p) ?p'))"
         
         using calculation(11,8,9) by presburger      (* moreover have "f(otimes'1 2 (q1 (T ?p) ?p')) = f ((inv_into (normed_gyrolinear_space''.norms dom1 norm'1) f) (2 * f((q1 (T ?p) ?p'))))"
       proof-*)
       moreover have "f(otimes'1 2 (q1 (T ?p) ?p')) = f(norm'1 (scale1 2 (gyroplus1 (T ?p) (gyroinv1 ?p'))))"
         proof-
           have "\<forall>r. \<forall>x\<in>dom1. (otimes'1 \<bar>r\<bar> (norm'1 x)) = norm'1 (scale1 \<bar>r\<bar> x)"
             by (metis abs_idempotent assms(1) normed_gyrolinear_space''.norm_scale)
           moreover have "otimes'1 2 (q1 (T ?p) ?p') = otimes'1 2 (norm'1 (gyroplus1 (T ?p) (gyroinv1 ?p')))"
            
             by (metis (mono_tags, lifting)
                 \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b) \<in> dom1\<close>
                 \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b \<in> dom1\<close>
                 assms(1,2,3) image_eqI normed_gyrolinear_space''.isgyrometric_def)
           moreover have "gyroplus1 (T ?p) (gyroinv1 ?p')\<in>dom1"
           proof-
             have "?p'\<in>dom1"
              
               using
                 \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b) \<in> dom1\<close>
               by blast
             moreover have "gyroinv1 ?p'\<in>dom1"
            
               by (metis assms(1) calculation gyrolinear_space.scale_closed
                   gyrolinear_space.scale_minus1_inv normed_gyrolinear_space''_def)
             moreover have "T ?p\<in>dom1"
               
               using
                 \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b \<in> dom1\<close>
                 assms(2) by blast
             ultimately show ?thesis 
               by (metis assms(1) gyrocommutative_gyrogroup_def gyrogroup_def
                   gyrogroupoid.gyroplus_closed gyrolinear_space_def
                   normed_gyrolinear_space''_def)
           qed
           moreover have " otimes'1 2 (norm'1 (gyroplus1 (T ?p) (gyroinv1 ?p'))) = norm'1 (scale1 2 (gyroplus1 (T ?p) (gyroinv1 ?p')))"
            
             by (metis abs_numeral calculation(1,3))
           ultimately show ?thesis
             by presburger
         qed
         moreover have " (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x))"
          
           using
             \<open>bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x} \<and> (\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow> f z < f y) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x)) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (oplus'1 (norm'1 x) (norm'1 y)) = f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (otimes'1 \<bar>r\<bar> (norm'1 x)) = \<bar>r\<bar> * f (norm'1 x))\<close>
           by argo
   moreover have "gyroplus1 (T ?p) (gyroinv1 ?p')\<in>dom1"
           proof-
             have "?p'\<in>dom1"
              
               using
                 \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b) \<in> dom1\<close>
               by blast
             moreover have "gyroinv1 ?p'\<in>dom1"
            
               by (metis assms(1) calculation gyrolinear_space.scale_closed
                   gyrolinear_space.scale_minus1_inv normed_gyrolinear_space''_def)
             moreover have "T ?p\<in>dom1"
               
               using
                 \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b \<in> dom1\<close>
                 assms(2) by blast
             ultimately show ?thesis 
               by (metis assms(1) gyrocommutative_gyrogroup_def gyrogroup_def
                   gyrogroupoid.gyroplus_closed gyrolinear_space_def
                   normed_gyrolinear_space''_def)
           qed
         moreover have " f(norm'1 (scale1 2 (gyroplus1 (T ?p) (gyroinv1 ?p')))) = 2 * f(norm'1 (gyroplus1 (T ?p) (gyroinv1 ?p')))"
         
           by (simp add: calculation(14,15))
         ultimately show ?thesis
           
           by (smt (verit, best) assms(1,2,3) imageI
               normed_gyrolinear_space''.isgyrometric_def)
           
        
       qed
       ultimately show ?case
         by simp 
     qed

   
     
          next
            case (Suc n)
            moreover have "?p\<in>dom1"
             
              by (meson \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1)
                  normed_gyrolinear_space''.gyromid_in_domain)
            moreover have "2^(n+2)*?d = f (otimes'1 2 (q1 ((?S^^(2^n))?p) ?p))"
            proof-
              have "2^(n+1)*?d = f ( (q1 ((?S^^(2^n))?p) ?p))"
                using Suc.IH
                by argo
              moreover have "2^(n+2) = 2 * (2^(n+1))"
                
                by force
              moreover have "2^(n+2)*?d = 2 * f ( (q1 ((?S^^(2^n))?p) ?p))"
                
                by (simp add: Suc)
 moreover have " ((?S^^(2^n))?p)\<in>dom1"
              using mazur_ulam_help2[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
              by (simp add:
                  \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b \<in> dom1\<close>)
            moreover have "q1 ((?S^^(2^n))?p) ?p = norm'1 (gyroplus1 ((?S^^(2^n))?p) (gyroinv1 ?p))"
          
              using
                \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b \<in> dom1\<close>
                assms(1,3) calculation(4) normed_gyrolinear_space''.isgyrometric_def
              by fastforce
            moreover have " (gyroplus1 ((?S^^(2^n))?p) (gyroinv1 ?p))\<in> dom1"
              
              by (metis (no_types, lifting) 
                  \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b \<in> dom1\<close>
                  assms(1) calculation(4) gyrocommutative_gyrogroup_def gyrogroup_def
                  gyrogroupoid.gyroplus_closed gyrolinear_space.scale_closed
                  gyrolinear_space.scale_minus1_inv gyrolinear_space_def
                  normed_gyrolinear_space''_def)
            moreover have "2 * f ( (q1 ((?S^^(2^n))?p) ?p)) = 2 * f (  norm'1 (gyroplus1 ((?S^^(2^n))?p) (gyroinv1 ?p)))"
            
              by (simp add: calculation(5))
            ultimately show ?thesis 
            proof -
              have f1: "bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {r. 0 \<le> r} \<and> (\<forall>r ra. r \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> ra \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> ra < r \<longrightarrow> f ra < f r) \<and> (\<forall>a. a \<in> dom1 \<longrightarrow> (\<forall>aa. aa \<in> dom1 \<longrightarrow> f (norm'1 (gyroplus1 a aa)) \<le> f (norm'1 a) + f (norm'1 aa))) \<and> (\<forall>r a. a \<in> dom1 \<longrightarrow> f (norm'1 (scale1 r a)) = (if r < 0 then - r else r) * f (norm'1 a)) \<and> (\<forall>a. a \<in> dom1 \<longrightarrow> (\<forall>aa. aa \<in> dom1 \<longrightarrow> f (oplus'1 (norm'1 a) (norm'1 aa)) = f (norm'1 a) + f (norm'1 aa))) \<and> (\<forall>r a. a \<in> dom1 \<longrightarrow> f (otimes'1 (if r < 0 then - r else r) (norm'1 a)) = (if r < 0 then - r else r) * f (norm'1 a))"
                by (smt (z3) \<open>bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x} \<and> (\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow> f z < f y) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x)) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (oplus'1 (norm'1 x) (norm'1 y)) = f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (otimes'1 \<bar>r\<bar> (norm'1 x)) = \<bar>r\<bar> * f (norm'1 x))\<close>)
              have f2: "\<forall>a r. (f (otimes'1 (if r < 0 then - r else r) (norm'1 a)) = (if r < 0 then - r else r) * f (norm'1 a)) = (f (otimes'1 (if r < 0 then - 1 * r else r) (norm'1 a)) = (if r < 0 then - 1 * r else r) * f (norm'1 a))"
                by simp
              have "\<forall>x1. ((x1::real) < 0) = (\<not> 0 \<le> x1)"
                by fastforce
              then have "\<forall>r a. a \<notin> dom1 \<or> (if 0 \<le> r then f (otimes'1 r (norm'1 a)) = r * f (norm'1 a) else f (otimes'1 (- 1 * r) (norm'1 a)) = - 1 * r * f (norm'1 a))"
                using f2 f1 by presburger
              then show ?thesis
                using \<open>2 ^ (n + 1) * f (q1 (T (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) = f (q1 ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b))\<close> \<open>gyroplus1 ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) \<in> dom1\<close> \<open>q1 ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b) = norm'1 (gyroplus1 ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)))\<close> by force
            qed
            qed
          
            moreover have " ((?S^^(2^n))?p)\<in>dom1"
              using mazur_ulam_help2[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
            
              using calculation(2) by force
           
          
            moreover have  "f (otimes'1 2 (q1 ((?S^^(2^n))?p) ?p)) = f (q1 (?phi_p ((?S^^(2^n))?p)) ((?S^^(2^n))?p))"
              using  normed_gyrolinear_space''.proposition16_hatori_abe_p5[OF assms(1) `?p\<in>dom1`]
             
             
              by (simp add: assms(3) calculation(4))
            moreover have AX1:"\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> ?S)x) y =  q1 (?phi_p x) (?S y)"
              using mazur_ulam_sameG_6_1[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) ]
           
              by (simp add: \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close>)
              
            moreover have "?phi_p ?p=?p"
               using  normed_gyrolinear_space''.proposition16_hatori_abe_p3[OF assms(1) `?p\<in>dom1`]
   
               by (simp add: calculation(2))
            moreover have *:"\<forall>m::nat. \<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> (?S^^m))x) y =   q1 (?phi_p x) ((?S^^m) y)"
            proof
              fix m::nat
              show  "\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> (?S^^m))x) y =   q1 (?phi_p x) ((?S^^m) y)"
              proof (induction m)
                case 0
                then show ?case 
                  by force
              next
                case (Suc m)
                moreover have "\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> (?S^^(m+1)))x) y =  q1 (?phi_p (?S ((?S^^(m))x))) y"
                  by auto
                moreover have "\<forall>x\<in>dom1. \<forall>y\<in>dom1.  q1 (?phi_p (?S ((?S^^(m))x))) y =  q1 (?phi_p ( ((?S^^(m))x))) (?S y)"
                proof-
                  have "\<forall>x\<in>dom1.(?S^^(m))x\<in>dom1"
                    using mazur_ulam_help2[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
                    
                    by presburger
                  then show ?thesis 
                    using AX1 by auto
                qed
                
                
                moreover have "\<forall>y\<in>dom1.?S y\<in>dom1"
                  using mazur_ulam_help2[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
                 
                  by (metis (no_types, lifting)  comp_funpow funpow_0 funpow_Suc_right)
                moreover have " \<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 (?phi_p ( ((?S^^(m))x))) (?S y) =  q1 (?phi_p x) ((?S^^(m))(?S y))"
                  using Suc.IH
                  
                  by (smt (verit) calculation(4) comp_eq_dest_lhs)
                moreover have " \<forall>y\<in>dom1. ((?S^^(m))(?S y)) =  (?S^^(m+1))y"
                  
                  by (metis (mono_tags, lifting) Suc_eq_plus1 comp_apply funpow_Suc_right)
                ultimately show ?case
                 
                  by (smt (verit, del_insts) Suc_eq_plus1_left add.commute)
                  
                
                        
              qed
            qed
          
            
            
       
            moreover have "(?S^^(2^n))?p\<in>dom1"
              
              using calculation(4) by fastforce
           
            moreover    have "\<forall>m::nat. \<forall>y\<in>dom1. ((?S^^(m))(?S y)) =  (?S^^(m+1))y"
                  
                  by (metis (mono_tags, lifting) Suc_eq_plus1 comp_apply funpow_Suc_right)
        moreover have "f (q1 (?phi_p ((?S^^(2^n))?p)) ((?S^^(2^n))?p)) = f (q1 (?phi_p ?p) ((?S^^(2^(n+1)))?p))"
        proof-
          have " \<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> (?S^^(2^n)))x) y =   q1 (?phi_p x) ((?S^^(2^n)) y)"
            using "*" by blast
          moreover have "(q1 (?phi_p ((?S^^(2^n))?p)) ((?S^^(2^n))?p)) =  (q1 (?phi_p ?p) ((?S^^(2^n)) ((?S^^(2^n))?p)))"
      
            using
              \<open>(((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b) \<in> dom1\<close>
              \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b \<in> dom1\<close>
              calculation by auto
          ultimately show ?thesis 
            by (smt (verit, del_insts) Suc_eq_plus1 comp_apply funpow.simps(2) funpow_mult
                mult.right_neutral nat_1_add_1 power_add power_one_right)
        qed
ultimately show ?case
            
              by (smt (verit, best) Suc_eq_plus1 add_2_eq_Suc' assms(1,3)
                  normed_gyrolinear_space''.gyrometric_sym
                  normed_gyrolinear_space''.isgyrometric_def)
          qed
         
        qed
       

      
        moreover have "\<forall>n::nat. \<forall>t\<in>dom1. (?S^^(2^n))t\<in>dom1"
          using mazur_ulam_help2[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
          
          by auto
        moreover have "\<forall>n::nat. ((q1 ((?S^^(2^n))?p) ?p) \<le> oplus'1 (q1 ((?S^^(2^n))?p) ((?S^^(2^n))a))
      (q1 ((?S^^(2^n))a) ?p))"
          using  normed_gyrolinear_space''.gyrometric_triangle[OF assms(1)]
          by (metis (no_types, lifting) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) calculation(2)
              normed_gyrolinear_space''.gyromid_in_domain)

 moreover have "\<forall>n::nat. 2^(n+1) * ?d =  f ((q1 ((?S^^(2^n))?p) ?p)) "
          
   using calculation(1) by presburger
        moreover have "\<forall>n::nat. (q1 ((?S^^(2^n))?p) ((?S^^(2^n))a)) = (q1 (?p) (a))"
        proof-
          have "?p\<in>dom1"
        
            by (meson \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1)
                normed_gyrolinear_space''.gyromid_in_domain)
          moreover have "?phi_p a = b"
            using
                normed_gyrolinear_space''.proposition16_hatori_abe_p4[OF assms(1) `?p\<in>dom1`]
           
            by (simp add: \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close>)
          moreover have "a\<in>dom1"
           
            by (simp add: \<open>a \<in> dom1\<close>)
          
          moreover have "\<forall>n::nat. (q1 (?p) (a)) = (q1 (?p) ((?phi_p \<circ> ((?S^^(2^n)))) b))"
           using mazur_ulam_help3_1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p ?phi_p' ?S]
           `?phi_p a = b`
            \<open>b \<in> dom1\<close> assms(1) calculation(2,3) comp_apply
               normed_gyrolinear_space''.proposition16_hatori_abe_p4[OF assms(1) `?p\<in>dom1`]
     
           by auto
          moreover have "\<forall>n::nat. (q1 ((?phi_p \<circ> ((?S^^(2^n)))) b) (?p)) = (q1  (?phi_p  b)  (((?S^^(2^n))) ?p))"
          proof-
             have AXX1:"\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> ?S)x) y =  q1 (?phi_p x) (?S y)"
              using mazur_ulam_sameG_6_1[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) ]
           
              by (simp add: \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close>)
            moreover have "?phi_p ?p=?p"
              using  normed_gyrolinear_space''.proposition16_hatori_abe_p3[OF assms(1) `?p\<in>dom1`]
              by (simp add:
                  \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b \<in> dom1\<close>)
            moreover have ****:"\<forall>m::nat. \<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> (?S^^m))x) y =   q1 (?phi_p x) ((?S^^m) y)"
            proof
              fix m::nat
              show  "\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> (?S^^m))x) y =   q1 (?phi_p x) ((?S^^m) y)"
              proof (induction m)
                case 0
                then show ?case 
                  by force
              next
                case (Suc m)
                moreover have "\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 ((?phi_p \<circ> (?S^^(m+1)))x) y =  q1 (?phi_p (?S ((?S^^(m))x))) y"
                  by auto
                moreover have "\<forall>x\<in>dom1. \<forall>y\<in>dom1.  q1 (?phi_p (?S ((?S^^(m))x))) y =  q1 (?phi_p ( ((?S^^(m))x))) (?S y)"
                proof-
                  have "\<forall>x\<in>dom1.(?S^^(m))x\<in>dom1"
                    using mazur_ulam_help2[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
                    
                    by presburger
                  then show ?thesis 
                    using AXX1 by auto
                qed
                moreover have " \<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 (?phi_p ( ((?S^^(m))x))) (?S y) =  q1 (?phi_p x)   (((?S^^(m))) (?S y))"
                proof-
                  have "\<forall>y\<in>dom1. ?S y \<in>dom1"
                   
                    by (smt (z3)
                        \<open>\<forall>n. \<forall>t\<in>dom1. (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) t \<in> dom1\<close>
                        comp_eq_dest_lhs funpow.simps(2) funpow_0 nat_power_eq_Suc_0_iff)
                  then show ?thesis using Suc.IH 
                    by (smt (verit, best) comp_eq_dest_lhs)
                qed
                moreover have "\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 (?phi_p x)   (((?S^^(m))) (?S y)) = q1 (?phi_p x)   (((?S^^(m+1))) y)"
                  
                  by (metis (mono_tags, lifting) Suc_eq_plus1 comp_apply funpow_Suc_right)
                ultimately show ?case 
                proof -
                  { fix aa :: 'a and aaa :: 'a
                    have ff1: "\<And>aa ab. aa \<notin> dom1 \<or> ab \<notin> dom1 \<or> q1 (if ab \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 ab) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ m) (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) aa)) = q1 (if ab \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 ab) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc m) aa)"
                      using \<open>\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 (if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ m) (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) y)) = q1 (if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ (m + 1)) y)\<close> by auto
                    have "\<And>aa ab. aa \<notin> dom1 \<or> ab \<notin> dom1 \<or> q1 (if ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ m) ab) \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ m) ab))) else undefined) aa = q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc m) ab) aa"
                      using \<open>\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> ((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ (m + 1)) x) y = q1 (if ((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ m) x) \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ m) x))) else undefined) y\<close> by force
                    then have "aa \<notin> dom1 \<or> aaa \<notin> dom1 \<or> q1 (((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> ((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc m) aaa) aa = q1 (if aaa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aaa) else undefined) ((((\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 aa) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>aa. if aa \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 aa) else undefined) \<circ> T) ^^ Suc m) aa)"
                      using ff1 \<open>\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 (if (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ m) x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ m) x)) else undefined) (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) y) = q1 (if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ m) (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) y))\<close> \<open>\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 (if ((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ m) x) \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ m) x))) else undefined) y = q1 (if (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ m) x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ m) x)) else undefined) (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) y)\<close> by auto }
                  then show ?thesis
                    by blast
                qed 
              qed
            qed
              ultimately show ?thesis
                
                by (meson \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1)
                    normed_gyrolinear_space''.gyromid_in_domain)
            qed
            moreover have "?phi_p a = b"
             
            
              using calculation(2) by blast
            moreover have "\<forall>n::nat.(((?S^^(2^n))) a)  = a"
               using mazur_ulam_help3_1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
             
               by presburger
            moreover have "\<forall>n::nat. (q1  (?phi_p  b)  (((?S^^(2^n))) ?p)) = (q1   (((?S^^(2^n))) a)  (((?S^^(2^n))) ?p))"
            proof-
              have "?phi_p b =a "
                using
                normed_gyrolinear_space''.proposition16_hatori_abe_p4[OF assms(1) `?p\<in>dom1`]
                
                by (simp add: \<open>b \<in> dom1\<close> calculation(3))
              then show ?thesis
                by (simp add: calculation(7))
            qed
            ultimately show ?thesis 
              
              by (smt (verit, best) assms(1,3) normed_gyrolinear_space''.gyrometric_sym
                  normed_gyrolinear_space''.isgyrometric_def)
            qed
          
           
        moreover have "\<forall>n::nat. ((?S^^(2^n))a) = a"
using mazur_ulam_help3_1[OF assms(1) assms(1), of T, OF assms(2) assms(3) assms(3), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(4) assms(5) assms(6), of ?p ?p' ?phi_p]
          by presburger
          moreover have "\<forall>n::nat. oplus'1 (q1 ((?S^^(2^n))?p) ((?S^^(2^n))a))
      (q1 ((?S^^(2^n))a) ?p) =  oplus'1 (q1 (?p) (a))
      (q1 (a) ?p)" 
            
            using calculation(5,6) by force
          moreover have "\<forall>n::nat. 2^(n+1) * ?d =  f ((q1 ((?S^^(2^n))?p) ?p)) "
          
            using calculation(1) by presburger
          moreover have "    (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y))"
           
            using
              \<open>bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x} \<and> (\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow> f z < f y) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x)) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (oplus'1 (norm'1 x) (norm'1 y)) = f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (otimes'1 \<bar>r\<bar> (norm'1 x)) = \<bar>r\<bar> * f (norm'1 x))\<close>
            by linarith
          moreover have "\<forall>n::nat.  f ((q1 ((?S^^(2^n))?p) ?p)) = f (norm'1 (gyroplus1 ((?S^^(2^n))?p)  (gyroinv1 ?p)))"
          
            by (smt (verit, best) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) calculation(2)
                normed_gyrolinear_space''.gyromid_in_domain
                normed_gyrolinear_space''.isgyrometric_def)
        
         
          moreover have " \<forall>n::nat. ((f (q1 ((?S^^(2^n))?p) ?p)) \<le>  (f (oplus'1 (q1 (?p) (a))
      (q1 (a) ?p))))"
          proof
            fix n::nat
            show "((f (q1 ((?S^^(2^n))?p) ?p)) \<le>  (f (oplus'1 (q1 (?p) (a))
      (q1 (a) ?p))))"
            proof-
              have "q1 ?p a = q1 a ?p"
             
                by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) normed_gyrolinear_space''.gyrometric_sym
                    normed_gyrolinear_space''.gyromid_in_domain)
              moreover have  "q1 ?p a = norm'1 (gyroplus1 ?p (gyroinv1 a))"
             
                using \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) normed_gyrolinear_space''.gyromid_in_domain
                  normed_gyrolinear_space''.isgyrometric_def by fastforce
              moreover have "(gyroplus1 ?p (gyroinv1 a))\<in>dom1"
             
                by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1) gyrocommutative_gyrogroup_def gyrogroup.ax1
                    gyrogroup_def gyrogroupoid.gyroplus_closed gyrolinear_space_def
                    normed_gyrolinear_space''.gyromid_in_domain normed_gyrolinear_space''_def)
              moreover have "q1 ?p a \<in> (normed_gyrolinear_space''.norms dom1 norm'1)"
                
                by (metis assms(1) calculation(2,3) imageI normed_gyrolinear_space''.norms_def)     
              moreover have "    (q1 (a) ?p)    \<in> (normed_gyrolinear_space''.norms dom1 norm'1)"
               
                using calculation(1,4) by presburger

              moreover have "(\<forall>x y. x \<in> normed_gyrolinear_space''.norms_all dom1 norm'1 \<longrightarrow>
             y \<in> normed_gyrolinear_space''.norms_all dom1 norm'1 \<longrightarrow>
             oplus'1 x y \<in> normed_gyrolinear_space''.norms_all dom1 norm'1)"
       using one_dim_vector_space_with_domain_def
 vector_space_with_domain_def[of " (normed_gyrolinear_space''.norms_all dom1 norm'1)" oplus'1 0 otimes'1]
      
       by (smt (verit, del_insts) assms(1) normed_gyrolinear_space''.ax_space
           normed_gyrolinear_space''.norms_all_def normed_gyrolinear_space''.norms_def
           normed_gyrolinear_space''.norms_neg_def)
     moreover have "(q1 (?p) (a))\<in> normed_gyrolinear_space''.norms_all dom1 norm'1 "
      
       by (metis Un_iff assms(1) calculation(4)
           normed_gyrolinear_space''.norms_all_def)
     moreover have "q1 a ?p \<in> normed_gyrolinear_space''.norms_all dom1 norm'1"
      
       using calculation(1,7) by presburger
         moreover have "(oplus'1 (q1 (?p) (a)) 
      (q1 (a) ?p)) \<in> (normed_gyrolinear_space''.norms_all dom1 norm'1)"
         
           using calculation(6,7,8) by blast
          moreover have "(oplus'1 (q1 (?p) (a)) 
      (q1 (a) ?p)) \<in> (normed_gyrolinear_space''.norms dom1 norm'1)" 
         using
                      normed_gyrolinear_space''.norm_ineq[OF assms(1)]

         by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) calculation(9)
             normed_gyrolinear_space''.gyrom_id normed_gyrolinear_space''.gyrometric_triangle
             normed_gyrolinear_space''.gyromid_in_domain
             normed_gyrolinear_space''.order_dom2)
       moreover have "(q1 ((?S^^(2^n))?p) ?p) \<in>   (normed_gyrolinear_space''.norms dom1 norm'1)"
         
         by (smt (verit, ccfv_threshold)
             \<open>\<forall>n. \<forall>t\<in>dom1. (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) t \<in> dom1\<close>
             \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) gyrocommutative_gyrogroup_def gyrogroup.ax1
             gyrogroup_def gyrogroupoid.gyroplus_closed gyrolinear_space_def imageI
             normed_gyrolinear_space''.gyromid_in_domain normed_gyrolinear_space''.isgyrometric_def
             normed_gyrolinear_space''.norms_def normed_gyrolinear_space''_def)
       
       ultimately show ?thesis 
         by (smt (verit, ccfv_SIG)
             \<open>\<forall>n. oplus'1 (q1 ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) a)) (q1 ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) a) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) = oplus'1 (q1 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b) a) (q1 a (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b))\<close>
             \<open>\<forall>n. q1 ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b) \<le> oplus'1 (q1 ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) a)) (q1 ((((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) (gyroinv1 x) else undefined) \<circ> T) ^^ 2 ^ n) a) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b))\<close>
             \<open>bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x} \<and> (\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow> f z < f y) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x)) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (oplus'1 (norm'1 x) (norm'1 y)) = f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (otimes'1 \<bar>r\<bar> (norm'1 x)) = \<bar>r\<bar> * f (norm'1 x))\<close>)  
     qed
   qed
 

                
            moreover have "\<forall>n::nat. 2^(n+1) * ?d \<le> 2 * f(q1 a ?p)"
            
              by (smt (verit, ccfv_threshold) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close>
                  \<open>bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x} \<and> (\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow> f z < f y) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x)) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (oplus'1 (norm'1 x) (norm'1 y)) = f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (otimes'1 \<bar>r\<bar> (norm'1 x)) = \<bar>r\<bar> * f (norm'1 x))\<close>
                  assms(1,3) calculation(11,4) gyrocommutative_gyrogroup_def gyrogroup.ax1 gyrogroup_def
                  gyrogroupoid.gyroplus_closed gyrolinear_space_def
                  normed_gyrolinear_space''.gyrometric_sym normed_gyrolinear_space''.gyromid_in_domain
                  normed_gyrolinear_space''.isgyrometric_def normed_gyrolinear_space''_def)
            moreover have "?d = 0"
            proof-
              have "?d = f (q1 (T ?p) ?p')"
               
                by blast
              moreover have "?d \<ge>0"
              proof-
                have "bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x}"
                  
                  
                  using
                    \<open>bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x} \<and> (\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow> f z < f y) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x)) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (oplus'1 (norm'1 x) (norm'1 y)) = f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (otimes'1 \<bar>r\<bar> (norm'1 x)) = \<bar>r\<bar> * f (norm'1 x))\<close>
                  by blast
                moreover have "(T ?p)\<in>dom1"
                  
                  by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,2) imageI
                      normed_gyrolinear_space''.gyromid_in_domain)
                moreover have "?p' \<in> dom1"
                  
                  by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,2) imageI
                      normed_gyrolinear_space''.gyromid_in_domain)
                moreover have " q1 (T ?p) ?p' =
    norm'1 (gyroplus1 (T ?p) (gyroinv1 ?p'))"
  using normed_gyrolinear_space''.isgyrometric_def[OF assms(1), of q1]
                 `(T ?p)\<in>dom1` `?p'\<in>dom1` 
                 
                 using assms(3) by presburger
                moreover have "q1 (T ?p) ?p' \<in> (normed_gyrolinear_space''.norms dom1 norm'1)"
               
                  by (smt (verit, ccfv_threshold) assms(1,3) calculation(2,3)
                      gyrocommutative_gyrogroup_def gyrogroup_def gyrogroupoid.gyroplus_closed
                      gyrolinear_space.scale_closed gyrolinear_space.scale_minus1_inv gyrolinear_space_def
                      image_iff normed_gyrolinear_space''.isgyrometric_def
                      normed_gyrolinear_space''.norms_def normed_gyrolinear_space''_def)
                ultimately show ?thesis
                  by (metis bij_betw_iff_bijections mem_Collect_eq)
              qed
              moreover have "\<forall>n. n\<ge>0 \<longrightarrow> ?d \<le> n"
              proof-
                have "\<forall>n::nat. 2^(n+1) * ?d \<le> 2 * f(q1 a ?p)"
               
                  using
                    \<open>\<forall>n. 2 ^ (n + 1) * f (q1 (T (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b))) \<le> 2 * f (q1 a (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b))\<close>
                  by blast
                moreover have "f(q1 a ?p) \<ge>0"
                proof-
                  have "bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x}"
                    
                    using
                      \<open>bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x} \<and> (\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow> f z < f y) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x)) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (oplus'1 (norm'1 x) (norm'1 y)) = f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (otimes'1 \<bar>r\<bar> (norm'1 x)) = \<bar>r\<bar> * f (norm'1 x))\<close>
                    by blast
                moreover have "a\<in>dom1"
                  
                  using \<open>a \<in> dom1\<close> by auto
                moreover have "?p \<in> dom1"
                  
                  by (meson \<open>b \<in> dom1\<close> assms(1) calculation(2)
                      normed_gyrolinear_space''.gyromid_in_domain)
                moreover have " q1 a ?p =
    norm'1 (gyroplus1 a (gyroinv1 ?p))"
  using normed_gyrolinear_space''.isgyrometric_def[OF assms(1), of q1]
                 `a\<in>dom1` `?p\<in>dom1` 
                 
                 using assms(3) by presburger
                moreover have "q1 a ?p \<in> (normed_gyrolinear_space''.norms dom1 norm'1)"
               
                  by (smt (verit, ccfv_threshold) assms(1,3) calculation(2,3)
                      gyrocommutative_gyrogroup_def gyrogroup_def gyrogroupoid.gyroplus_closed
                      gyrolinear_space.scale_closed gyrolinear_space.scale_minus1_inv gyrolinear_space_def
                      image_iff normed_gyrolinear_space''.isgyrometric_def
                      normed_gyrolinear_space''.norms_def normed_gyrolinear_space''_def)
                ultimately show ?thesis
                  
                  by (meson bij_betw_iff_bijections mem_Collect_eq)
              qed
              moreover obtain "t" where "t=f (q1 a ?p)"
                by blast
              moreover have "\<forall>n::nat.  ((2::real) * t) / (2^(n+1)) \<ge>?d"
              proof-
                have "\<forall>n::nat. 2^(n+1) * ?d \<le> 2 * f(q1 a ?p)"
                  using calculation(1) by blast
                moreover have "\<forall>n::nat. (2::real)^(n+1) \<noteq> (0::real)"
                  by auto
                moreover have "\<forall>n::nat. (2::real)^(n+1) > 0"
                 
                  by simp
                ultimately show ?thesis
                  by (simp add:
                      \<open>t = f (q1 a (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b))\<close>
                      mult.commute pos_le_divide_eq)
              qed
               
 moreover have "\<forall>n::nat.  ( t/ (2^n)) \<ge>?d"
 proof-
   have "\<forall>n::nat.  ((2::real) * t) / (2^(n+1)) \<ge> ?d"
     using calculation(4) by blast
   moreover have "(2::real) \<noteq> (0::real)"
     by simp
   moreover have " \<forall>n::nat.  ((2::real) * t) / (2^(n+1)) = (((2::real) * t)/(2::real)) / ((2^(n+1))/(2::real))"
     
     by simp

   ultimately show ?thesis 
     by auto
 qed
              moreover have "\<forall>r::real. r>0 \<longrightarrow> (\<exists>n::nat. (t/ 2^n) \<le> r)"
              proof
                fix r::real
                show "r>0 \<longrightarrow> (\<exists>n::nat. (t/ 2^n) \<le> r)"
                proof
                  assume "r>0"
                  show " (\<exists>n::nat. (t/ 2^n) \<le> r)"
                  proof-
                  obtain "l" where "(l::nat) \<ge> log 2 (t/r)"
                  
                    by (meson real_arch_simple)
                  moreover have "2^l \<ge> (t/r)"
                   
                    by (smt (verit) calculation less_log_of_power)
                  
                  moreover have "t\<ge>0"
                    by (simp add:
                        \<open>0 \<le> f (q1 a (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b))\<close>
                        \<open>t = f (q1 a (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b))\<close>)
                  moreover have "t=0\<or>t\<noteq>0"
                    by blast
                  moreover {
                    assume "t=0"
                    then have ?thesis 
                      using \<open>0 < r\<close> by auto
                  }
                  moreover {
                    assume "t\<noteq>0"
                      then have ?thesis 
                    
                    by (smt (verit, ccfv_threshold) \<open>0 < r\<close> calculation(2) mult.commute pos_divide_le_eq
                        power_one_right)

                  }
                  ultimately show ?thesis 
                    by fastforce
                  
                qed
              qed
            qed
            moreover have "\<forall>r::real. r>0 \<longrightarrow> ?d \<le> r"
              using calculation(5,6) dual_order.trans by blast
            moreover have "?d \<ge>0"
              
              using
                \<open>0 \<le> f (q1 (T (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (T a) (T b)))\<close>
              by blast
            ultimately show ?thesis 
             
              by (metis dense linorder_less_linear linorder_not_less)
               
            qed
            ultimately show ?thesis 
              by force
            qed
            moreover have "f (q1 (T ?p) ?p') = 0"
          
              using calculation(13) by force
            ultimately show ?thesis
              by meson
          qed
        
            moreover have "norm'1 gyrozero1 = 0"
              
              by (meson assms(1) gyrocommutative_gyrogroup_def gyrogroup_def gyrogroupoid.zero_in_dom
                  gyrolinear_space_def normed_gyrolinear_space''.axioms(1)
                  normed_gyrolinear_space''.norm_zero)
             moreover have "bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x}"
              
           
               using
                 \<open>bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x} \<and> (\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow> f z < f y) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x)) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (oplus'1 (norm'1 x) (norm'1 y)) = f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (otimes'1 \<bar>r\<bar> (norm'1 x)) = \<bar>r\<bar> * f (norm'1 x))\<close>
               by blast
            (*moreover have "f 0 = 0 "
              sledgehammer
              using \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) calculation(13,5,8)
                normed_gyrolinear_space''.gyrom_id normed_gyrolinear_space''.gyromid_in_domain
              by fastforce
           *)
            moreover have "\<forall>t\<in>dom1. t\<noteq>gyrozero1 \<longrightarrow> norm'1 t > norm'1 gyrozero1"
              
              using assms(1) calculation(3) normed_gyrolinear_space''.norm_pos
                normed_gyrolinear_space''.norm_zero by fastforce
              
            moreover have "\<forall>t\<in>dom1. t\<noteq>gyrozero1 \<longrightarrow> f(norm'1 t) > f(norm'1 gyrozero1)"
            proof-
              have "(\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and>
               z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow>
               f z < f y)"
                
               
                using
                  \<open>bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x} \<and> (\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow> f z < f y) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x)) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (oplus'1 (norm'1 x) (norm'1 y)) = f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (otimes'1 \<bar>r\<bar> (norm'1 x)) = \<bar>r\<bar> * f (norm'1 x))\<close>
                by argo
              moreover have "\<forall>t\<in>dom1. norm'1 t\<in> normed_gyrolinear_space''.norms dom1 norm'1"
                
                by (metis assms(1) imageI normed_gyrolinear_space''.norms_def)
              moreover have "gyrozero1 \<in>dom1"
              
                by (meson assms(1) gyrocommutative_gyrogroup_def gyrogroup_def gyrogroupoid.zero_in_dom
                    gyrolinear_space_def normed_gyrolinear_space''_def)
              moreover have "norm'1 gyrozero1 \<in> normed_gyrolinear_space''.norms dom1 norm'1"
               
                using calculation(2,3) by fastforce
              ultimately show ?thesis 
                using \<open>\<forall>t\<in>dom1. t \<noteq> gyrozero1 \<longrightarrow> norm'1 gyrozero1 < norm'1 t\<close> by blast
            qed
            moreover have "f (norm'1 gyrozero1) = 0"
             
              by (metis
                  \<open>bij_betw f (normed_gyrolinear_space''.norms dom1 norm'1) {x. 0 \<le> x} \<and> (\<forall>y z. y \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z \<in> normed_gyrolinear_space''.norms dom1 norm'1 \<and> z < y \<longrightarrow> f z < f y) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (norm'1 (gyroplus1 x y)) \<le> f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (norm'1 (scale1 r x)) = \<bar>r\<bar> * f (norm'1 x)) \<and> (\<forall>x\<in>dom1. \<forall>y\<in>dom1. f (oplus'1 (norm'1 x) (norm'1 y)) = f (norm'1 x) + f (norm'1 y)) \<and> (\<forall>r. \<forall>x\<in>dom1. f (otimes'1 \<bar>r\<bar> (norm'1 x)) = \<bar>r\<bar> * f (norm'1 x))\<close>
                  abs_of_nonneg assms(1) bij_betw_iff_bijections calculation(3,6)
                  gyrocommutative_gyrogroup_def gyrogroup_def gyrogroupoid.zero_in_dom
                  gyrolinear_space.scale_closed gyrolinear_space_def imageI mem_Collect_eq
                  mult_zero_left normed_gyrolinear_space''.norms_def normed_gyrolinear_space''_def
                  order_antisym_conv order_le_less)
             
            
            moreover have "f (norm'1 (gyroplus1 (T ?p) (gyroinv1 ?p'))) =f (norm'1 gyrozero1)"
           
              by (smt (verit, del_insts) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,2,3) calculation(2,7) imageI
                  normed_gyrolinear_space''.gyromid_in_domain
                  normed_gyrolinear_space''.isgyrometric_def)
              
              
            moreover have "gyroplus1 (T ?p) (gyroinv1 ?p')\<in>dom1"
            proof-
              have "?p'\<in>dom1"
              
                by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,2) imageI
                    normed_gyrolinear_space''.gyromid_in_domain)
              moreover have "gyroinv1 ?p'\<in>dom1"
                
                by (metis assms(1) calculation gyrolinear_space.scale_closed
                    gyrolinear_space.scale_minus1_inv normed_gyrolinear_space''_def)
              moreover have "T ?p\<in>dom1"
                
                by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,2) imageI
                    normed_gyrolinear_space''.gyromid_in_domain)
              ultimately show ?thesis 
                by (metis assms(1) gyrocommutative_gyrogroup_def gyrogroup_def
                    gyrogroupoid.gyroplus_closed gyrolinear_space_def
                    normed_gyrolinear_space''_def)
            qed
            moreover have "norm'1 (gyroplus1 (T ?p) (gyroinv1 ?p'))\<in>  (normed_gyrolinear_space''.norms dom1 norm'1)"
              using normed_gyrolinear_space''.norms_def[OF assms(1)]
          
              using calculation(9) by blast
              
             (* using calculation(21) by blast*)
            moreover have "gyrozero1 \<in>dom1"
          
              by (meson assms(1) gyrocommutative_gyrogroup_def gyrogroup_def gyrogroupoid.zero_in_dom
                  gyrolinear_space_def normed_gyrolinear_space''_def)
            moreover have "(norm'1 gyrozero1) \<in>(normed_gyrolinear_space''.norms dom1 norm'1)"
               using normed_gyrolinear_space''.norms_def[OF assms(1)]
              
               
               using calculation(11) by blast
            
            moreover have "(norm'1 (gyroplus1 (T ?p) (gyroinv1 ?p'))) = (norm'1 gyrozero1)"
              
             
              using calculation(6,8,9) by auto
              (*using calculation(18,20,21)  by fastforce*)
            moreover have "T ?p = ?p'"
              by (smt (verit, best) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,2,3) calculation(13,3) imageI
                  normed_gyrolinear_space''.gyrom_id2 normed_gyrolinear_space''.gyromid_in_domain
                  normed_gyrolinear_space''.isgyrometric_def)
            
                ultimately show ?thesis 
                  
                  by argo
              qed
            qed
          qed
        
            
              

lemma mazur_ulam:
  fixes dom1::"'a set" 
  fixes dom2::"'b set"
  fixes T::"'a\<Rightarrow>'b"
  assumes "normed_gyrolinear_space'' dom2 gyrozero2 gyroplus2 gyroinv2 gyr2 scale2 norm'2 oplus'2 otimes'2"
  "normed_gyrolinear_space'' dom1 gyrozero1 gyroplus1 gyroinv1 gyr1 scale1 norm'1 oplus'1 otimes'1"
   "T ` dom1 = dom2" 
  "normed_gyrolinear_space''.isgyrometric dom2 gyroplus2 gyroinv2 norm'2  q2"
  "normed_gyrolinear_space''.isgyrometric dom1 gyroplus1 gyroinv1 norm'1  q1"
  "\<forall>a\<in>dom1. \<forall>b\<in>dom1. q2 (T a) (T b) = q1 a b"
  "\<exists>x\<in>dom2. x\<noteq>gyrozero2"
"(\<forall>y\<in>dom2. \<exists>x\<in>dom1. T x = y)"
shows "\<forall>a\<in>dom1. \<forall>b\<in>dom1. ((normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2  gyr2 scale2)
 (T a) (T b) = T ((normed_gyrolinear_space''.gyromid  dom1 gyroplus1 gyroinv1  gyr1 scale1) a b))"
proof
fix a
  assume "a\<in>dom1"
  show "  \<forall>b\<in>dom1.
            normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a)
             (T b) =
            T (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)"
  proof
    fix b
    assume "b\<in>dom1"
    show  "normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a)
             (T b) =
            T (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)"
    proof-
      let ?p = "normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b"
      let ?p' = "normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a)
             (T b)"
      let ?norms2 = " norm'2 ` dom2 \<union> (\<lambda>x. - 1 * norm'2 x) ` dom2"
       
 
      let ?phi_p = "\<lambda>x. (if x \<in> dom1 then gyroplus1 (scale1 2 ?p) (gyroinv1 x) else undefined)"
      let ?phi_p' = "\<lambda>x. (if x \<in> dom2 then gyroplus2 (scale2 2 ?p') (gyroinv2 x) else undefined)"
      let ?S = "(?phi_p \<circ>(inv_into dom1 T)\<circ>?phi_p' \<circ> T)"
      have "inj_on T dom1"
        by (metis (no_types, opaque_lifting) assms(2,5,6) inj_onI
            normed_gyrolinear_space''.gyrom_id normed_gyrolinear_space''.gyrom_id2)
      moreover have "?S ` dom1 = dom1"
        using mazur_ulam_help1[OF assms(1) assms(2), of T, OF assms(3) assms(4) assms(5), of a b, OF `a\<in>dom1` `b\<in>dom1`, OF assms(6) assms(7) assms(8), of ?p ?p' ?phi_p]
   
        by presburger
                    
   (*   proof-
        have " T ` dom1 = dom2 "
          using assms(3) by blast
        moreover have "(?phi_p' \<circ> T) ` dom1 = dom2"
        proof-
          have "\<forall>x\<in>dom1. ((?phi_p' \<circ> T) x) \<in> dom2"
          proof
            fix x 
            assume "x\<in>dom1"
            show "((?phi_p' \<circ> T) x) \<in> dom2"
            proof-
              have "T x \<in> dom2"
                using \<open>x \<in> dom1\<close> calculation by blast
              moreover have "?phi_p' (T x) \<in> dom2"
                by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) calculation gyrocommutative_gyrogroup_def
                    gyrogroup.ax1 gyrogroup_def gyrogroupoid.gyroplus_closed gyrolinear_space.scale_closed
                    gyrolinear_space_def imageI normed_gyrolinear_space''.gyromid_in_domain
                    normed_gyrolinear_space''_def)
              ultimately show ?thesis
                by fastforce
            qed
          qed
          moreover have "\<forall>x\<in>dom2. \<exists>y\<in>dom1. ((?phi_p' \<circ> T) y) = x"
          proof
            fix x
            assume "x\<in>dom2"
            show " \<exists>y\<in>dom1. ((?phi_p' \<circ> T) y) = x"
            proof-
              obtain "y" where "y = ((inv_into dom1 T) \<circ> ?phi_p') x "
                by blast
              moreover have " ((?phi_p' \<circ> T) y) =  ((?phi_p' \<circ> T) (((inv_into dom1 T) \<circ> ?phi_p') x))"
                using calculation by force
              moreover have "(T \<circ> (inv_into dom1 T)) (?phi_p' x) = (?phi_p' x)"
                by (smt (verit, ccfv_SIG)
                    \<open>\<forall>x\<in>dom1. ((\<lambda>x. if x \<in> dom2 then gyroplus2 (scale2 2 (normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a) (T b))) (gyroinv2 x) else undefined) \<circ> T) x \<in> dom2\<close>
                    \<open>x \<in> dom2\<close> assms(3,8) comp_apply f_inv_into_f)
               moreover have "?p' \<in>dom2"
            
        
                 by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) imageI
                     normed_gyrolinear_space''.gyromid_in_domain)
                  moreover have "\<forall>z\<in>dom2. (?phi_p' \<circ> ?phi_p') z = z"
                  proof 
                    fix z
                    assume "z\<in>dom2"
                    show "(?phi_p' \<circ> ?phi_p') z = z"
                      using normed_gyrolinear_space''.proposition16_hatori_abe_p1_v2[OF assms(1) `?p' \<in>dom2`]
                
                      by (simp add: \<open>z \<in> dom2\<close>)
                    
                   
                
                  qed
              moreover have "?phi_p' (?phi_p' x) = x"
             
                using \<open>x \<in> dom2\<close> calculation(5) by fastforce
              ultimately show ?thesis 
                by (metis (no_types, lifting)
                    \<open>\<forall>x\<in>dom1. ((\<lambda>x. if x \<in> dom2 then gyroplus2 (scale2 2 (normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a) (T b))) (gyroinv2 x) else undefined) \<circ> T) x \<in> dom2\<close>
                    \<open>x \<in> dom2\<close> assms(3) comp_apply f_inv_into_f inv_into_into)
            qed
          qed 
          moreover have "(?phi_p' \<circ> T) ` dom1 \<subseteq> dom2"
          
            using calculation(1) by blast
          moreover have "dom2 \<subseteq>(?phi_p' \<circ> T) ` dom1 "
            
            using calculation(2) by fastforce
          ultimately show ?thesis by fastforce
        qed
          moreover have "((inv_into dom1 T)\<circ> ?phi_p' \<circ> T) ` dom1 = dom1"
          proof-
               have *:"\<forall>x\<in>dom1. ((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x\<in> dom1"
             
                
                 by (metis (lifting) calculation(1,2) comp_eq_dest_lhs imageI inv_into_into)
               moreover have "\<forall>x\<in>dom1. \<exists>y\<in>dom1. (((inv_into dom1 T)\<circ> ?phi_p' \<circ> T) y) = x"
                 
             
                 by (smt (verit, best)
                     \<open>((\<lambda>x. if x \<in> dom2 then gyroplus2 (scale2 2 (normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a) (T b))) (gyroinv2 x) else undefined) \<circ> T) ` dom1 = dom2\<close>
                     \<open>inj_on T dom1\<close> assms(3) imageE imageI image_comp inv_into_f_f)
               moreover have "((inv_into dom1 T)\<circ> ?phi_p' \<circ> T) ` dom1 \<subseteq> dom1"
                 using calculation(1) by blast
               moreover have "dom1 \<subseteq> ((inv_into dom1 T)\<circ> ?phi_p' \<circ> T) ` dom1"
               
                 using calculation(2) by fastforce
               ultimately show ?thesis 
                 by fastforce
             qed
             moreover have "( ?phi_p \<circ> (inv_into dom1 T)\<circ> ?phi_p' \<circ> T) ` dom1 = dom1"
             proof-
               have "\<forall>x\<in>dom1. ( ?phi_p \<circ> (inv_into dom1 T)\<circ> ?phi_p' \<circ> T) x \<in> dom1"
               proof
                 fix x 
                 assume "x\<in>dom1"
                 show " ( ?phi_p \<circ> (inv_into dom1 T)\<circ> ?phi_p' \<circ> T) x \<in> dom1"
                 proof-
                   have "  ((inv_into dom1 T)\<circ> ?phi_p' \<circ> T) x \<in> dom1"
                    
                     
                     using \<open>x \<in> dom1\<close> calculation(3) by blast
                   moreover have "?phi_p ( ((inv_into dom1 T)\<circ> ?phi_p' \<circ> T) x) =
   gyroplus1 (scale1 2 ?p) (gyroinv1 ( ((inv_into dom1 T)\<circ> ?phi_p' \<circ> T) x))"
                     
                     using calculation by argo
                   moreover have "(gyroinv1 ( ((inv_into dom1 T)\<circ> ?phi_p' \<circ> T) x))\<in>dom1"
                   
                     by (metis (no_types, lifting) assms(2) calculation(1) gyrolinear_space.scale_closed
                         gyrolinear_space.scale_minus1_inv normed_gyrolinear_space''_def)
                   moreover have "(scale1 2 ?p)\<in>dom1"
               
                     by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(2) gyrolinear_space.scale_closed
                         normed_gyrolinear_space''.gyromid_in_domain normed_gyrolinear_space''_def)
                   moreover have "gyroplus1 (scale1 2 ?p) (gyroinv1 ( ((inv_into dom1 T)\<circ> ?phi_p' \<circ> T) x))\<in>dom1"
                 
                     using assms(2) calculation(3,4) gyrocommutative_gyrogroup_def gyrogroup_def
                       gyrogroupoid.gyroplus_closed gyrolinear_space_def normed_gyrolinear_space''_def
                     by fastforce
                   ultimately show ?thesis 
                     by auto
                     
                 qed
               qed
               moreover  have "\<forall>x\<in>dom1. \<exists>y\<in>dom1. ((?phi_p\<circ>(inv_into dom1 T)\<circ> ?phi_p' \<circ> T) y) = x"
               proof
                 fix x 
                 assume "x\<in>dom1"
                 show "\<exists>y\<in>dom1. ((?phi_p\<circ>(inv_into dom1 T)\<circ> ?phi_p' \<circ> T) y) = x"
                 proof-
                     have "\<forall>x\<in>dom1. \<exists>y\<in>dom1. (((inv_into dom1 T)\<circ> ?phi_p' \<circ> T) y) = x"
                    
                       by (metis (no_types, lifting)
                           \<open>(inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom2 then gyroplus2 (scale2 2 (normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a) (T b))) (gyroinv2 x) else undefined) \<circ> T) ` dom1 = dom1\<close>
                           image_iff)
               moreover obtain "t" where "t=?phi_p x"
               
                 by auto
               moreover obtain "t2" where "((inv_into dom1 T)\<circ> ?phi_p' \<circ> T)  t2 = ?phi_p x"
                 
                 by (smt (verit, best)
                     \<open>\<forall>x\<in>dom1. ((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom2 then gyroplus2 (scale2 2 (normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a) (T b))) (gyroinv2 x) else undefined) \<circ> T) x \<in> dom1\<close>
                     \<open>x \<in> dom1\<close> calculation(1) comp_apply)
                 moreover have "?p \<in>dom1"
            
        
                   
                   by (meson \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(2)
                       normed_gyrolinear_space''.gyromid_in_domain)
                  moreover have "\<forall>z\<in>dom1. (?phi_p \<circ> ?phi_p) z = z"
                  proof 
                    fix z
                    assume "z\<in>dom1"
                    show "(?phi_p \<circ> ?phi_p) z = z"
                      using normed_gyrolinear_space''.proposition16_hatori_abe_p1_v2[OF assms(2) `?p\<in>dom1`]
                
                      by (simp add: \<open>z \<in> dom1\<close>)
                    
                   
                
                  qed
                  ultimately show ?thesis
                    by (metis (no_types, lifting)
                        \<open>\<forall>x\<in>dom1. ((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom2 then gyroplus2 (scale2 2 (normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a) (T b))) (gyroinv2 x) else undefined) \<circ> T) x \<in> dom1\<close>
                        \<open>x \<in> dom1\<close> comp_def)
                qed
              qed
              moreover have "( ?phi_p \<circ> (inv_into dom1 T)\<circ> ?phi_p' \<circ> T) ` dom1 \<subseteq> dom1"
               
                using calculation(1) by blast
              moreover have "dom1 \<subseteq>( ?phi_p \<circ> (inv_into dom1 T)\<circ> ?phi_p' \<circ> T) ` dom1 "
                
                using calculation(2) by fastforce
              ultimately show ?thesis 
                by fastforce
             qed
                  
         
           ultimately show ?thesis 
            
             by meson
         qed
      *)
      moreover  have "\<forall>x\<in>dom1. \<forall>y\<in>dom1. q1 (?S x) (?S y) = q1 x y"
      proof
        fix x
        assume "x\<in>dom1"
        show "\<forall>y\<in>dom1. q1 (?S x) (?S y) = q1 x y"
        proof
          fix y   
          assume "y\<in>dom1"
          show "q1 (?S x) (?S y) = q1 x y"
          proof-
            have "q2 (T x) (T y) = q1 x y"
              using \<open>x \<in> dom1\<close> \<open>y \<in> dom1\<close> assms(6) by blast
            moreover have "q2 (?phi_p' (T x)) (?phi_p' (T y)) = q2 (T x) (T y)"
            
              by (smt (verit, ccfv_threshold) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> \<open>x \<in> dom1\<close> \<open>y \<in> dom1\<close>
                  assms(1,3,4) gyrocommutative_gyrogroup_def gyrogroup.ax1 gyrolinear_space.scale_closed
                  gyrolinear_space_def imageI normed_gyrolinear_space''.gyromid_in_domain
                  normed_gyrolinear_space''.gyromid_minus_sym
                  normed_gyrolinear_space''.proposition15_hatori_abe
                  normed_gyrolinear_space''_def)
            moreover have "q1 ((inv_into dom1 T) (?phi_p' (T x))) ((inv_into dom1 T)((?phi_p' (T y)))) = q2 (?phi_p' (T x)) (?phi_p' (T y))"     
              
              by (smt (verit, ccfv_threshold) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> \<open>x \<in> dom1\<close> \<open>y \<in> dom1\<close>
                  assms(1,3,6) f_inv_into_f gyrocommutative_gyrogroup_def gyrogroup_def
                  gyrogroupoid.gyroplus_closed gyrolinear_space.scale_closed
                  gyrolinear_space.scale_minus1_inv gyrolinear_space_def imageI inv_into_into
                  normed_gyrolinear_space''.gyromid_in_domain normed_gyrolinear_space''_def)
            moreover have "?p\<in>dom1"
            
              by (meson \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(2)
                  normed_gyrolinear_space''.gyromid_in_domain)
            moreover have "(((inv_into dom1 T) (?phi_p' (T x))))\<in>dom1"
            
              by (smt (verit, ccfv_threshold) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> \<open>x \<in> dom1\<close> assms(1,3)
                  gyrocommutative_gyrogroup_def gyrogroup_def gyrogroupoid.gyroplus_closed
                  gyrolinear_space.scale_closed gyrolinear_space.scale_minus1_inv gyrolinear_space_def
                  imageI inv_into_into normed_gyrolinear_space''.gyromid_in_domain
                  normed_gyrolinear_space''_def)
 moreover have "(((inv_into dom1 T) (?phi_p' (T y))))\<in>dom1"
            
              by (smt (verit, ccfv_threshold) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> \<open>y \<in> dom1\<close> assms(1,3)
                  gyrocommutative_gyrogroup_def gyrogroup_def gyrogroupoid.gyroplus_closed
                  gyrolinear_space.scale_closed gyrolinear_space.scale_minus1_inv gyrolinear_space_def
                  imageI inv_into_into normed_gyrolinear_space''.gyromid_in_domain
                  normed_gyrolinear_space''_def)
            moreover have "q1 ((inv_into dom1 T) (?phi_p' (T x))) ((inv_into dom1 T)((?phi_p' (T y)))) =
  q1 (?phi_p (((inv_into dom1 T) (?phi_p' (T x))))) (?phi_p (((inv_into dom1 T)((?phi_p' (T y))))))"
              using normed_gyrolinear_space''.proposition16_hatori_abe_p2[OF assms(2) `?p\<in>dom1`]
              `(((inv_into dom1 T) (?phi_p' (T x))))\<in>dom1`
               `(((inv_into dom1 T) (?phi_p' (T y))))\<in>dom1`
              
              using assms(5) by fastforce
              
            ultimately show ?thesis 
              by simp
          qed
        qed
      qed
    
      moreover have "?S ?p = (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1  gyr1 scale1)
 (?S a) (?S b)"
        using mazur_ulam_sameG[OF assms(2), of ?S]
        by (smt (verit) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(2,5) calculation(2,3) f_inv_into_f
            inv_into_into normed_gyrolinear_space''.gyromid_in_domain)
      moreover have "?S ?p = ?p"
      proof-
        have "?S a = a"
        proof-
          have "?p' \<in> dom2"
        
            by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) imageI
                normed_gyrolinear_space''.gyromid_in_domain)
          moreover have "?phi_p' (T a)  = (T b)"
            using normed_gyrolinear_space''.proposition16_hatori_abe_p4[OF assms(2)]
            by (smt (verit, ccfv_SIG) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) calculation imageI
                normed_gyrolinear_space''.proposition16_hatori_abe_p4)
          moreover have "(inv_into dom1 T) (?phi_p' (T a)) =  (inv_into dom1 T) (T b)"
            using calculation(2) by argo
          moreover have "(inv_into dom1 T) (?phi_p' (T a)) = b"
            by (simp add: \<open>b \<in> dom1\<close> \<open>inj_on T dom1\<close> calculation(2))
          moreover have "?p \<in> dom1"
            
            by (meson \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(2)
                normed_gyrolinear_space''.gyromid_in_domain)
          moreover have "?phi_p b = a"
           
            by (smt (verit, ccfv_SIG) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(2) calculation(5)
                normed_gyrolinear_space''.proposition16_hatori_abe_p4)
          ultimately show ?thesis 
            by (simp add: \<open>b \<in> dom1\<close>)  
        qed
        moreover have "?S b = b"
        proof-
          have "?p' \<in> dom2"
        
            by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) imageI
                normed_gyrolinear_space''.gyromid_in_domain)
          moreover have "?phi_p' (T b)  = (T a)"
            using normed_gyrolinear_space''.proposition16_hatori_abe_p4[OF assms(2)]
            by (smt (verit, ccfv_SIG) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) calculation imageI
                normed_gyrolinear_space''.proposition16_hatori_abe_p4)
          moreover have "(inv_into dom1 T) (?phi_p' (T b)) =  (inv_into dom1 T) (T a)"
            using calculation(2) by argo
          moreover have "(inv_into dom1 T) (?phi_p' (T b)) = a"
            by (simp add: \<open>a \<in> dom1\<close> \<open>inj_on T dom1\<close> calculation(2))
          moreover have "?p \<in> dom1"
            
            by (meson \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(2)
                normed_gyrolinear_space''.gyromid_in_domain)
          moreover have "?phi_p a = b"
           
            by (smt (verit, ccfv_SIG) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(2) calculation(5)
                normed_gyrolinear_space''.proposition16_hatori_abe_p4)
          ultimately show ?thesis 
            by (simp add: \<open>a \<in> dom1\<close>)  
        qed
        ultimately show ?thesis 
          using
            \<open>((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom2 then gyroplus2 (scale2 2 (normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a) (T b))) (gyroinv2 x) else undefined) \<circ> T) (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b) = normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom2 then gyroplus2 (scale2 2 (normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a) (T b))) (gyroinv2 x) else undefined) \<circ> T) a) (((\<lambda>x. if x \<in> dom1 then gyroplus1 (scale1 2 (normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b)) (gyroinv1 x) else undefined) \<circ> inv_into dom1 T \<circ> (\<lambda>x. if x \<in> dom2 then gyroplus2 (scale2 2 (normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a) (T b))) (gyroinv2 x) else undefined) \<circ> T) b)\<close>
          by argo
      qed
      moreover have "(?phi_p' \<circ> T) ?p = T ?p" 
      proof-
        have "?phi_p (((?phi_p \<circ> (inv_into dom1 T)\<circ> ?phi_p' \<circ> T)) ?p) = ?phi_p ?p"
          using calculation(5) by presburger
        moreover have "?p \<in> dom1"
         
          by (meson \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(2)
              normed_gyrolinear_space''.gyromid_in_domain)
   moreover have "\<forall>z\<in>dom1. (?phi_p \<circ> ?phi_p) z = z"
                  proof 
                    fix z
                    assume "z\<in>dom1"
                    show "(?phi_p \<circ> ?phi_p) z = z"
                      using normed_gyrolinear_space''.proposition16_hatori_abe_p1_v2[OF assms(2)]             
                    
                      by (simp add: \<open>z \<in> dom1\<close> calculation(2))
                
                  qed
                  moreover have "((inv_into dom1 T)\<circ> ?phi_p' \<circ> T) ?p\<in> dom1"

       proof-
         have " T ` dom1 = dom2 "
          using assms(3) by blast
        moreover have "(?phi_p' \<circ> T) ` dom1 = dom2"
        proof-
          have "\<forall>x\<in>dom1. ((?phi_p' \<circ> T) x) \<in> dom2"
          proof
            fix x 
            assume "x\<in>dom1"
            show "((?phi_p' \<circ> T) x) \<in> dom2"
            proof-
              have "T x \<in> dom2"
                using \<open>x \<in> dom1\<close> calculation by blast
              moreover have "?phi_p' (T x) \<in> dom2"
                by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) calculation gyrocommutative_gyrogroup_def
                    gyrogroup.ax1 gyrogroup_def gyrogroupoid.gyroplus_closed gyrolinear_space.scale_closed
                    gyrolinear_space_def imageI normed_gyrolinear_space''.gyromid_in_domain
                    normed_gyrolinear_space''_def)
              ultimately show ?thesis
                by fastforce
            qed
          qed
          moreover have "\<forall>x\<in>dom2. \<exists>y\<in>dom1. ((?phi_p' \<circ> T) y) = x"
          proof
            fix x
            assume "x\<in>dom2"
            show " \<exists>y\<in>dom1. ((?phi_p' \<circ> T) y) = x"
            proof-
              obtain "y" where "y = ((inv_into dom1 T) \<circ> ?phi_p') x "
                by blast
              moreover have " ((?phi_p' \<circ> T) y) =  ((?phi_p' \<circ> T) (((inv_into dom1 T) \<circ> ?phi_p') x))"
                using calculation by force
              moreover have "(T \<circ> (inv_into dom1 T)) (?phi_p' x) = (?phi_p' x)"
                by (smt (verit, ccfv_SIG)
                    \<open>\<forall>x\<in>dom1. ((\<lambda>x. if x \<in> dom2 then gyroplus2 (scale2 2 (normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a) (T b))) (gyroinv2 x) else undefined) \<circ> T) x \<in> dom2\<close>
                    \<open>x \<in> dom2\<close> assms(3,8) comp_apply f_inv_into_f)
               moreover have "?p' \<in>dom2"
            
        
                 by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) imageI
                     normed_gyrolinear_space''.gyromid_in_domain)
                  moreover have "\<forall>z\<in>dom2. (?phi_p' \<circ> ?phi_p') z = z"
                  proof 
                    fix z
                    assume "z\<in>dom2"
                    show "(?phi_p' \<circ> ?phi_p') z = z"
                      using normed_gyrolinear_space''.proposition16_hatori_abe_p1_v2[OF assms(1) `?p' \<in>dom2`]
                
                      by (simp add: \<open>z \<in> dom2\<close>)
                    
                   
                
                  qed
              moreover have "?phi_p' (?phi_p' x) = x"
             
                using \<open>x \<in> dom2\<close> calculation(5) by fastforce
              ultimately show ?thesis 
                by (metis (no_types, lifting)
                    \<open>\<forall>x\<in>dom1. ((\<lambda>x. if x \<in> dom2 then gyroplus2 (scale2 2 (normed_gyrolinear_space''.gyromid dom2 gyroplus2 gyroinv2 gyr2 scale2 (T a) (T b))) (gyroinv2 x) else undefined) \<circ> T) x \<in> dom2\<close>
                    \<open>x \<in> dom2\<close> assms(3) comp_apply f_inv_into_f inv_into_into)
            qed
          qed 
          moreover have "(?phi_p' \<circ> T) ` dom1 \<subseteq> dom2"
          
            using calculation(1) by blast
          moreover have "dom2 \<subseteq>(?phi_p' \<circ> T) ` dom1 "
            
            using calculation(2) by fastforce
          ultimately show ?thesis by fastforce
        qed
        moreover
               have *:"\<forall>x\<in>dom1. ((inv_into dom1 T)\<circ>?phi_p' \<circ> T) x\<in> dom1"
             
                
                 by (metis (lifting) calculation(1,2) comp_eq_dest_lhs imageI inv_into_into)
               ultimately show ?thesis 
                 using
                   \<open>normed_gyrolinear_space''.gyromid dom1 gyroplus1 gyroinv1 gyr1 scale1 a b \<in> dom1\<close>
                 by fastforce
         qed
       
            
         moreover have "?phi_p (((?phi_p \<circ> (inv_into dom1 T)\<circ> ?phi_p' \<circ> T)) ?p) =
( (inv_into dom1 T)\<circ> ?phi_p' \<circ> T) ?p"
        
        
           using calculation(3,4) by fastforce
         moreover have "T (( (inv_into dom1 T)\<circ> ?phi_p' \<circ> T) ?p) = (?phi_p' \<circ> T) ?p"
        
           by (smt (verit, ccfv_threshold) \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) calculation(2)
               comp_apply f_inv_into_f gyrocommutative_gyrogroup_def gyrogroup_def
               gyrogroupoid.gyroplus_closed gyrolinear_space.scale_closed
               gyrolinear_space.scale_minus1_inv gyrolinear_space_def imageI
               normed_gyrolinear_space''.gyromid_in_domain normed_gyrolinear_space''_def)
         ultimately show ?thesis       
          
           by (smt (verit, ccfv_SIG) assms(2) gyrolinear_space.scale_1
               gyrolinear_space.scale_distrib gyrolinear_space.scale_minus1_inv
               normed_gyrolinear_space''_def)
         qed
      moreover have "?p'\<in>dom2"
        by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(1,3) imageI
            normed_gyrolinear_space''.gyromid_in_domain)
      moreover have "T ?p \<in> dom2"
        by (metis \<open>a \<in> dom1\<close> \<open>b \<in> dom1\<close> assms(2,3) imageI
            normed_gyrolinear_space''.gyromid_in_domain)
      ultimately show ?thesis 
        using normed_gyrolinear_space''.proposition16_hatori_abe_p3[OF assms(1) `?p'\<in>dom2`]
        by auto
     
    qed
  qed
qed
  

end
