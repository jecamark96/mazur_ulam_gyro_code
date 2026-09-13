theory Example 
  imports Main HOL.Transcendental GyroGroup GGV  Bijection_Intervals
begin

definition "G" where 
  "G = {x::real. (x<(-1) \<or> x\<ge>1)}"

definition "phi" where
  "phi x = (if (x\<ge>0) then (exp x) else (- (exp (-x))))"


lemma phi_is_bij:
  shows "bij_betw phi UNIV G"
proof -
  let ?psi = "\<lambda>y::real. if 0 \<le> y then ln y else - ln (-y)"

  have left_inv: "?psi (phi x) = x" for x
    by (cases "0 \<le> x") (simp_all add: phi_def)

  have inj: "inj (phi :: real \<Rightarrow> real)"
    by (rule inj_on_inverseI[where g="?psi"])
       (simp add: left_inv)

  have into: "phi ` UNIV \<subseteq> G"
    by (auto simp: phi_def G_def split: if_splits)

  have onto: "G \<subseteq> phi ` UNIV"
  proof
    fix y
    assume yG: "y \<in> G"

    show "y \<in> phi ` UNIV"
    proof (cases "1 \<le> y")
      case True
      have ypos: "0 < y"
        using True by linarith

      have "phi (ln y) = y"
        using True ypos by (simp add: phi_def)
      then show ?thesis
        by (metis UNIV_I image_eqI)
    next
      case False
      have yneg: "y < -1"
        using yG False by (auto simp: G_def)

      have ypos: "0 < -y"
        using yneg by linarith

      have lnpos: "0 < ln (-y)"
        by (rule ln_gt_zero) (use yneg in linarith)

      have "phi (- ln (-y)) = y"
        using ypos lnpos by (simp add: phi_def)
      then show ?thesis
        by (metis UNIV_I image_eqI)
    qed
  qed

  show ?thesis
    using inj into onto
    by (auto simp: bij_betw_def)
qed

definition "opluss"::"real \<Rightarrow> real \<Rightarrow> real" where
  "opluss a b = (if (a\<in>G \<and> b\<in>G) then (phi 
(((inv_into UNIV phi) a) + ((inv_into UNIV phi) b)) ) else undefined)"

interpretation grc: gyrogroupoid G 1 opluss
proof
  show "1 \<in> G"
    by (simp add: G_def)
next
  show " \<And>a b. a \<in> G \<and> b \<in> G \<longrightarrow> opluss a b \<in> G"
    by (metis bij_betw_imp_surj_on opluss_def phi_is_bij rangeI)
next
  show "\<exists>a. a \<in> G \<and> a \<noteq> 1"
    by (metis (no_types, lifting) G_def add.inverse_inverse bij_betw_def
        mem_Collect_eq neg_0_le_iff_le order_less_irrefl phi_def phi_is_bij rangeI
        zero_le_one zero_less_one)
qed

interpretation ggc: gyrocommutative_gyrogroup G "1::real" opluss "(phi 
\<circ> (\<lambda>x. -1 * ((inv_into UNIV phi) x)))" "\<lambda>a. (\<lambda>b. (\<lambda>x. x))"
proof

  show "\<And>a. a \<in> G \<longrightarrow> (phi \<circ> (\<lambda>x. - 1 * inv phi x)) a \<in> G"
    by (metis phi_is_bij bij_betw_def range_eqI comp_def)
next
  show "\<And>a b c. a \<in> G \<and> b \<in> G \<and> c \<in> G \<longrightarrow> c \<in> G"
    by auto
next
  show "\<And>a. a \<in> G \<longrightarrow> opluss 1 a = a"
  proof-
    fix a 
    show " a \<in> G \<longrightarrow> opluss 1 a = a"
    proof
      assume "a \<in> G"
      show " opluss 1 a = a"
      proof-
        have "1\<in>G"
          
          by (simp add: G_def)
        moreover have "opluss 1 a = phi ((inv phi 1) + (inv phi a))"
          using opluss_def
          using opluss_def calculation \<open>a \<in> G\<close> by simp
        moreover have "inv phi 1 = (0::real)"
        proof-
          have "0\<le>(0::real)"
            
            by simp
          moreover have "phi (0::real) =1"
            using phi_def[of 0] exp_zero  
           
            by (metis \<open>phi 0 = (if 0 \<le> 0 then exp 0 else - exp (- 0))\<close> exp_zero \<open>phi 0 = (if 0 \<le> 0 then exp 0 else - exp (- 0))\<close> dual_order.refl) 
        ultimately show ?thesis 
          by (metis bij_betw_def inv_f_f phi_is_bij)
      qed
      ultimately show ?thesis 
        by (metis (no_types, opaque_lifting) \<open>a \<in> G\<close> add_0 bij_betw_def imageE inv_f_eq
            phi_is_bij)
    qed
  qed
qed
next
  show " \<And>a. a \<in> G \<longrightarrow> opluss ((phi \<circ> (\<lambda>x. - 1 * inv phi x)) a) a = 1"
    by (smt (verit) bij_betw_def comp_def exp_zero inv_f_eq opluss_def phi_def
        phi_is_bij rangeI)
next
  show " \<And>a b z.
       a \<in> G \<and> b \<in> G \<and> z \<in> G \<longrightarrow> opluss a (opluss b z) = opluss (opluss a b) z"
    by (smt (verit, del_insts) One_nat_def bij_betw_def inv_f_eq opluss_def
        phi_is_bij range_eqI top_set_def)
next
  show "\<And>a b. a \<in> G \<and> b \<in> G \<longrightarrow> (\<forall>x\<in>G. x = x)"
    by auto
next
  show "\<And>x y. x \<in> G \<and> y \<in> G \<longrightarrow> gyrogroupoid.gyroaut G opluss (\<lambda>x. x)"
  proof-
    fix x y 
    show " x \<in> G \<and> y \<in> G \<longrightarrow> gyrogroupoid.gyroaut G opluss (\<lambda>x. x)"
    proof
      assume "x \<in> G \<and> y \<in> G"
      show "gyrogroupoid.gyroaut G opluss (\<lambda>x. x)"
      proof-
        have "bij_betw (\<lambda>x. x) G G"
          by (simp add: bij_betwI')
        moreover have "(\<lambda>x. x) (opluss x y) = opluss ((\<lambda>x. x)x) ((\<lambda>x. x) y)"
        
          by presburger
        moreover have "gyrogroupoid G 1 opluss"
        
          by (metis grc.gyrogroupoid_axioms)
        ultimately show ?thesis 
          using gyrogroupoid.gyroaut_def[of G 1 opluss]
          
          by blast
      qed
    qed
  qed
next
  show " \<forall>a\<in>G. \<forall>b\<in>G. opluss a b = opluss b a"
    by (simp add: add.commute opluss_def)
qed

definition otimess::"real\<Rightarrow> real \<Rightarrow> real" where
  "otimess r x = (if (x \<in> G) then phi (r * (inv phi x)) else undefined)"

lemma scale_closed_check:
  shows  "\<forall>r::real. (\<forall>x\<in>G. ((otimess r x) \<in> G))"
  by (metis phi_is_bij otimess_def UNIV_I bij_betw_iff_bijections)

lemma scale_1_check:
  shows "\<forall>a\<in>G. otimess (1::real) a = a"
proof
  fix a
  assume "a\<in>G"
  show " otimess (1::real) a = a"
    by (metis (no_types, lifting) \<open>a \<in> G\<close> bij_betw_def f_inv_into_f otimess_def
        phi_is_bij real_scaleR_def scaleR_one)
qed


lemma scale_distrib_check:
  shows "\<forall>r1::real. \<forall>r2::real.\<forall>a\<in>G. otimess (r1+r2) a =
 opluss (otimess r1 a) (otimess r2 a)"
proof
  fix r1
  show " \<forall>r2::real.\<forall>a\<in>G. otimess (r1+r2) a =
 opluss (otimess r1 a) (otimess r2 a)"
  proof
    fix r2
    show "\<forall>a\<in>G. otimess (r1+r2) a =
 opluss (otimess r1 a) (otimess r2 a)"
    proof
      fix a 
      assume "a\<in>G"
      show " otimess (r1+r2) a =
 opluss (otimess r1 a) (otimess r2 a)"
      proof-
        have "otimess (r1+r2) a = phi ((r1+r2) * (inv phi a))"
          using otimess_def
          by (metis otimess_def \<open>a \<in> G\<close>)
        moreover have "otimess r1 a \<in> G"
       
          by (metis \<open>a \<in> G\<close> scale_closed_check)
       moreover have "otimess r2 a \<in> G"
       
          by (metis \<open>a \<in> G\<close> scale_closed_check)
        moreover have "opluss (otimess r1 a) (otimess r2 a) = 
      phi (( r1 * ((inv phi) a)) +
 ( r2 * ((inv phi) a)))"
          using opluss_def otimess_def
         
          by (smt (verit, best) \<open>a \<in> G\<close> bij_betw_def calculation(2,3) inv_f_eq
              phi_is_bij)
        ultimately show ?thesis
          by argo
      qed
  qed
qed
qed

lemma  scale_assoc_check:
  shows "\<forall>r1::real. \<forall>r2::real. \<forall>a\<in>G. otimess (r1*r2) a = otimess r1 (otimess r2 a)"
  by (metis bij_betw_def inv_f_eq mult.assoc otimess_def phi_is_bij
      range_eqI)

definition fii::"real\<Rightarrow>real" where
  "fii a = (if a\<in>G then a else undefined)"

lemma inv_phi_G:
  assumes aG: "a \<in> G"
  shows "inv phi a = (if 0 \<le> a then ln a else - ln (-a))"
proof -
  let ?psi = "\<lambda>y::real. if 0 \<le> y then ln y else - ln (-y)"

  have left_inv: "?psi (phi x) = x" for x
    by (cases "0 \<le> x") (simp_all add: phi_def)

  have right_inv: "phi (inv phi a) = a"
    by (rule bij_betw_inv_into_right[OF phi_is_bij aG])

  show ?thesis
    using left_inv[of "inv phi a"]
    using right_inv by force
qed

lemma f_1:
  assumes "a\<in>G"
  shows "a\<ge>1 \<longrightarrow> fii (otimess (abs(r)) a) = a powr (abs(r))"
proof
  assume "a\<ge>1"
  show "fii (otimess (abs(r)) a) = a powr (abs(r))"
  proof-
    have  "fii (otimess (abs(r)) a) = otimess (abs(r)) a"
    by (metis scale_closed_check otimess_def fii_def)
  moreover have "inv phi a \<ge> 0"
    by (metis UNIV_I \<open>1 \<le> a\<close> bij_betw_def inv_into_f_f lemma_exp_total phi_def
        phi_is_bij)
  moreover have "otimess (abs(r)) a = exp((abs(r)) * (inv phi a))"
    by (simp add: assms calculation(2) otimess_def phi_def)
  ultimately show ?thesis 
    by (metis assms comm_monoid_mult_class.mult_1 exp_powr_real mult.commute
        otimess_def phi_def scale_1_check)
qed
qed


lemma f_2:
  assumes "a\<in>G" "r\<noteq>0"
  shows "a<1 \<longrightarrow> fii (otimess (abs(r)) a) = - (a powr (abs(r)))"
proof
  assume "a<1"
  show "fii (otimess (abs(r)) a) = -(a powr (abs(r)))"
  proof-
    have  "fii (otimess (abs(r)) a) = otimess (abs(r)) a"
    by (metis scale_closed_check otimess_def fii_def)
  moreover have "inv phi a < 0"
    by (metis \<open>a < 1\<close> assms(1) bij_betw_inv_into_right exp_gt_one lemma_exp_total
        linorder_not_less not_less_iff_gr_or_eq phi_def phi_is_bij)
  moreover have "otimess (abs(r)) a = -exp(-((abs(r)) * (inv phi a)))"
    using assms calculation(2) otimess_def phi_def
   
    by (metis abs_le_zero_iff less_le_not_le zero_le_mult_iff)
  ultimately show ?thesis 
    
    by (smt (verit) assms(1) bij_betw_def exp_powr_real f_inv_into_f mult.commute
        mult_minus_left phi_def phi_is_bij uminus_powr_eq)
qed
qed
lemma f:
  assumes "a\<in>G"
  shows "norm (fii (otimess r a)) = (abs(a)) powr abs(r)"
proof-
  have "fii (otimess r a) = otimess r a"
    by (metis scale_closed_check otimess_def fii_def)
  moreover have "norm (otimess r a) = abs(otimess r a)"
    by auto
  moreover have "abs(otimess r a) = abs(phi (r * (inv phi a)))"
    by (metis assms otimess_def)
  moreover have "r * (inv phi a) \<ge> 0 \<or> r * (inv phi a)<0"
    by fastforce
  moreover {
    assume "r * (inv phi a) \<ge> 0"
    then have "phi (r * (inv phi a)) = exp (r * (inv phi a))"
      by (metis \<open>0 \<le> r * inv phi a\<close> phi_def)
    moreover obtain "x" where "a = phi x"
      by (metis assms comp_apply ggc.gyro_inv_idem)
    moreover have "x >0 \<or> x=0 \<or> x<0"
      
      by auto
    moreover {
      assume "x=0"
      then have ?thesis 
        by (metis \<open>\<bar>otimess r a\<bar> = \<bar>phi (r * inv phi a)\<bar>\<close>
            \<open>fii (otimess r a) = otimess r a\<close> \<open>norm (otimess r a) = \<bar>otimess r a\<bar>\<close> abs_1
            bij_betw_def calculation(2) dual_order.refl exp_zero inv_f_f mult_zero_right
            phi_def phi_is_bij powr_one_eq_one)
    }
    moreover {
      assume "x>0"
      then have "a = exp x"
       
        by (metis \<open>0 < x\<close> calculation(2) phi_def not_exp_less_zero exp_raw_ln linorder_not_le)
       
      moreover have "x = ln a"
     
        
        using calculation by simp
      moreover have "exp (r * ln a) = a powr r"
       
        by (metis calculation(1) ln_exp exp_powr_real powr_def)
      moreover have "x = inv phi a"
        
        by (metis \<open>a = phi x\<close> bij_betw_def comp_apply id_apply inj_iff
            phi_is_bij)
      
      moreover have "r \<ge>0"
        using `r * (inv phi a) \<ge> 0` `x>0` `x = inv phi a`
      
        using linorder_not_less zero_le_mult_iff by auto
      ultimately have ?thesis
        
        using \<open>\<bar>otimess r a\<bar> = \<bar>phi (r * inv phi a)\<bar>\<close> \<open>fii (otimess r a) = otimess r a\<close>
          \<open>phi (r * inv phi a) = exp (r * inv phi a)\<close> by fastforce
    }
moreover {
      assume "x<0"
      then have "a = -exp (-x)"
       
       
        by (metis \<open>x < 0\<close> calculation(2) phi_def linorder_not_le)
      moreover have "x = -ln (-a)"
     
        
        using calculation by simp
      moreover have "exp (r * (-ln (-a))) = (-a) powr (-r)"
      
        by (simp add: calculation(1) powr_def)
       
      moreover have "x = inv phi a"
        
        by (metis \<open>a = phi x\<close> bij_betw_def comp_apply id_apply inj_iff
            phi_is_bij)
      
      moreover have "r \<le>0"
        using `r * (inv phi a) \<ge> 0` `x<0` `x = inv phi a`
      
        using linorder_not_less zero_le_mult_iff 
      
        by auto
      ultimately have ?thesis
        
        using \<open>\<bar>otimess r a\<bar> = \<bar>phi (r * inv phi a)\<bar>\<close> \<open>fii (otimess r a) = otimess r a\<close>
          \<open>phi (r * inv phi a) = exp (r * inv phi a)\<close> by fastforce
    }
    ultimately have ?thesis
      by satx
  }
  moreover {
    assume "r * (inv phi a) < 0"
    then have "phi (r * (inv phi a)) = -exp (-( r * (inv phi a)))"
      using phi_def
      
      by (metis \<open>r * inv phi a < 0\<close> phi_def linorder_not_le)
    moreover obtain "x" where "a = phi x"
      by (metis assms comp_apply ggc.gyro_inv_idem)
    moreover have "x >0 \<or> x=0 \<or> x<0"
      
      by auto
    moreover {
      assume "x=0"
      then have ?thesis 
        by (metis \<open>\<bar>otimess r a\<bar> = \<bar>phi (r * inv phi a)\<bar>\<close>
            \<open>fii (otimess r a) = otimess r a\<close> \<open>norm (otimess r a) = \<bar>otimess r a\<bar>\<close> abs_1
            bij_betw_def calculation(2) dual_order.refl exp_zero inv_f_f mult_zero_right
            phi_def phi_is_bij powr_one_eq_one)
    }
    moreover {
      assume "x>0"
      then have "a = exp x"
       
        by (metis \<open>0 < x\<close> calculation(2) phi_def not_exp_less_zero exp_raw_ln linorder_not_le)
       
      moreover have "x = ln a"
     
        
        using calculation by simp
      moreover have "-exp (-(r * ln a)) = - (a powr (-r))"
       
        by (metis calculation(1) exp_powr_real ln_powr ln_exp mult_minus_left)
      moreover have "x = inv phi a"
        
        by (metis \<open>a = phi x\<close> bij_betw_def comp_apply id_apply inj_iff
            phi_is_bij)
      
      moreover have "r <0"
        using `r * (inv phi a) < 0` `x>0` `x = inv phi a`
      
        
        by (simp add: mult_less_0_iff)
      ultimately have ?thesis
        
       
        using \<open>\<bar>otimess r a\<bar> = \<bar>phi (r * inv phi a)\<bar>\<close> \<open>fii (otimess r a) = otimess r a\<close>
          \<open>phi (r * inv phi a) = - exp (- (r * inv phi a))\<close> abs_real_def
        by fastforce
    }
moreover {
      assume "x<0"
      then have "a = -exp (-x)"
       
       
        by (metis \<open>x < 0\<close> calculation(2) phi_def linorder_not_le)
      moreover have "x = -ln (-a)"
     
        
        using calculation by simp
      moreover have "-exp (-(r * (-ln (-a)))) = - ((-a) powr r)"
      
        by (simp add: calculation(1) powr_def)
       
      moreover have "x = inv phi a"
        
        by (metis \<open>a = phi x\<close> bij_betw_def comp_apply id_apply inj_iff
            phi_is_bij)
      
      moreover have "r \<ge>0"
        using `r * (inv phi a) < 0` `x<0` `x = inv phi a`
      
        using linorder_not_less zero_le_mult_iff 
      
       
        by (simp add: mult_le_0_iff order_less_le)
      ultimately have ?thesis
        
       
        using \<open>\<bar>otimess r a\<bar> = \<bar>phi (r * inv phi a)\<bar>\<close> \<open>fii (otimess r a) = otimess r a\<close>
          \<open>phi (r * inv phi a) = - exp (- (r * inv phi a))\<close> by force
    }
    ultimately have ?thesis 
      by satx
  }

 
  ultimately show ?thesis

    by satx
qed
definition phi_norms_pos :: "real set" where
  "phi_norms_pos = norm ` G"
definition phi_norms_neg::"real set" where 
  "phi_norms_neg = (\<lambda>x. -1 * norm x) ` G"
lemma phi_norms_pos_is:
  shows "phi_norms_pos = {x::real. x\<ge>1}"
proof
  show " phi_norms_pos \<subseteq> {x. 1 \<le> x}"
  proof
    fix x
    assume "x\<in>phi_norms_pos"
    show "x\<in> {x. 1 \<le> x}"
    proof-
      obtain "y" where "y\<in>G \<and> x = norm y"
   
        by (metis \<open>x \<in> phi_norms_pos\<close> imageE phi_norms_pos_def)
      have "y<(-1) \<or> y\<ge>1"
        
        using G_def \<open>y \<in> G \<and> x = norm y\<close> by auto
      moreover {
        assume "y<(-1)"
        then have "norm y = abs y"

          by force
        then have " abs y > 1"

   using \<open>norm y = \<bar>y\<bar>\<close> \<open>y < - 1\<close> real_norm_def abs_1 add_0 \<open>y \<in> G \<and> x = norm y\<close> add.right_neutral calculation by simp
        then have "norm y > 1"
         
          by fastforce                 
        then have ?thesis 
         
          using \<open>y \<in> G \<and> x = norm y\<close> less_eq_real_def by blast
      }
 moreover {
        assume "y\<ge>1"        then have "norm y = abs y"

          by force
        then have " abs y \<ge> 1"

   using \<open>norm y = \<bar>y\<bar>\<close> \<open>y \<ge>  1\<close> real_norm_def abs_1 add_0 \<open>y \<in> G \<and> x = norm y\<close> add.right_neutral calculation by simp
        then have "norm y \<ge> 1"
         
          by fastforce                
        then have ?thesis 
         
          using \<open>y \<in> G \<and> x = norm y\<close> less_eq_real_def by blast
      }ultimately show ?thesis
        by linarith
    qed
  qed

next
  show "{x::real. 1 \<le> x} \<subseteq> phi_norms_pos"
  proof
    show " \<And>x. x \<in> {x. 1 \<le> x} \<Longrightarrow> x \<in> phi_norms_pos"
    proof-
    fix x
    show " x \<in> {x. 1 \<le> x} \<Longrightarrow> x \<in> phi_norms_pos"
    proof-
      assume "x\<in>{x::real. 1\<le> x}"
      show "x\<in> phi_norms_pos"
      proof-
        obtain "y" where "y\<in> {x::real. x < - 1 \<or> 1 \<le> x} \<and> abs y = x"
        unfolding phi_norms_pos_def G_def
        using \<open>x \<in> {x. 1 \<le> x}\<close> by fastforce
      moreover have "norm y = abs y"
        
        by auto
      moreover have "norm y = x"
      
        by (metis calculation(2) calculation(1))
      ultimately show ?thesis 
        using \<open>norm y = x\<close> \<open>y \<in> {x. x < - 1 \<or> 1 \<le> x} \<and> \<bar>y\<bar> = x\<close> \<open>norm y = \<bar>y\<bar>\<close> phi_norms_pos_def G_def by auto
    qed
  qed
qed
qed
qed

lemma phi_norms_neg_is:
  shows "phi_norms_neg = {x::real. x\<le>(-1)}"
proof
  show "phi_norms_neg \<subseteq> {x. x \<le> - 1}"
  proof
    show "\<And>x. x \<in> phi_norms_neg \<Longrightarrow> x \<in> {x. x \<le> - 1}"
    proof-
      fix x
      show " x \<in> phi_norms_neg \<Longrightarrow> x \<in> {x. x \<le> - 1}"
      proof-
        assume "x\<in>phi_norms_neg"
        show "x\<in>{x::real. x \<le> - 1}"
          
        proof-
          obtain "y" where "y\<in> G \<and> x = (-1::real) * norm(y::real)"
 using phi_norms_neg_def
           
            using \<open>x \<in> phi_norms_neg\<close> by auto
          moreover have "abs y \<ge> 1"
            using G_def
            
            using calculation phi_norms_pos_def phi_norms_pos_is
            by auto
          moreover have "norm y \<ge> 1"
            
            by (metis calculation(2) real_norm_def)
          ultimately show ?thesis
            using phi_norms_neg_def
           
            by auto

        qed
      qed
    qed
  qed
next
  show " {x. x \<le> - 1} \<subseteq> phi_norms_neg"
  proof
    show "\<And>x. x \<in> {x. x \<le> - 1} \<Longrightarrow> x \<in> phi_norms_neg"
    proof-
      fix x
      show " x \<in> {x. x \<le> - 1} \<Longrightarrow> x \<in> phi_norms_neg"
      proof-
        assume "x \<in> {x. x \<le> - 1}"
        show "x \<in> phi_norms_neg"
        proof-
          obtain "y" where "y \<in> G \<and> x = - abs(y)"
            
            by (smt (verit, best) G_def \<open>x \<in> {x. x \<le> - 1}\<close>
                mem_Collect_eq)
          
          moreover have "x=-norm(y)"
           
            by (metis calculation real_norm_def)
          ultimately show ?thesis
            using \<open>x = - norm y\<close> \<open>y \<in> G \<and> x = - \<bar>y\<bar>\<close> phi_norms_neg_def by auto
        qed
    
        qed
      qed
    qed
  qed

definition normss::"real set" where
  "normss =  phi_norms_neg \<union> phi_norms_pos"
definition S::"real \<Rightarrow> real" where 
  "S = (SOME s. bij_betw s {x::real. x<0} {x::real. x\<le>(-1)})"


lemma exists_S:
  shows "\<exists>s. bij_betw s {x::real. x<0} {x::real. x\<le>(-1)}"
  using exists_bij_interval by simp
(*proof-
  let ?s = "\<lambda>x. (x-1)"
  have "bij_betw ?s {x::real. x<0} {x::real. x<(-1)}"
  proof-
    have "inj_on ?s {x::real. x<0}"
      by simp
    moreover have "?s ` {x::real. x<0} = {x::real. x<(-1)}"
    proof
      show " (\<lambda>x. x - 1) ` {x::real. x < 0} \<subseteq> {x::real. x < (- 1)}"
        by auto
    next
      show "{x::real. x < - 1} \<subseteq> (\<lambda>x. x - 1) ` {x. x < 0}"
      proof
  fix y :: real
  assume hy: "y \<in> {x. x < -1}"
  show "y \<in>  (\<lambda>x. x - 1) ` {x. x < 0}"
  proof-
    have ylt: "y < -1"
      
      using hy by auto

  have "y = (\<lambda>x. x - 1) (y + 1)"
    by simp
  moreover have "y + 1 \<in> {x. x < 0}"
    using ylt by simp
  moreover have "y \<in> (\<lambda>x. x - 1) ` {x. x < 0}"
    
    using calculation(2) by force
  ultimately show ?thesis 
    by presburger
    qed
  qed
qed
  then show ?thesis 
    
    by (simp add: bij_betw_def)
qed
  then show ?thesis 
    by fast
qed
*)


lemma S_bij:
  shows "bij_betw S {x::real. x < 0} {x::real. x \<le> -1}"
  unfolding S_def
  using exists_S
  by (rule someI_ex)

lemma S_neg:
  shows "\<forall>x::real. x<0 \<longrightarrow>  S x \<le> -1"
  unfolding S_def S_bij
  using S_bij S_def bij_betw_apply by fastforce

definition T::"real \<Rightarrow> real " where 
  "T x = (if x\<ge>0 then exp x else S x) "


lemma T_1:
  shows "T ` {x::real. x\<ge>0} = phi_norms_pos"
proof
  show "T ` {x. 0 \<le> x} \<subseteq> phi_norms_pos"
    unfolding phi_norms_pos_def G_def
  proof
    fix x
    assume " x \<in> T ` {x. 0 \<le> x}"
    show " x \<in> norm ` {x::real. x < - 1 \<or> 1 \<le> x}"
    proof-
      obtain "y" where "y\<ge>0 \<and> x = exp y"
        using T_def \<open>x \<in> T ` {x. 0 \<le> x}\<close> image_iff by auto
      moreover have " x\<ge> 1"
      
        by (simp add: calculation)
      moreover obtain "z" where "( (z::real) < - 1 \<or> 1 \<le> z ) \<and> x = norm z"
       
        using calculation(2) by fastforce
      ultimately show ?thesis
 
        by blast
    qed
  qed
next
  show "phi_norms_pos \<subseteq> T ` {x. 0 \<le> x}"
    unfolding phi_norms_pos_def T_def G_def
  proof
    fix x 
    assume *: " x \<in> norm ` {x::real. x < (- 1 )\<or> 1 \<le> x}"
    show "x \<in> (\<lambda>x. if 0 \<le> x then exp x else S x) ` {x. 0 \<le> x} "
    proof-
      obtain "y" where "y \<in>  {x::real. x < (- 1 )\<or> 1 \<le> x} \<and> x = norm y"
       
        using "*" by blast
      moreover have "y< (-1) \<or> 1\<le>y"
        using ` y \<in>  {x::real. x < (- 1 )\<or> 1 \<le> x} \<and> x = norm y`
      
        by simp
      moreover have "x=abs y"
        
        by (simp add: calculation(1))
      moreover have "x\<ge>1"
        
        using calculation(2,3) by linarith
      moreover obtain "z" where "x = exp z"
     
        using calculation(4) lemma_exp_total by auto
      ultimately show ?thesis 
       
        by (metis (full_types, lifting) image_iff mem_Collect_eq one_le_exp_iff) 
    qed
  qed
qed

lemma T_2:
  shows "T ` {x::real. x<0} = phi_norms_neg"
proof
  show "T ` {x.  x<0} \<subseteq> phi_norms_neg"
    unfolding phi_norms_neg_def G_def
  proof
    fix x
    assume " x \<in> T ` {x. x <0}"
    show " x \<in> (\<lambda>x. - 1 * norm x) ` {x::real. x < - 1 \<or> 1 \<le> x}"
    proof-
      obtain "y" where "y<0 \<and> x = S y"
        using T_def \<open>x \<in> T ` {x. x<0}\<close> image_iff by auto
      moreover have " x\<le> (-1)"
      
        by (simp add: S_neg calculation)
      moreover have "- x \<ge> 1"
          by (metis calculation(2) neg_le_iff_le add.inverse_inverse)
      moreover obtain "z" where "( (z::real) < - 1 \<or> 1 \<le> z ) \<and> x = - abs z"
        using calculation(2)
        by (smt (verit, ccfv_SIG))
      moreover have "x = -norm z"
        
        by (simp add: calculation(4))
      ultimately show ?thesis
 
        
        by force
    qed
  qed
next
  show "phi_norms_neg \<subseteq> T ` {x. x < 0}"
    unfolding phi_norms_neg_def T_def G_def
  proof
    fix x 
    assume *: " x \<in> (\<lambda>x. - 1 * norm x) ` {x::real. x < (- 1 )\<or> 1 \<le> x}"
    show "x \<in> (\<lambda>x. if 0 \<le> x then exp x else S x) ` {x. x<0} "
    proof-
      obtain "y" where "y \<in>  {x::real. x < (- 1 )\<or> 1 \<le> x} \<and> x = - norm y"
       
        using "*" 
        by auto
      moreover have "y< (-1) \<or> 1\<le>y"
        using ` y \<in>  {x::real. x < (- 1 )\<or> 1 \<le> x} \<and> x = -norm y`
      
        by simp
      moreover have "x=-abs y"
        
        by (simp add: calculation(1))
      moreover have "x\<le>(-1)"
        
        using calculation(2,3) by linarith
      moreover obtain "z" where "z\<in>  {x::real. x<0} \<and> x = S z"
        using S_bij
        
        by (metis (no_types, lifting) "*" G_def bij_betw_iff_bijections
            phi_norms_neg_def phi_norms_neg_is)
      ultimately show ?thesis 
      
        by fastforce
    qed
  qed
qed

lemma T_bij:
  shows "bij_betw T UNIV normss"
proof-
  have "\<forall>x\<in>UNIV.
       \<forall>y\<in>UNIV.
          (if 0 \<le> x then exp x else S x) = (if 0 \<le> y then exp y else S y) \<longrightarrow>
          x = y"
  proof
    fix x::real
    assume "x\<in>UNIV"
    show "\<forall>y\<in>UNIV.
          (if 0 \<le> x then exp x else S x) = (if 0 \<le> y then exp y else S y) \<longrightarrow>
          x = y"
    proof
      fix y::real
      assume "y\<in>UNIV"
      show "  (if 0 \<le> x then exp x else S x) = (if 0 \<le> y then exp y else S y) \<longrightarrow>
          x = y"
      proof
        assume " (if 0 \<le> x then exp x else S x) = (if 0 \<le> y then exp y else S y)"
        show "x=y"
        proof-
          have "x\<ge>0 \<or> x < 0"
            
            by auto
          moreover {
            assume "x\<ge>0"
            then have "(if 0 \<le> x then exp x else S x) = exp x"
            
              by presburger
            then have " (if 0 \<le> y then exp y else S y) = exp x"
              
              using \<open>(if 0 \<le> x then exp x else S x) = exp x\<close> \<open>(if 0 \<le> x then exp x else S x) = (if 0 \<le> y then exp y else S y)\<close> by simp

            then have "y \<ge> 0 \<or> y <0"
              
              
              by linarith
            moreover {
              assume "y \<ge>0"
              then have "exp y = exp x"
                
                by (metis \<open>0 \<le> y\<close> \<open>(if 0 \<le> y then exp y else S y) = exp x\<close>)
              then have ?thesis 
                by simp
            }
            moreover {
              assume "y<0"
              then  have "S y = exp x"
                
                using \<open>(if 0 \<le> y then exp y else S y) = exp x\<close> by auto
              then have "exp x \<ge>0"
               
                by auto
              then have "S y \<ge>0"
                
                by (metis \<open>0 \<le> exp x\<close> \<open>S y = exp x\<close>)
              
              then have ?thesis 
                using S_neg \<open>y < 0\<close> by auto
            }
            then have ?thesis 
              by (metis \<open>y < 0 \<Longrightarrow> x = y\<close> calculation(2) calculation(1))
          }
          moreover {
             assume "x<0"
            then have "(if 0 \<le> x then exp x else S x) = S x"
            
             
              by simp
            then have " (if 0 \<le> y then exp y else S y) = S x"
              
              
              by (metis \<open>(if 0 \<le> x then exp x else S x) = S x\<close> \<open>(if 0 \<le> x then exp x else S x) = (if 0 \<le> y then exp y else S y)\<close>)
            then have "y \<ge> 0 \<or> y <0"
              
              
              by linarith
            moreover {
              assume "y \<ge>0"
              then have "exp y = S x"
              
                by (metis \<open>0 \<le> y\<close> \<open>(if 0 \<le> y then exp y else S y) = S x\<close>)
              then have ?thesis 
             
                by (metis S_neg \<open>x < 0\<close> add.inverse_inverse cosh_arcosh_real cosh_real_pos
                    exp_gt_zero neg_le_iff_le neg_less_0_iff_less order.asym)
             
            }
            moreover {
              assume "y<0"
              then  have "S y = S x"
                
              
                by (metis  calculation(2) \<open>(if 0 \<le> y then exp y else S y) = S x\<close>)
              
              then have ?thesis 
                using S_bij bij_betw_def[of S "{x. x < 0}" "{x. x \<le> - 1}"] 
inj_on_def[of S "{x. x < 0}"] 
                
                using \<open>x < 0\<close> \<open>y < 0\<close> by blast
            }
            then have ?thesis 
              by (metis \<open>y < 0 \<Longrightarrow> x = y\<close> calculation(2) calculation(1))
          }
          ultimately show ?thesis
            by linarith
        qed
      qed
    qed
  qed
  moreover have "inj_on T UNIV"
    unfolding inj_on_def T_def
    using calculation by fastforce
  moreover have "T`UNIV = normss"
  proof-
    have "T`{x::real. x\<ge>0} =  phi_norms_pos"
   
      by (metis T_1)
    moreover have "T`{x::real. x<0} =  phi_norms_neg"
      
      by (metis T_2)
    moreover have "T`{x::real. x\<ge>0} \<union> T`{x::real. x<0} = T`UNIV"
     
      by fastforce
    moreover have "phi_norms_pos \<union> phi_norms_neg = normss"
      
      using normss_def by auto
    ultimately show ?thesis 
      by presburger
  qed
    ultimately show ?thesis
      using bij_betw_def by blast
qed


lemma x_pos_T_m_exp:
  assumes "x\<ge>0"
  shows "\<forall>m. x = T m \<longrightarrow> m\<ge>0"
proof
  fix m
  show "x = T m \<longrightarrow> m\<ge>0"
  proof
    assume "x=T m"
    show "m\<ge>0"
    proof-
         have "m\<ge>0"
        proof(rule ccontr)
          assume "\<not>(m\<ge>0)"
          have "m<0"
            using \<open>\<not> 0 \<le> m\<close> by linarith
          then have "T m = S m"
            
            using \<open>m < 0\<close> T_def by auto
          then have "bij_betw S {x::real. x<0} {x::real. x\<le>(-1)}"
            
            using S_bij by auto
           
            
          then have "S m \<le> (-1)"
            using S_def
          
            by (metis \<open>m < 0\<close> S_neg)
           
          then show False 
            
            using \<open>T m = S m\<close> \<open>x = T m\<close> assms by linarith
         
        qed
        then show ?thesis
          by presburger
      qed
    qed
  qed


lemma x_neg_T_m_exp:
  assumes "x<0"
  shows "\<forall>m. x = T m \<longrightarrow> m<0"
proof
  fix m
  show "x = T m \<longrightarrow> m<0"
  proof
    assume "x=T m"
    show "m<0"
    proof-
         have "m<0"
        proof(rule ccontr)
          assume "\<not>(m<0)"
          have "m\<ge>0"
            
            using \<open>\<not> m < 0\<close> by auto
          then have "T m = exp m"
           
            by (metis \<open>0 \<le> m\<close> T_def)
          then show False 
            
      
            using \<open>T m = exp m\<close> \<open>x = T m\<close> assms by simp
        qed
        then show ?thesis
          by presburger
      qed
    qed
  qed

     
definition opluss'::"real\<Rightarrow>real\<Rightarrow>real" where
  "opluss' a b = (if (a\<in>normss \<and> b \<in>normss) then T ((inv T a) + (inv T b))
else undefined)"
definition otimess'::"real\<Rightarrow>real\<Rightarrow>real" where
  "otimess' r a = (if (a\<in>normss) then T (r*(inv T a))
else undefined)"

lemma T_inv_1:
  shows "(inv T 1) = 0"
        proof-
          obtain "m" where "1=T m"
            
            by (metis T_def dual_order.refl exp_zero)
          moreover have "m\<ge>0"
           
            using calculation x_pos_T_m_exp 
            
            by (metis  x_pos_T_m_exp calculation le_numeral_extra(1))
          
          moreover have "1 = exp m"
           
            by (simp add: T_def calculation(1,2))
          moreover have "m = ln 1"
          
            by (simp add: calculation(3))
          moreover have "m=0"
           
            by (simp add: calculation(4))
          moreover have "1\<in>UNIV"
            
            by simp
          moreover have "m = (inv T 1)"
            using T_bij `1 \<in> UNIV `
            
            by (simp add: bij_betw_inv_into_left calculation(1))
          ultimately show ?thesis
            by presburger
        qed
interpretation ggv7: one_dim_vector_space_with_domain normss opluss' 1 otimess'
proof
  show "\<And>x y. x \<in> normss \<Longrightarrow> y \<in> normss \<Longrightarrow> opluss' x y \<in> normss"
    using T_bij bij_betw_apply opluss'_def by fastforce
next
  show "1 \<in> normss"
    by (metis UnCI grc.zero_in_dom image_eqI norm_one normss_def
        phi_norms_pos_def)
next
  show " \<And>x y z.
       x \<in> normss \<Longrightarrow>
       y \<in> normss \<Longrightarrow>
       z \<in> normss \<Longrightarrow> opluss' (opluss' x y) z = opluss' x (opluss' y z)"
    by (smt (verit, del_insts) T_bij bij_betw_imp_inj_on bij_betw_imp_surj_on
        inv_f_f opluss'_def range_eqI)
next
  show "\<And>x y. x \<in> normss \<Longrightarrow> y \<in> normss \<Longrightarrow> opluss' x y = opluss' y x"
    by (simp add: add.commute opluss'_def)
next
  show "\<And>x. x \<in> normss \<Longrightarrow> opluss' x 1 = x"
  proof-
    fix x
    assume "x\<in>normss"
    show "opluss' x 1 = x"
    proof-
      have "1 \<in> normss"
    by (metis UnCI grc.zero_in_dom image_eqI norm_one normss_def
        phi_norms_pos_def)
      moreover have "opluss' x 1 = T ((inv T x) + (inv T 1))"
        using opluss'_def
      
        by (metis opluss'_def calculation \<open>x \<in> normss\<close>)
      moreover have "(0::real)\<ge>0"
      
        by simp
      moreover have "T (0::real) =1"
        
        by (simp add: T_def)
      moreover have "0\<in>UNIV"
       
        by simp
      moreover have "(inv T (T (0::real))) =inv T 1"
      
        by (metis calculation(4))
      moreover have "inv T (1::real) = (0::real)"
        using T_def  `T (0::real) =1`   `0\<in>UNIV` `1\<in>normss`
        T_bij
       
        by (metis bij_betw_inv_into_left)
      ultimately show ?thesis
        using T_bij
       
        by (simp add: \<open>x \<in> normss\<close> bij_betw_inv_into_right)
    qed
  qed
next
  show "\<And>x. x \<in> normss \<Longrightarrow> \<exists>y\<in>normss. opluss' x y = 1"
  proof-
    fix x
    assume "x\<in>normss"
    show "\<exists>y\<in>normss. opluss' x y = 1"
    proof-
      have "x>0 \<or> x=0 \<or> x <0"
       
        by linarith
      moreover{
        assume "x>0"
        obtain "m" where "x = T m"
          
          by (metis T_bij \<open>x \<in> normss\<close> bij_betw_iff_bijections)
        moreover have "m\<ge>0"
         
          using \<open>0 < x\<close> calculation x_pos_T_m_exp
          
          using order_less_imp_le by blast
       
          
        moreover have "x = exp m"
          
          by (simp add: T_def calculation(1,2))
        moreover have "m = ln x"
         
          by (metis calculation(3) ln_exp)
         
        moreover have "-(inv T x)  = ln(1/x)"
          
          by (metis T_bij bij_betw_inv_into_left calculation(1,3)
              exp_minus' iso_tuple_UNIV_I ln_exp)
        moreover have "inv T x  = m"
          
          by (metis calculation(3,5) exp_minus' ln_exp
              verit_minus_simplify(4))
        moreover obtain "y" where  " y = T (ln (1/x))"
          
          by presburger
        moreover have "(inv T 1) = 0"
        
          by (metis T_inv_1)
       
        moreover have "(inv T x) + (inv T y ) = (inv T 1)"
        proof-
          have "inv T 1 = 0"
          
            by (metis calculation(8))
          moreover have "inv T x + inv T y = ln x + ln (1/x)"
            using T_bij
            
            by (simp add: \<open>inv T x = m\<close> \<open>m = ln x\<close> \<open>y = T (ln (1 / x))\<close>
                bij_betw_inv_into_left)
          ultimately show ?thesis 
            using \<open>- inv T x = ln (1 / x)\<close> \<open>inv T x = m\<close> \<open>m = ln x\<close>
            by auto
        qed
        ultimately have "?thesis"
          using T_bij
          unfolding opluss'_def
          
          by (metis T_def UNIV_I bij_betw_iff_bijections exp_zero
              order_refl)
      }
      moreover{
        assume "x<0"
        obtain "m" where "x = T m"
          
          by (metis T_bij \<open>x \<in> normss\<close> bij_betw_iff_bijections)
        moreover have "m<0"
        
          by (metis \<open>x < 0\<close> calculation x_neg_T_m_exp)
        moreover have "x = S m"
        
          using T_def calculation(1,2) by force
        moreover have "m = inv_into {x. x<0} S x"
          using S_bij
       
          by (simp add: bij_betw_inv_into_left calculation(2,3))
        moreover obtain "y" where "y = T (-1 * inv_into {x. x<0} S x)"
       
          by presburger
        moreover have "((inv T x) + (inv T y)) =(inv T 1)"
           proof-
          have "inv T 1 = 0"
            
            by (metis T_inv_1)
          moreover have "inv T x + inv T y = (inv_into {x. x<0} S x) - (inv_into {x. x<0} S x)"
            using T_bij S_bij
          
            by (metis UNIV_I \<open>m = inv_into {x. x < 0} S x\<close> \<open>x = T m\<close>
                \<open>y = T (- 1 * inv_into {x. x < 0} S x)\<close> add.right_inverse
                bij_betw_inv_into_left
                cancel_comm_monoid_add_class.diff_cancel mult.commute
                mult_minus1_right)
          
          ultimately show ?thesis 
           
            by simp
        qed
        moreover have "1\<in>normss"
        proof-
          have "1\<in>G"
            using G_def by auto
          moreover have "1\<in>normss"
            unfolding normss_def
            phi_norms_neg_def phi_norms_pos_def
            
            using phi_norms_pos_def phi_norms_pos_is by auto
          ultimately show ?thesis 
            by presburger
        qed
        moreover have "T(inv T 1) = 1"
          
          by (meson T_bij bij_betw_inv_into_right calculation(7))
        ultimately have ?thesis using T_bij S_bij
          unfolding opluss'_def
          
          by (metis UNIV_I bij_betw_iff_bijections)
      }
      moreover {
        assume "x=0"
        then obtain "y"  where "y = T (-(inv T 0))"
        
          by presburger
          moreover have "((inv T x) + (inv T y)) =(inv T 1)"
           proof-
          have "inv T 1 = 0"
            
            by (metis T_inv_1)
          moreover have "inv T x + inv T y = 0"
            using T_bij S_bij
            
            by (simp add: \<open>x = 0\<close> \<open>y = T (- inv T 0)\<close>
                bij_betw_inv_into_left)
            
          
          ultimately show ?thesis 
           
            by simp
        qed
 moreover have "1\<in>normss"
        proof-
          have "1\<in>G"
            using G_def by auto
          moreover have "1\<in>normss"
            unfolding normss_def
            phi_norms_neg_def phi_norms_pos_def
            
            using phi_norms_pos_def phi_norms_pos_is by auto
          ultimately show ?thesis 
            by presburger
        qed
        moreover have "T(inv T 1) = 1"
          using T_bij
      
          by (metis T_bij calculation(3) bij_betw_inv_into_right)
        ultimately have ?thesis
          using T_bij S_bij unfolding opluss'_def 
         
          by (metis UNIV_I \<open>x \<in> normss\<close> bij_betw_iff_bijections)
      }
      ultimately show ?thesis 
        by satx 
    qed
  qed
next
  show "\<And>x a. x \<in> normss \<Longrightarrow> otimess' a x \<in> normss"
  
    using T_bij bij_betw_apply otimess'_def by fastforce
next
  show "\<And>x a b.
       x \<in> normss \<Longrightarrow>
       otimess' (a + b) x = opluss' (otimess' a x) (otimess' b x)"
    using T_bij unfolding otimess'_def opluss'_def
    by (simp add: bij_betwE bij_betw_inv_into_left
        ring_class.ring_distribs(2))
next
  show " \<And>x a b.
       x \<in> normss \<Longrightarrow>
       otimess' a (otimess' b x) = otimess' (a * b) x"
    by (smt (verit, ccfv_threshold) T_bij UNIV_I
        ab_semigroup_mult_class.mult_ac(1) bij_betw_iff_bijections
        bij_betw_inv_into_left otimess'_def)
next
  show " \<And>x. x \<in> normss \<Longrightarrow> otimess' 1 x = x"
    using T_bij unfolding otimess'_def
    by (simp add: bij_betw_inv_into_right)
next
  show "\<And>x y a.
       x \<in> normss \<Longrightarrow>
       y \<in> normss \<Longrightarrow>
       otimess' a (opluss' x y) =
       opluss' (otimess' a x) (otimess' a y)"
    using T_bij unfolding opluss'_def otimess'_def
    
    by (simp add: bij_betwE bij_betw_inv_into_left
        ring_class.ring_distribs(1))
next
  show "\<forall>y x. y \<in> normss \<and> x \<in> normss \<and> x \<noteq> 1 \<longrightarrow>
          (\<exists>!r. y = otimess' r x)"
  proof
    fix y 
    show "\<forall>x. y \<in> normss \<and> x \<in> normss \<and> x \<noteq> 1 \<longrightarrow>
          (\<exists>!r. y = otimess' r x)"
    proof
      fix x
      show " y \<in> normss \<and> x \<in> normss \<and> x \<noteq> 1 \<longrightarrow>
          (\<exists>!r. y = otimess' r x)"
      proof
        assume "y \<in> normss \<and> x \<in> normss \<and> x \<noteq> 1"
        show " (\<exists>!r. y = otimess' r x)"
        proof-
          have "inv T x\<noteq>0"
          proof (rule ccontr)
            assume "\<not>(inv T x\<noteq>0)"
            have "inv T x = 0"
              
              using \<open>\<not> inv T x \<noteq> 0\<close> by fastforce
            moreover have "x = T 0"
              using T_bij
            
              by (metis \<open>\<not> inv T x \<noteq> 0\<close> \<open>y \<in> normss \<and> x \<in> normss \<and> x \<noteq> 1\<close>
                  bij_betw_inv_into_right)
            ultimately show False
              by (simp add: T_def
                  \<open>y \<in> normss \<and> x \<in> normss \<and> x \<noteq> 1\<close>)
          qed
          moreover  obtain "r" where "r = (inv T y)/(inv T x)"
  
            by presburger
          moreover have "y = otimess' r x"
            unfolding otimess'_def T_bij
           
            using T_bij \<open>y \<in> normss \<and> x \<in> normss \<and> x \<noteq> 1\<close>
              bij_betw_inv_into_right calculation(1,2) by fastforce
          ultimately show ?thesis using T_bij
         
            by (smt (verit, best) UNIV_I \<open>y \<in> normss \<and> x \<in> normss \<and> x \<noteq> 1\<close>
                bij_betw_iff_bijections nonzero_eq_divide_eq
                otimess'_def)
        qed
      qed
    qed
  qed
qed


lemma norms_smult':
  fixes r::real
  assumes "a\<in>G" 
  shows "norm (fii (otimess r a)) =otimess' (abs(r)) (norm (fii a))"
proof-
  have "norm (fii a) = abs a"
    using assms fii_def by simp
  
  have "norm (fii a) \<ge>0"
    by simp
  moreover have "norm (fii a) = 0 \<or> (norm (fii a)>0)"

    by simp
  moreover {
    assume "norm (fii a) =0"
  
   have "norm (fii a) = abs a"
     using assms fii_def by simp
   moreover have "a=0"
  
     using \<open>norm (fii a) = 0\<close> calculation by auto
   ultimately have ?thesis
     unfolding otimess_def phi_def
    
     by (metis (no_types, lifting) G_def assms exp_zero
         mem_Collect_eq neg_0_less_iff_less not_exp_le_zero
         not_exp_less_zero)

 }
  moreover {

    assume "norm (fii a) >0"
    then have "fii a \<in> G"
    
    by (metis assms fii_def)
  moreover have "norm (fii a) \<in> normss "
    unfolding normss_def  phi_norms_pos_def
    
 
    using assms \<open>norm (fii a) = \<bar>a\<bar>\<close> by auto
  moreover obtain "m" where "T m = norm (fii a)"
    using `norm (fii a) \<in> normss ` T_bij
   
     by (meson bij_betw_iff_bijections)
  moreover have "m\<ge>0"
    
    using \<open>0 \<le> norm (fii a)\<close> calculation(3) x_pos_T_m_exp
    by presburger
  moreover have "T m  = exp m"
  
    by (metis calculation(4) T_def)
  moreover have "inv T (norm (fii a)) =m"
    using T_bij
    bij_betw_def
  
    by (metis calculation(3) inv_f_f)
  moreover have "m = ln (norm (fii a))"
   
    by (metis calculation(3) calculation(5) ln_exp)

  moreover have "(\<bar>r\<bar> * inv T (norm (fii a)))\<ge>0"
    
    using abs_ge_zero calculation(5,7) zero_le_mult_iff

    by (metis  zero_le_mult_iff abs_ge_zero calculation(4) calculation(6))
  moreover have "T (\<bar>r\<bar> * inv T (norm (fii a))) = exp ((\<bar>r\<bar> * inv T (norm (fii a))))"
    
    by (meson T_def calculation(8))
  moreover have "norm(fii a) = abs(a)"
    
   
    by (metis \<open>norm (fii a) = \<bar>a\<bar>\<close>)
  moreover have "otimess' (abs(r)) (norm (fii a)) = (abs(a)) powr (abs (r)) "
    unfolding otimess'_def ` norm (fii a) \<in> normss `
   
    by (metis calculation(10,2,3,5,6,9) exp_powr_real
        mult.commute)
  ultimately have ?thesis 
    by (metis  \<open>norm (fii a) = \<bar>a\<bar>\<close> \<open>T m = norm (fii a)\<close>  \<open>otimess' \<bar>r\<bar> (norm (fii a)) = \<bar>a\<bar> powr \<bar>r\<bar>\<close>
 assms f)
}
  ultimately show ?thesis by blast
qed

lemma ineq_1:
  assumes "a\<in> G" "b\<in>G"  
  shows "opluss' (norm (fii a)) (norm (fii b)) = (abs a) * (abs b)"
proof-

  have "(norm (fii a))\<in>normss"
    unfolding normss_def phi_norms_pos_def
 
    by (simp add: assms(1) fii_def)
moreover  have "(norm (fii b))\<in>normss"
    unfolding normss_def phi_norms_pos_def
 
    by (simp add: assms(2) fii_def)
  moreover have "(norm (fii a)) = (abs a)"
  
    using assms(1) fii_def real_norm_def by presburger
 moreover have "(norm (fii b)) = (abs b)"
  
    using assms(2) fii_def real_norm_def by presburger
  moreover have "opluss' (norm (fii a)) (norm (fii b)) = T ((inv T (abs a)) + (inv T (abs b)))"
    unfolding opluss'_def
    by (metis calculation(1,2,3,4))
moreover have "abs a \<ge>0"
    
    by simp
  moreover have "abs a \<in>normss"

    by (metis calculation(1) calculation(3))
  moreover obtain "m1" where "T m1 = abs a"
    
    by (metis calculation(1,3) ggv7.smult_one otimess'_def)
  moreover have "abs b \<ge>0"
    
    by simp
  moreover have "abs b \<in>normss"

    by (metis calculation(2) calculation(4))
  moreover have "abs a \<ge>1"
    using assms(1) G_def
  
    by (smt (verit, best) mem_Collect_eq)
 moreover have "abs b \<ge>1"
    using assms(2) G_def
  
    by (smt (verit, best) mem_Collect_eq)
  moreover obtain "m2" where "T m2 = abs b"
    using T_bij 
 
    by (meson bij_betw_inv_into_right calculation(10))
  moreover have "m1 = inv T (abs a)"
    using T_bij
  
    by (metis UNIV_I bij_betw_inv_into_left calculation(8))
      moreover have "m2 = inv T (abs b)"
    using T_bij
  
   
    by (metis UNIV_I bij_betw_inv_into_left
        calculation(13))
  moreover have "m1+m2\<ge>0"
  
    by (metis add_nonneg_nonneg calculation(13,6,8,9)
        x_pos_T_m_exp)
  
  moreover have "m1 = ln (abs a)"
    
    by (metis calculation(8) abs_ge_zero x_pos_T_m_exp ln_unique T_def)
  moreover have "m2= ln (abs b)"
  
    
    by (metis T_def calculation(13,9) ln_exp x_pos_T_m_exp)
  moreover have "T (m1+m2) = exp ((ln (abs a)) + (ln(abs b)))"
    
    by (metis T_def calculation(16,17,18))
  moreover have "(ln(abs a)) + (ln(abs b)) = ln ((abs a)*(abs b))"
    using ln_mult_pos[of "abs a" "abs b"]
    
    using calculation(11,12) by argo
  ultimately show ?thesis
    by (metis abs_norm_cancel exp_ln_abs mult_eq_0_iff
        norm_mult)
qed

lemma ineq_2:
  assumes "a\<in>G" "b\<in>G"
  shows "norm (fii (opluss a b)) = abs (phi ((inv phi a) + (inv phi b)))"
proof-
  have "opluss a b \<in> G"
    unfolding opluss_def phi_is_bij assms
 
    using assms(1,2) grc.gyroplus_closed opluss_def by auto
  moreover have "fii (opluss a b ) = opluss a b "
  
    by (simp add: calculation fii_def)
  moreover have "norm (fii (opluss a b)) = abs(opluss a b)"
   
    by (metis calculation(2) real_norm_def)
  ultimately show ?thesis 
    unfolding opluss_def assms
    using assms(1,2) by auto
qed

lemma phi_mono: 
  shows "\<forall>x y::real. x \<le> y \<longrightarrow> phi x \<le> phi y"
proof -
  have H: "\<forall>x y::real. x \<le> y \<longrightarrow> phi x \<le> phi y"
  proof (rule allI, rule allI, rule impI)
    fix x y :: real
    assume xy: "x \<le> y"

    show "phi x \<le> phi y"
    proof (cases "0 \<le> x")
      case True
      then have "0 \<le> y"
        using xy by linarith
      then show ?thesis
        using True xy
        by (simp add: phi_def)
    next
      case False
      then have xneg: "x < 0"
        by simp

      show ?thesis
      proof (cases "0 \<le> y")
        case True
        have "phi x < 0"
          using xneg by (simp add: phi_def)
        moreover have "0 < phi y"
          using True by (simp add: phi_def)
        ultimately show ?thesis
          by linarith
      next
        case False
        then have yneg: "y < 0"
          by simp

        have "- y \<le> - x"
          using xy by simp
        then have "exp (- y) \<le> exp (- x)"
          by simp
        then have "- exp (- x) \<le> - exp (- y)"
          by simp
        then show ?thesis
          using xneg yneg
          by (simp add: phi_def)
      qed
    qed
  qed
  then show ?thesis 
    by argo
 
qed

    
  
lemma norm_ineq_check:
  assumes "a\<in>G" "b\<in>G"  
  shows " norm (fii (opluss a  b)) \<le> opluss' (norm (fii a)) (norm (fii b))"
proof-
  have "abs a \<ge>1 "
    using G_def assms
  
    by (smt (verit, best) mem_Collect_eq)
  moreover have "abs b \<ge>1 "
    using G_def assms
  
    by (smt (verit, best) mem_Collect_eq)
  moreover have "(inv phi a )= ln (abs a) \<or> (inv phi a) = - ln(abs a)"
  proof-
    have "a<(-1) \<or> a\<ge>1"
      using G_def assms(1) by auto
moreover {
  assume a_less: "a < (-1::real)"

  have "abs a = -a"
    using a_less by simp

  have phi_preimage: "phi (- ln (abs a)) = a"
  proof -
    have y_neg: "- ln (abs a) < 0"
      using a_less by simp

    have "phi (- ln (abs a)) = - exp (- (- ln (abs a)))"
      using y_neg phi_def 
      by (metis verit_comp_simplify1(3))
    also have "... = - exp (ln (abs a))"
      by simp
    also have "... = - abs a"
      using a_less by simp
    also have "... = a"
      using a_less by simp
    finally show ?thesis .
  qed

  moreover have "inv phi a = - ln (abs a)"
    using phi_is_bij phi_preimage
      inv_f_eq
    
    by (metis bij_betw_def)

  ultimately have ?thesis
    by simp
}
  moreover {
  assume a_less: "a \<ge> (1::real)"

  have "abs a = a"
    using a_less by simp

  have phi_preimage: "phi ( ln (abs a)) = a"
  
    by (metis \<open>\<bar>a\<bar> = a\<close> a_less lemma_exp_total ln_exp
        phi_def)
 

  moreover have "inv phi a =  ln (abs a)"
    using phi_is_bij phi_preimage
      inv_f_eq
    
    by (metis bij_betw_def)

  ultimately have ?thesis
    by simp
}
  ultimately show ?thesis 
    by presburger
qed
  moreover have "(inv phi b )= ln (abs b) \<or> (inv phi b) = - ln(abs b)"
  proof-
    have "b<(-1) \<or> b\<ge>1"
      using G_def assms(2) by auto
moreover {
  assume a_less: "b < (-1::real)"

  have "abs b = -b"
    using a_less by simp

  have phi_preimage: "phi (- ln (abs b)) = b"
  proof -
    have y_neg: "- ln (abs b) < 0"
      using a_less by simp

    have "phi (- ln (abs b)) = - exp (- (- ln (abs b)))"
      using y_neg phi_def 
      by (metis verit_comp_simplify1(3))
    also have "... = - exp (ln (abs b))"
      by simp
    also have "... = - abs b"
      using a_less by simp
    also have "... = b"
      using a_less by simp
    finally show ?thesis .
  qed

  moreover have "inv phi b = - ln (abs b)"
    using phi_is_bij phi_preimage
      inv_f_eq
    
    by (metis bij_betw_def)

  ultimately have ?thesis
    by simp
}
  moreover {
  assume a_less: "b \<ge> (1::real)"

  have "abs b = b"
    using a_less by simp

  have phi_preimage: "phi ( ln (abs b)) = b"
  
    by (metis \<open>\<bar>b\<bar> = b\<close> a_less lemma_exp_total ln_exp
        phi_def)
 

  moreover have "inv phi b =  ln (abs b)"
    using phi_is_bij phi_preimage
      inv_f_eq
    
    by (metis bij_betw_def)

  ultimately have ?thesis
    by simp
}
  ultimately show ?thesis 
    by presburger
qed
  moreover have "-ln (abs a) -ln (abs b) \<le> (inv phi a) + (inv phi b) \<and>
   (inv phi a) + (inv phi b) \<le> ln (abs a) + ln (abs b)"
  proof-
    have "ln (abs a) \<ge> -ln (abs a)"
      
      by (simp add: calculation(1))
    moreover have "ln (abs b) \<ge> -ln (abs b)"
    
    
      by (simp add: \<open>1 \<le> \<bar>b\<bar>\<close>)
    moreover have "(inv phi a) = ln (abs a) \<or> (inv phi a) = -ln (abs a)"
     
      using \<open>inv phi a = ln \<bar>a\<bar> \<or> inv phi a = - ln \<bar>a\<bar>\<close> abs_real_def ln_minus
      by presburger
    moreover {
      assume "inv phi a = ln (abs a)"
      have "(inv phi b) = ln (abs b) \<or> (inv phi b) = -ln (abs b)"
        
        by (metis \<open>inv phi b = ln \<bar>b\<bar> \<or> inv phi b = - ln \<bar>b\<bar>\<close>
            )
      moreover {
        assume "inv phi b = ln (abs b)"
        then have ?thesis 
          
          using \<open>- ln \<bar>a\<bar> \<le> ln \<bar>a\<bar>\<close> \<open>- ln \<bar>b\<bar> \<le> ln \<bar>b\<bar>\<close> \<open>inv phi a = ln \<bar>a\<bar>\<close>
          by argo
      }
      moreover {
        assume "inv phi b = -ln (abs b)"
        then have ?thesis 
         
          using \<open>- ln \<bar>a\<bar> \<le> ln \<bar>a\<bar>\<close> \<open>- ln \<bar>b\<bar> \<le> ln \<bar>b\<bar>\<close> \<open>inv phi a = ln \<bar>a\<bar>\<close>
          by argo
      }
      ultimately have ?thesis
        
        by linarith
    }

 moreover {
      assume "inv phi a = -ln (abs a)"
      have "(inv phi b) = ln (abs b) \<or> (inv phi b) = -ln (abs b)"
        
        by (metis \<open>inv phi b = ln \<bar>b\<bar> \<or> inv phi b = - ln \<bar>b\<bar>\<close>)
      moreover {
        assume "inv phi b = ln (abs b)"
        then have ?thesis 
        
          using \<open>- ln \<bar>a\<bar> \<le> ln \<bar>a\<bar>\<close> \<open>- ln \<bar>b\<bar> \<le> ln \<bar>b\<bar>\<close> \<open>inv phi a = - ln \<bar>a\<bar>\<close>
          by argo
      }
      moreover {
        assume "inv phi b = -ln (abs b)"
        then have ?thesis 
          
          using \<open>- ln \<bar>a\<bar> \<le> ln \<bar>a\<bar>\<close> \<open>- ln \<bar>b\<bar> \<le> ln \<bar>b\<bar>\<close> \<open>inv phi a = - ln \<bar>a\<bar>\<close>
          by argo
      }
      ultimately have ?thesis
        
        by linarith
    }
    ultimately show ?thesis 
      by satx
  qed
  moreover have "-abs(a*b) \<le> phi (-ln (abs a) -ln (abs b))"
    using phi_def
  proof-
    have "-ln (abs a) -ln (abs b) < 0 \<or> -ln (abs a) -ln(abs b)\<ge>0"
      
      by argo
    moreover {
      assume "-ln (abs a) -ln (abs b) < 0"
      then have "phi (-ln (abs a) -ln (abs b)) = - exp (ln(abs a) + ln (abs b))"
        using phi_def 
        by (smt (verit, best))
      then have ?thesis 
        
        by (metis (no_types, opaque_lifting) \<open>1 \<le> \<bar>a\<bar>\<close> \<open>1 \<le> \<bar>b\<bar>\<close> abs_mult
            lemma_exp_total less_eq_real_def ln_exp mult_exp_exp)
       
    }
    moreover {
      assume "-ln (abs a) -ln (abs b) \<ge> 0"
  then have "phi (-ln (abs a) -ln (abs b)) = exp (-(ln(abs a) + ln (abs b)))"
    using phi_def 
    
    by (metis ab_group_add_class.ab_diff_conv_add_uminus
        minus_add_distrib)
  then have "phi (-ln (abs a) -ln (abs b)) = 1/abs(a*b)"
    
    by (metis (no_types, lifting) \<open>1 \<le> \<bar>a\<bar>\<close> \<open>1 \<le> \<bar>b\<bar>\<close> abs_idempotent abs_mult
        exp_ln_abs exp_minus' ln_mult mult_eq_0_iff not_one_le_zero)
  
  then have ?thesis
       by (smt (verit, ccfv_SIG) zero_le_divide_1_iff)
   }
   ultimately show ?thesis
     by satx
 qed
  moreover have " phi (-ln (abs a) -ln (abs b)) \<le> phi((inv phi a)+(inv phi b))"
    
    by (metis  calculation(5) phi_mono)
  moreover have " phi((inv phi a)+(inv phi b)) \<le> phi (ln (abs a) + ln(abs b))"
   
    using calculation(5) phi_mono by blast
  moreover have "phi (ln (abs a) + ln(abs b)) \<le> abs(a*b)"
  proof-
    have "ln (abs a) + ln(abs b) \<ge>0 \<or> ln (abs a) + ln(abs b)<0"
      by argo
    moreover {
      assume "ln (abs a) + ln(abs b) \<ge>0"
      then have "phi (ln (abs a) + ln(abs b)) = exp (ln (abs a) + ln(abs b))"
        
        by (metis phi_def)
      then have ?thesis 
        by (metis \<open>1 \<le> \<bar>a\<bar>\<close> \<open>1 \<le> \<bar>b\<bar>\<close> abs_abs abs_eq_0 abs_mult exp_ln_abs ln_mult_pos
            mult_eq_0_iff not_one_le_zero order.strict_trans2 order_refl
            zero_less_one)
    }
    moreover {
       assume "ln (abs a) + ln(abs b) <0"
       then have ?thesis
         
         using \<open>1 \<le> \<bar>a\<bar>\<close> \<open>1 \<le> \<bar>b\<bar>\<close> add_increasing2 calculation(2) ln_ge_zero
         by blast
       
     }
     ultimately show ?thesis
       by satx
   qed
   moreover have "abs (phi ((inv phi a)+(inv phi b))) \<le> abs(a*b)"
     using calculation(6,7,8,9) by argo
   moreover have "abs (phi ((inv phi a)+(inv phi b))) =  norm (fii (opluss a b))"
  
     by (metis ineq_2 assms(2) assms(1))
   moreover have "abs(a*b) =  opluss' (norm (fii a)) (norm (fii b))"
     
     by (metis ineq_1 assms(2) assms(1) abs_mult)
   ultimately show ?thesis
    
     by linarith
qed

(*
interpretation ggc: gyrocommutative_gyrogroup G "1::real" opluss "(phi 
\<circ> (\<lambda>x. -1 * ((inv_into UNIV phi) x)))" "\<lambda>a. (\<lambda>b. (\<lambda>x. x))"
*)

lemma normis:
  shows " {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} = normss"
proof
  show " {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<subseteq> normss"
    using fii_def normss_def phi_norms_neg_def phi_norms_pos_def by auto
next
  show "normss \<subseteq> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} "
    using fii_def normss_def phi_norms_neg_def phi_norms_pos_def by fastforce
qed

lemma ggv7_lemma:
  shows "one_dim_vector_space_with_domain normss opluss' 1 otimess'"
  using ggv7.one_dim_vector_space_with_domain_axioms by blast
interpretation ggv: ggv_space G "1::real" opluss  "(phi 
\<circ> (\<lambda>x. -1 * ((inv_into UNIV phi) x)))" "\<lambda>a. (\<lambda>b. (\<lambda>x. x))"  otimess
opluss' otimess' fii 1
proof
  show "inj_on fii G"
    by (metis fii_def inj_onI)
next
  show "\<forall>r. \<forall>x\<in>G. otimess r x \<in> G"
    using scale_closed_check by blast
next
  show " \<forall>a\<in>G. otimess 1 a = a"
    using scale_1_check by blast
next
  show "\<forall>r1 r2. \<forall>a\<in>G. otimess (r1 + r2) a = opluss (otimess r1 a) (otimess r2 a)"
        using scale_distrib_check by blast
next
  show " \<forall>r1 r2. \<forall>a\<in>G. otimess (r1 * r2) a = otimess r1 (otimess r2 a)"
    using scale_assoc_check by blast
next
  show " \<And>x y. x \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
           y \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
           opluss' x y \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)}"
    using ggv7.add_closed normis by auto
next
  show "1 \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)}"
    using ggv7.zero_in_dom normis by argo
next
  show "\<And>x y z.
       x \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
       y \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
       z \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
       opluss' (opluss' x y) z = opluss' x (opluss' y z)"
    using ggv7.add_assoc normis by blast
next
  show "\<And>x y. x \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
           y \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
           opluss' x y = opluss' y x"
    using ggv7.add_comm normis by blast
next
  show "\<And>x. x \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow> opluss' x 1 = x"
    using ggv7.add_zero normis by blast
next
  show "\<And>x. x \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
         \<exists>y\<in>{x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)}. opluss' x y = 1"
    using ggv7.add_inv normis by blast
next
  show "\<And>x a. x \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
           otimess' a x \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)}"
    using ggv7.smult_closed normis by blast
next
  show "\<And>x a b.
       x \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
       otimess' (a + b) x = opluss' (otimess' a x) (otimess' b x)"
       using ggv7.smult_distr_sadd normis by blast
next
     show " \<And>x a b.
       x \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
       otimess' a (otimess' b x) = otimess' (a * b) x"
       using ggv7.smult_assoc normis by blast
   next
     show "\<And>x. x \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow> otimess' 1 x = x"
       using ggv7.smult_one normis by blast
   next
     show " \<And>x y a.
       x \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
       y \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<Longrightarrow>
       otimess' a (opluss' x y) = opluss' (otimess' a x) (otimess' a y)"
       using ggv7.smult_distr_sadd2 normis by blast
   next
     show "\<forall>y x. y \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<and>
          x \<in> {x. \<exists>a\<in>G. x = norm (fii a) \<or> x = - norm (fii a)} \<and> x \<noteq> 1 \<longrightarrow>
          (\<exists>!r. y = otimess' r x)"
       by (metis (lifting) ggv7_lemma normis one_dim_vector_space_with_domain_axioms_def
           one_dim_vector_space_with_domain_def)
   next
     show "\<forall>r. \<forall>a\<in>G. norm (fii (otimess r a)) = otimess' \<bar>r\<bar> (norm (fii a))"
       using norms_smult' by blast
   next
     show " \<forall>a\<in>G. \<forall>r. a \<noteq> 1 \<and> r \<noteq> 0 \<longrightarrow>
               fii (otimess \<bar>r\<bar> a) /\<^sub>R norm (fii (otimess r a)) =
               fii a /\<^sub>R norm (fii a)"

     proof
       fix a
       assume "a\<in>G"
       show "\<forall>r. a \<noteq> 1 \<and> r \<noteq> 0 \<longrightarrow>
               fii (otimess \<bar>r\<bar> a) /\<^sub>R norm (fii (otimess r a)) =
               fii a /\<^sub>R norm (fii a)"
       proof
         fix r
         show " a \<noteq> 1 \<and> r \<noteq> 0 \<longrightarrow>
               fii (otimess \<bar>r\<bar> a) /\<^sub>R norm (fii (otimess r a)) =
               fii a /\<^sub>R norm (fii a)"

         proof
           assume "a \<noteq> 1 \<and> r \<noteq> 0"
           show " fii (otimess \<bar>r\<bar> a) /\<^sub>R norm (fii (otimess r a)) =
               fii a /\<^sub>R norm (fii a)"
           proof-
             have "a\<ge>1 \<or> a<1"
             
               by force
             moreover {
               assume "a\<ge>1"
               then have "fii (otimess \<bar>r\<bar> a) = a powr (abs(r))"
                
                 using \<open>a \<in> G\<close> f_1 by blast
               moreover have "norm (fii (otimess r a)) = (abs(a)) powr (abs(r))"
                
                 using \<open>a \<in> G\<close> f by blast
               moreover have "a= abs(a)"
                 
                 using \<open>1 \<le> a\<close> by force
               ultimately have ?thesis 
                 by (metis \<open>a \<in> G\<close> fii_def left_inverse powr_eq_0_iff real_norm_def
                     real_scaleR_def)
             } moreover {
               assume "a<1"
               then have "fii (otimess \<bar>r\<bar> a) =- ((abs(a)) powr (abs(r)))"
                
                 using \<open>a \<in> G\<close> f_2 
                 by (metis \<open>a \<noteq> 1 \<and> r \<noteq> 0\<close> mult_minus1 powr_one' powr_powr
                     verit_minus_simplify(4))
               moreover have "norm (fii (otimess r a)) = (abs(a)) powr (abs(r))"
                
                 using \<open>a \<in> G\<close> f by blast
               moreover have "a= -abs(a)"
                 
                 by (smt (verit, ccfv_threshold) G_def \<open>a < 1\<close> \<open>a \<in> G\<close> mem_Collect_eq)
               ultimately have ?thesis 
                 by (smt (verit, ccfv_SIG) \<open>a \<in> G\<close> f fii_def left_inverse powr_eq_0_iff
                     real_norm_def real_scaleR_def scaleR_right.diff)
             }
             ultimately show ?thesis 
               by fastforce
           qed
         qed
       qed
     qed
   next
     show "\<forall>r. \<forall>u\<in>G. \<forall>v\<in>G. \<forall>a\<in>G. otimess r a = otimess r a"
     
       by fastforce
   next
     show " \<forall>r1 r2. \<forall>v\<in>G. \<forall>x\<in>G. x = x"
       by fastforce
   next
     show " \<forall>a\<in>G. \<forall>b\<in>G. norm (fii (opluss a b)) \<le> opluss' (norm (fii a)) (norm (fii b))"
       using norm_ineq_check by blast
   next
     show "\<forall>u\<in>G. \<forall>v\<in>G. \<forall>a\<in>G. norm (fii a) = norm (fii a) "
       by blast
qed


end