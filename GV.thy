theory GV
imports Main GyroGroup "HOL-Analysis.Inner_Product" HOL.Real_Vector_Spaces GGV
begin

locale gyrovector_space = 
  fixes dom::"'a::real_inner set"
  fixes gyrozero :: "'a" ("0\<^sub>g")
  fixes gyroplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 100)
  fixes gyroinv :: "'a \<Rightarrow> 'a" ("\<ominus>")
  fixes gyr :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes scale ::"real \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 105) 
  fixes plus'::"real \<Rightarrow> real \<Rightarrow> real"
  fixes smult'::"real \<Rightarrow> real \<Rightarrow> real"
  fixes plus'_zero::"real"
  assumes zero_in_dom:"gyrozero \<in> dom"
   
  assumes gyroplus_closed:" (a\<in> dom \<and> b\<in>dom)\<longrightarrow>  a \<oplus> b \<in> dom"
  assumes non_trivial_dom:"\<exists>a. (a\<in>dom \<and> a\<noteq>gyrozero)" (*non-trivial domain*)

  assumes ax1:"a\<in>dom \<longrightarrow> gyroinv a \<in> dom"
  assumes "a\<in>dom \<and> b\<in>dom \<and> c\<in>dom \<longrightarrow> gyr a b c \<in> dom"
  assumes gyro_left_id [simp]: "\<And> a. (a\<in>dom \<longrightarrow> 0\<^sub>g \<oplus> a = a)"
  assumes gyro_left_inv [simp]: "\<And> a. (a\<in>dom \<longrightarrow> \<ominus>a \<oplus> a = 0\<^sub>g)"
  assumes gyro_left_assoc: "\<And> a b z.(a\<in>dom \<and> b\<in>dom \<and> z\<in>dom \<longrightarrow> 
a \<oplus> (b \<oplus> z) = (a \<oplus> b) \<oplus> (gyr a b z))"
  assumes gyr_left_loop: "\<And> a b. (a\<in>dom \<and> b\<in>dom \<longrightarrow> (\<forall>x\<in>dom. gyr a b x = gyr (a \<oplus> b) b x))"
  assumes gyr_gyroaut: "\<And> x y. (x\<in>dom \<and> y\<in>dom \<longrightarrow> 
 ((\<forall> a\<in>dom. (\<forall>b\<in>dom. (
 (gyr x y (a \<oplus> b)) = ((gyr x y a) \<oplus> (gyr x y b))))) \<and> (bij_betw (gyr x y) dom dom)))"
  assumes gyro_commute: "\<forall>a\<in>dom.\<forall>b\<in>dom. (a \<oplus> b = gyr a b (b \<oplus> a))"
  assumes scale_closed: "\<forall>r::real. (\<forall>x\<in>dom. ((scale r x) \<in> dom))"
  assumes scale_1:"\<forall>a\<in>dom. scale 1 a = a"
  assumes  scale_distrib: "\<forall>r1::real. \<forall>r2::real. \<forall>a\<in>dom. scale (r1+r2) a = (scale r1 a) \<oplus> (scale r2 a)"
  assumes  scale_assoc:"\<forall>r1::real. \<forall>r2::real. \<forall>a\<in>dom. scale (r1*r2) a = scale r1 (scale r2 a)"
  assumes one_dim_vs:"one_dim_vector_space_with_domain {x.\<exists>a\<in>dom. x = norm ( a) \<or> x = - norm ( a)} plus' plus'_zero smult'"
  assumes norm_smult':"\<forall>r::real.\<forall>a\<in>dom. norm ( (scale r a)) = smult' \<bar>r\<bar> (norm ( a))"
  assumes scale_prop1:"\<forall>a\<in>dom. \<forall>r::real. ((a\<noteq>gyrozero \<and> r\<noteq>0)\<longrightarrow> ( (scale \<bar>r\<bar> a)) /\<^sub>R (norm ( (scale r a))) = ( a) /\<^sub>R (norm ( a)))"
  assumes scale_gyr1:"\<forall>r::real. \<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>a\<in>dom. gyr u v (scale r a) = scale r (gyr u v a)"
  assumes scale_gyr_id: "\<forall>r1::real. \<forall>r2::real. \<forall>v\<in>dom. \<forall>x\<in>dom. (gyr (scale r1 v) (scale r2 v) x = x)"

  assumes norm_triangle_ineq: "\<forall>a\<in>dom. \<forall>b\<in>dom. norm ( (a \<oplus> b)) \<le> plus' (norm ( a)) (norm ( b))"
  assumes inner_gyroauto_invariant: "\<forall>u\<in>dom.\<forall>v\<in>dom.\<forall>a\<in>dom.\<forall>b\<in>dom. inner ((gyr u v a))  ((gyr u v b)) = inner ( a) ( b)"

begin

lemma gspace_id_is_ggv_space_help:
  shows   "one_dim_vector_space_with_domain {x.\<exists>a\<in>dom. x = norm (id a) \<or> x = - norm ( id a)} plus' plus'_zero smult'"
  using one_dim_vs 
  by simp

interpretation is_ggv:  ggv_space dom gyrozero gyroplus gyroinv gyr scale plus' smult' id plus'_zero

proof
  show " gyrozero \<in> dom"
    by (simp add: zero_in_dom)
next
  show "\<And>a b. a \<in> dom \<and> b \<in> dom \<longrightarrow> gyroplus a b \<in> dom"
    using  gyroplus_closed by blast
next
  show "\<exists>a. a \<in> dom \<and> a \<noteq> gyrozero"
    using  gyrovector_space_def 
    using non_trivial_dom by force
next
  show " \<And>a. a \<in> dom \<longrightarrow> gyroinv a \<in> dom"
    using  ax1 by blast
next
  show "\<And>a b c. a \<in> dom \<and> b \<in> dom \<and> c \<in> dom \<longrightarrow> gyr a b c \<in> dom"
    by (meson  bij_betwE gyr_gyroaut)
next
  show "\<And>a. a \<in> dom \<longrightarrow> gyroplus gyrozero a = a"
    using gyro_left_id by blast
next
  show "\<And>a. a \<in> dom \<longrightarrow> gyroplus (gyroinv a) a = gyrozero"
    using gyro_left_inv by blast
next
  show " \<And>a b z.
       a \<in> dom \<and> b \<in> dom \<and> z \<in> dom \<longrightarrow>
       gyroplus a (gyroplus b z) = gyroplus (gyroplus a b) (gyr a b z)"
    using gyro_left_assoc by blast
next 
  show "\<And>a b. a \<in> dom \<and> b \<in> dom \<longrightarrow> (\<forall>x\<in>dom. gyr a b x = gyr (gyroplus a b) b x)"
    using gyr_left_loop by blast
next
  show "\<And>x y. x \<in> dom \<and> y \<in> dom \<longrightarrow> gyrogroupoid.gyroaut dom gyroplus (gyr x y)"

  proof-
    fix x y
    show " x \<in> dom \<and> y \<in> dom \<longrightarrow> gyrogroupoid.gyroaut dom gyroplus (gyr x y)"
    proof
      assume "x \<in> dom \<and> y \<in> dom"
      show " gyrogroupoid.gyroaut dom gyroplus (gyr x y)"
      proof-
        have "x \<in> dom \<and> y \<in> dom \<longrightarrow>
    (\<forall>a\<in>dom.
        \<forall>b\<in>dom. gyr x y (gyroplus a b) = gyroplus (gyr x y a) (gyr x y b)) \<and>
    bij_betw (gyr x y) dom dom"
          using    gyr_gyroaut[of x y]
       
          by blast
        moreover have *:"  (\<forall>a\<in>dom.
        \<forall>b\<in>dom. gyr x y (gyroplus a b) = gyroplus (gyr x y a) (gyr x y b)) \<and>
    bij_betw (gyr x y) dom dom"
          
          using \<open>x \<in> dom \<and> y \<in> dom\<close> calculation by force
        moreover have **: "gyrogroupoid dom gyrozero gyroplus "
          
          by (simp add: gyrogroupoid_def gyroplus_closed non_trivial_dom
              zero_in_dom)
         
        ultimately show ?thesis
          unfolding  gyrogroupoid.gyroaut_def
          using gyrogroupoid.gyroaut_def[of dom gyrozero gyroplus "(gyr x y)"]
        * **
    gyrogroupoid_def
            gyrovector_space_def
          
          by argo
      qed
    qed
  qed
next
  show "\<forall>a\<in>dom. \<forall>b\<in>dom. gyroplus a b = gyr a b (gyroplus b a)"
    using gyro_commute by blast
next
  show " inj_on id dom"
    by simp
next
  show "\<forall>r. \<forall>x\<in>dom. scale r x \<in> dom"
    using scale_closed by blast
next
  show " \<forall>a\<in>dom. scale 1 a = a"
    using scale_1 by blast
next
  show "\<forall>r1 r2. \<forall>a\<in>dom. scale (r1 + r2) a = gyroplus (scale r1 a) (scale r2 a)"
    using scale_distrib by blast
next
  show " \<forall>r1 r2. \<forall>a\<in>dom. scale (r1 * r2) a = scale r1 (scale r2 a)"
    using scale_assoc by blast
next
  show "\<And>x y. x \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
           y \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
           plus' x y \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)}"
    using one_dim_vs gspace_id_is_ggv_space_help
    by (meson one_dim_vector_space_with_domain_def
        vector_space_with_domain.add_closed)
next
  show " plus'_zero \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)}"
    using one_dim_vs gspace_id_is_ggv_space_help
    by (simp add: one_dim_vector_space_with_domain_def
        vector_space_with_domain_def)
next
  show "\<And>x y z.
       x \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
       y \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
       z \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
       plus' (plus' x y) z = plus' x (plus' y z)"
    using one_dim_vs gspace_id_is_ggv_space_help

    by (simp add: one_dim_vector_space_with_domain_def
        vector_space_with_domain_def)
next
  show "\<And>x y. x \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
           y \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
           plus' x y = plus' y x"
   using one_dim_vs gspace_id_is_ggv_space_help

    by (simp add: one_dim_vector_space_with_domain_def
        vector_space_with_domain_def)
next
  show "\<And>x. x \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
         plus' x plus'_zero = x"
      using one_dim_vs gspace_id_is_ggv_space_help

    by (simp add: one_dim_vector_space_with_domain_def
        vector_space_with_domain_def)
next
  show "\<And>x. x \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
         \<exists>y\<in>{x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)}.
            plus' x y = plus'_zero"
   using one_dim_vs gspace_id_is_ggv_space_help

    by (simp add: one_dim_vector_space_with_domain_def
        vector_space_with_domain_def)
next
  show " \<And>x a. x \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
           smult' a x \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)}"
      using one_dim_vs gspace_id_is_ggv_space_help

    by (simp add: one_dim_vector_space_with_domain_def
        vector_space_with_domain_def)
next
  show "\<And>x a b.
       x \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
       smult' (a + b) x = plus' (smult' a x) (smult' b x)"
     using one_dim_vs gspace_id_is_ggv_space_help

    by (simp add: one_dim_vector_space_with_domain_def
        vector_space_with_domain_def)
next
  show "\<And>x a b.
       x \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
       smult' a (smult' b x) = smult' (a * b) x"
  using one_dim_vs gspace_id_is_ggv_space_help

    by (simp add: one_dim_vector_space_with_domain_def
        vector_space_with_domain_def)
next
  show "\<And>x. x \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
         smult' 1 x = x"
   using one_dim_vs gspace_id_is_ggv_space_help

    by (simp add: one_dim_vector_space_with_domain_def
        vector_space_with_domain_def)
next
  show "\<And>x y a.
       x \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
       y \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<Longrightarrow>
       smult' a (plus' x y) = plus' (smult' a x) (smult' a y)"
 using one_dim_vs gspace_id_is_ggv_space_help

    by (simp add: one_dim_vector_space_with_domain_def
        vector_space_with_domain_def)
next
  show "\<forall>y x. y \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<and>
          x \<in> {x. \<exists>a\<in>dom. x = norm (id a) \<or> x = - norm (id a)} \<and>
          x \<noteq> plus'_zero \<longrightarrow>
          (\<exists>!r. y = smult' r x)"
    using one_dim_vs gspace_id_is_ggv_space_help

   
    by (simp add: one_dim_vector_space_with_domain_axioms_def
        one_dim_vector_space_with_domain_def)
 
next
  show "\<forall>r. \<forall>a\<in>dom. norm (id (scale r a)) = smult' \<bar>r\<bar> (norm (id a))"
   
    by (simp add: norm_smult')
next
  show "\<forall>a\<in>dom.
       \<forall>r. a \<noteq> gyrozero \<and> r \<noteq> 0 \<longrightarrow>
           id (scale \<bar>r\<bar> a) /\<^sub>R norm (id (scale r a)) = id a /\<^sub>R norm (id a)"
 
    by (simp add: scale_prop1)
next
  show "\<forall>r. \<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>a\<in>dom. gyr u v (scale r a) = scale r (gyr u v a)"
  
    using scale_gyr1 by force
next
  show "\<forall>r1 r2. \<forall>v\<in>dom. \<forall>x\<in>dom. gyr (scale r1 v) (scale r2 v) x = x"
    
    using scale_gyr_id by blast
next
  show "\<forall>a\<in>dom.
       \<forall>b\<in>dom. norm (id (gyroplus a b)) \<le> plus' (norm (id a)) (norm (id b))"
    by (metis  eq_id_iff norm_triangle_ineq)
next
  show "\<forall>u\<in>dom. \<forall>v\<in>dom. \<forall>a\<in>dom. norm (id (gyr u v a)) = norm (id a)"
    
    by (smt (verit, ccfv_threshold)  eq_id_iff
        inner_gyroauto_invariant norm_eq_square)
qed

lemma is_ggv_lemma: 
  shows "ggv_space dom gyrozero gyroplus gyroinv gyr scale plus' smult' id plus'_zero"
  using is_ggv.ggv_space_axioms by auto
end


sublocale gyrovector_space \<subseteq> ggv_space dom gyrozero gyroplus gyroinv gyr scale plus' smult' id plus'_zero
  using is_ggv_lemma by auto


lemma gspace_id_is_ggv_space:
  assumes " gyrovector_space dom1 gyrozero gyroplus gyroinv gyr scale plus' smult' plus'_zero"

shows  " ggv_space dom1 gyrozero gyroplus gyroinv gyr scale plus' smult' id plus'_zero"
  by (simp add: assms gyrovector_space.is_ggv_lemma)

lemma helper_ggv_space_id_is_gspace:
  shows "{x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} = {x. \<exists>a\<in>dom1. x = norm (id a) \<or> x = - norm (id a)}"
  by auto

lemma helper_ggv_space_id_is_gspace2:
   assumes  "ggv_space dom1 gyrozero gyroplus gyroinv gyr scale plus' smult' id plus'_zero"
  shows "one_dim_vector_space_with_domain {x.\<exists>a\<in>dom1. x = norm ( a) \<or> x = - norm ( a)} plus' plus'_zero smult'"
  using assms ggv_intro.one_dim_vs_ggv ggv_space.axioms(1) by fastforce
lemma ggv_space_id_is_gspace:
 assumes  "ggv_space dom1 gyrozero gyroplus gyroinv gyr scale plus' smult' id plus'_zero"
"\<forall>u\<in>dom1.
       \<forall>v\<in>dom1. \<forall>a\<in>dom1. \<forall>b\<in>dom1. inner (gyr u v a) (gyr u v b) = inner a b "  
shows " gyrovector_space dom1 gyrozero gyroplus gyroinv gyr scale plus' smult' plus'_zero"
proof
  show "gyrozero \<in> dom1"
    by (meson assms ggv_intro.axioms(1) ggv_space_def
        gyrocommutative_gyrogroup_def gyrogroup_def
        gyrogroupoid.zero_in_dom)
next
  show " \<And>a b. a \<in> dom1 \<and> b \<in> dom1 \<longrightarrow> gyroplus a b \<in> dom1"
    by (metis assms(1) ggv_intro.axioms(1) ggv_space_def
        gyrocommutative_gyrogroup_def gyrogroup_def gyrogroupoid_def)
next  
  show "\<exists>a. a \<in> dom1 \<and> a \<noteq> gyrozero"
    by (meson assms ggv_intro.axioms(1) ggv_space_def
        gyrocommutative_gyrogroup_def gyrogroup_def gyrogroupoid_def)
next
  show "\<And>a. a \<in> dom1 \<longrightarrow> gyroinv a \<in> dom1"
    by (metis assms(1) ggv_intro.scale_closed_ggv ggv_space.scale_minus1
        ggv_space_def)
next
  show "\<And>a b c. a \<in> dom1 \<and> b \<in> dom1 \<and> c \<in> dom1 \<longrightarrow> gyr a b c \<in> dom1"
    by (metis assms(1) ggv_intro_def ggv_space_def gyrocommutative_gyrogroup_def
        gyrogroup.gyr_def_closed)
next
  show "\<And>a. a \<in> dom1 \<longrightarrow> gyroplus gyrozero a = a"
    by (meson assms ggv_intro_def ggv_space_def gyrocommutative_gyrogroup_def
        gyrogroup.gyro_left_id)
next
  show " \<And>a. a \<in> dom1 \<longrightarrow> gyroplus (gyroinv a) a = gyrozero"
    by (meson assms ggv_intro_def ggv_space_def gyrocommutative_gyrogroup_def
        gyrogroup.gyro_left_inv)
next
  show "\<And>a b z.
       a \<in> dom1 \<and> b \<in> dom1 \<and> z \<in> dom1 \<longrightarrow>
       gyroplus a (gyroplus b z) = gyroplus (gyroplus a b) (gyr a b z)"
    by (meson assms ggv_intro_def ggv_space_def gyrocommutative_gyrogroup_def
        gyrogroup.gyro_left_assoc)
next
  show "\<And>a b. a \<in> dom1 \<and> b \<in> dom1 \<longrightarrow>
           (\<forall>x\<in>dom1. gyr a b x = gyr (gyroplus a b) b x)"
    by (meson assms ggv_intro_def ggv_space_def gyrocommutative_gyrogroup_def
        gyrogroup.gyr_left_loop)
next
  show "\<And>x y. x \<in> dom1 \<and> y \<in> dom1 \<longrightarrow>
           (\<forall>a\<in>dom1.
               \<forall>b\<in>dom1.
                  gyr x y (gyroplus a b) =
                  gyroplus (gyr x y a) (gyr x y b)) \<and>
           bij_betw (gyr x y) dom1 dom1"
    using gyrogroupoid.gyroaut_def
    by (metis assms(1) ggv_intro.axioms(1) ggv_space.axioms(1)
        gyrocommutative_gyrogroup_def gyrogroup.axioms(1)
        gyrogroup.gyr_gyroaut)
next
  show " \<forall>a\<in>dom1. \<forall>b\<in>dom1. gyroplus a b = gyr a b (gyroplus b a)"
    by (meson assms ggv_intro_def ggv_space_def
        gyrocommutative_gyrogroup.gyro_commute)
next
  show " \<forall>r. \<forall>x\<in>dom1. scale r x \<in> dom1"
    by (meson assms ggv_intro.scale_closed_ggv ggv_space_def)
next
  show "\<forall>a\<in>dom1. scale 1 a = a"
    by (meson assms ggv_intro.scale_1_ggv ggv_space_def)
next
  show " \<forall>r1 r2. \<forall>a\<in>dom1. scale (r1 + r2) a = gyroplus (scale r1 a) (scale r2 a)"
    by (meson assms ggv_intro.scale_distrib_ggv ggv_space_def)
next
  show " \<forall>r1 r2. \<forall>a\<in>dom1. scale (r1 * r2) a = scale r1 (scale r2 a)"
    by (meson assms ggv_intro.scale_assoc_ggv ggv_space_def)
next
  show "\<And>x y. x \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
           y \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
           plus' x y \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a}"
    by (smt (verit, ccfv_threshold) Collect_cong assms ggv_intro.one_dim_vs_ggv
        ggv_space_def id_apply one_dim_vector_space_with_domain_def
        vector_space_with_domain.add_closed)
next
  show "plus'_zero \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a}"
    using Collect_cong assms ggv_intro.one_dim_vs_ggv ggv_space_def
        id_apply one_dim_vector_space_with_domain_def
        vector_space_with_domain_def helper_ggv_space_id_is_gspace
          ggv_intro.one_dim_vs_ggv  helper_ggv_space_id_is_gspace2[OF assms(1)]
    by (smt (z3))
next
  show "\<And>x y z.
       x \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
       y \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
       z \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
       plus' (plus' x y) z = plus' x (plus' y z)"
   using Collect_cong assms ggv_intro.one_dim_vs_ggv ggv_space_def
        id_apply one_dim_vector_space_with_domain_def
        vector_space_with_domain_def helper_ggv_space_id_is_gspace
           ggv_intro.one_dim_vs_ggv  helper_ggv_space_id_is_gspace2[OF assms(1)]
   by (smt (z3))
next
  show "\<And>x y. x \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
           y \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
           plus' x y = plus' y x"
using Collect_cong assms ggv_intro.one_dim_vs_ggv ggv_space_def
        id_apply one_dim_vector_space_with_domain_def
        vector_space_with_domain_def helper_ggv_space_id_is_gspace
           ggv_intro.one_dim_vs_ggv  helper_ggv_space_id_is_gspace2[OF assms(1)]
  by (smt (z3))
next
  show "\<And>x. x \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
         plus' x plus'_zero = x"
  using Collect_cong assms  ggv_intro.one_dim_vs_ggv ggv_space_def
        id_apply one_dim_vector_space_with_domain_def
        vector_space_with_domain_def helper_ggv_space_id_is_gspace
          ggv_intro.one_dim_vs_ggv  helper_ggv_space_id_is_gspace2[OF assms(1)]
  by (smt (z3))
next
  show "\<And>x. x \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
         \<exists>y\<in>{x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a}. plus' x y = plus'_zero"
    using Collect_cong assms  ggv_intro.one_dim_vs_ggv ggv_space_def
        id_apply one_dim_vector_space_with_domain_def
        vector_space_with_domain_def helper_ggv_space_id_is_gspace
         ggv_intro.one_dim_vs_ggv  helper_ggv_space_id_is_gspace2[OF assms(1)]
    by (smt (z3))
next
  show "\<And>x a. x \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
           smult' a x \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a}"
 using Collect_cong assms  ggv_intro.one_dim_vs_ggv ggv_space_def
        id_apply one_dim_vector_space_with_domain_def
        vector_space_with_domain_def helper_ggv_space_id_is_gspace
           ggv_intro.one_dim_vs_ggv  helper_ggv_space_id_is_gspace2[OF assms(1)]
  by (smt (z3))
next
  show " \<And>x a b.
       x \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
       smult' (a + b) x = plus' (smult' a x) (smult' b x)"
   using Collect_cong assms  ggv_intro.one_dim_vs_ggv ggv_space_def
        id_apply one_dim_vector_space_with_domain_def
        vector_space_with_domain_def helper_ggv_space_id_is_gspace
           ggv_intro.one_dim_vs_ggv helper_ggv_space_id_is_gspace2[OF assms(1)]
   by (smt (z3))
next
  show "\<And>x a b.
       x \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
       smult' a (smult' b x) = smult' (a * b) x"
 using Collect_cong assms  ggv_intro.one_dim_vs_ggv ggv_space_def
        id_apply one_dim_vector_space_with_domain_def
        vector_space_with_domain_def helper_ggv_space_id_is_gspace
           ggv_intro.one_dim_vs_ggv  helper_ggv_space_id_is_gspace2[OF assms(1)]
  by (smt (z3))
next
  show "\<And>x. x \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow> smult' 1 x = x"
 using Collect_cong assms  ggv_intro.one_dim_vs_ggv ggv_space_def
        id_apply one_dim_vector_space_with_domain_def
        vector_space_with_domain_def helper_ggv_space_id_is_gspace
      ggv_intro.one_dim_vs_ggv helper_ggv_space_id_is_gspace2[OF assms(1)]
  by (smt (z3))
next
  show "\<And>x y a.
       x \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
       y \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<Longrightarrow>
       smult' a (plus' x y) = plus' (smult' a x) (smult' a y)"
 using Collect_cong assms  ggv_intro.one_dim_vs_ggv ggv_space_def
        id_apply one_dim_vector_space_with_domain_def
        vector_space_with_domain_def helper_ggv_space_id_is_gspace
       ggv_intro.one_dim_vs_ggv  helper_ggv_space_id_is_gspace2[OF assms(1)]
  by (smt (z3))
next
  show " \<forall>y x. y \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<and>
          x \<in> {x. \<exists>a\<in>dom1. x = norm a \<or> x = - norm a} \<and> x \<noteq> plus'_zero \<longrightarrow>
          (\<exists>!r. y = smult' r x)"
 using  one_dim_vector_space_with_domain_def
        
          helper_ggv_space_id_is_gspace2[OF assms(1)]


  by (metis (no_types, lifting)
      one_dim_vector_space_with_domain_axioms_def[of
        "{uua. \<exists>uub. uub \<in> dom1 \<and> (uua = norm uub \<or> uua = - norm uub)}"
        plus'_zero smult'])
next
  show "\<forall>r. \<forall>a\<in>dom1. norm (scale r a) = smult' \<bar>r\<bar> (norm a)"
    by (metis assms(1) ggv_intro.norm_smult'_ggv ggv_space_def id_apply)
next
  show " \<forall>a\<in>dom1.
       \<forall>r. a \<noteq> gyrozero \<and> r \<noteq> 0 \<longrightarrow>
           scale \<bar>r\<bar> a /\<^sub>R norm (scale r a) = a /\<^sub>R norm a"
    by (metis assms(1) ggv_space.scale_prop1_ggv id_apply)
next
  show " \<forall>r. \<forall>u\<in>dom1. \<forall>v\<in>dom1. \<forall>a\<in>dom1. gyr u v (scale r a) = scale r (gyr u v a)"
    by (meson assms ggv_space.scale_gyr1_ggv)
next
  show " \<forall>r1 r2. \<forall>v\<in>dom1. \<forall>x\<in>dom1. gyr (scale r1 v) (scale r2 v) x = x"
    by (meson assms ggv_space.scale_gyr_id_ggv)
next
  show " \<forall>a\<in>dom1. \<forall>b\<in>dom1. norm (gyroplus a b) \<le> plus' (norm a) (norm b)"

    by (metis assms(1) ggv_space.norm_triangle_ineq_ggv id_def)
next
  show " \<forall>u\<in>dom1.
       \<forall>v\<in>dom1. \<forall>a\<in>dom1. \<forall>b\<in>dom1. inner (gyr u v a) (gyr u v b) = inner a b "
    using assms(2) by argo
qed

end