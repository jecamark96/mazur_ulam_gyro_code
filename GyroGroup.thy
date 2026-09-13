theory GyroGroup
  imports Main "HOL-Types_To_Sets.Group_On_With" "HOL-Analysis.Inner_Product" HOL.Real_Vector_Spaces 
begin

locale monoid_add_on_with = semigroup_add_on_with +
  fixes z
  assumes add_zero: "a \<in> S \<Longrightarrow> pls z a = a"
  assumes zero_mem: "z \<in> S"
begin
end



locale gyrogroupoid = 
  fixes dom::"'a set"
  fixes gyrozero :: "'a" ("0\<^sub>g")
  fixes gyroplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 100)
  assumes zero_in_dom:"gyrozero \<in> dom"
  assumes gyroplus_closed:" (a\<in> dom \<and> b\<in>dom)\<longrightarrow>  a \<oplus> b \<in> dom"
  assumes non_trivial_dom:"\<exists>a. (a\<in>dom \<and> a\<noteq>gyrozero)" (*non-trivial domain*)
begin

definition gyroaut :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "gyroaut f \<longleftrightarrow> 
       ((\<forall> a\<in>dom. \<forall>b\<in>dom. f (a \<oplus> b) = f a \<oplus> f b) \<and> 
       bij_betw f dom dom)"


(*ziroautomorfizam na domenu*)

end

locale gyrogroup =
  gyrogroupoid +
 (* fixes dom::"'a set"
  fixes gyrozero :: "'a" ("0\<^sub>g")
  fixes gyroplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 100)
  fixes gyroinv :: "'a \<Rightarrow> 'a" ("\<ominus>")
  fixes gyr :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"

 assumes "gyrogroupoid dom gyrozero gyroplus"  
  
*)
  fixes gyroinv :: "'a \<Rightarrow> 'a" ("\<ominus>")
  fixes gyr :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ax1:"a\<in>dom \<longrightarrow> gyroinv a \<in> dom"
  assumes "a\<in>dom \<and> b\<in>dom \<and> c\<in>dom \<longrightarrow> gyr a b c \<in> dom"
  assumes gyro_left_id [simp]: "\<And> a. (a\<in>dom \<longrightarrow> 0\<^sub>g \<oplus> a = a)"
  assumes gyro_left_inv [simp]: "\<And> a. (a\<in>dom \<longrightarrow> \<ominus>a \<oplus> a = 0\<^sub>g)"
  assumes gyro_left_assoc: "\<And> a b z.(a\<in>dom \<and> b\<in>dom \<and> z\<in>dom \<longrightarrow> 
a \<oplus> (b \<oplus> z) = (a \<oplus> b) \<oplus> (gyr a b z))"
  assumes gyr_left_loop: "\<And> a b. (a\<in>dom \<and> b\<in>dom \<longrightarrow> (\<forall>x\<in>dom. gyr a b x = gyr (a \<oplus> b) b x))"
  assumes gyr_gyroaut: "\<And> x y. (x\<in>dom \<and> y\<in>dom \<longrightarrow> gyroaut (gyr x y))"
begin

(*
definition gyrominus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<ominus>\<^sub>b" 100) where
  "a \<ominus>\<^sub>b b = (if (a\<in>dom \<and> b\<in>dom) then a \<oplus> (\<ominus> b) else undefined)"
*)

definition gyrominus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<ominus>\<^sub>b" 100) where
  "a \<ominus>\<^sub>b b =  a \<oplus> (\<ominus> b) "

lemma gyrominus_closed:
  shows "\<forall>a\<in>dom.\<forall>b\<in>dom. a \<ominus>\<^sub>b b  \<in> dom"
  by (simp add: ax1 gyrominus_def gyroplus_closed)

end

context gyrogroup
begin

lemma gyr_distrib [simp]:
  assumes "a\<in>dom" "b\<in>dom" "x\<in>dom" "y\<in>dom"
  shows "gyr a b (x \<oplus> y) = gyr a b x \<oplus> gyr a b y"
  using assms local.gyr_gyroaut local.gyroaut_def by blast
  
lemma gyr_inj:
  assumes "a \<in> dom" "b \<in> dom" "x\<in>dom" "y\<in>dom"
 "gyr a b x = gyr a b y"
  shows "x = y"
  using assms
  by (meson bij_betw_imp_inj_on gyr_gyroaut gyroaut_def inj_onD)
(*
  by (metis bij_betw_iff_bijections local.gyr_gyroaut local.gyroaut_def)
 *)
text \<open>Def 2.7, (2.2)\<close>
(*
definition cogyroplus (infixr "\<oplus>\<^sub>c" 100) where
  "a \<oplus>\<^sub>c b = (if (a \<in>dom \<and> b\<in>dom) then a \<oplus> (gyr a (\<ominus>b) b) else undefined)"
*)

definition cogyroplus (infixr "\<oplus>\<^sub>c" 100) where
  "a \<oplus>\<^sub>c b =  a \<oplus> (gyr a (\<ominus>b) b)"

lemma cogyroplus_closed:
  shows "\<forall>a\<in>dom.\<forall>b\<in>dom. a \<oplus>\<^sub>c b  \<in> dom"
  by (metis bij_betwE cogyroplus_def gyr_gyroaut gyroaut_def gyrogroup.ax1 gyrogroup_axioms gyroplus_closed)

(*
definition cogyrominus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<ominus>\<^sub>c\<^sub>b" 100) where
  "a \<ominus>\<^sub>c\<^sub>b b = (if a\<in>dom\<and>b\<in>dom then a \<oplus>\<^sub>c (\<ominus> b) else undefined)"
*)

definition cogyrominus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<ominus>\<^sub>c\<^sub>b" 100) where
  "a \<ominus>\<^sub>c\<^sub>b b =  a \<oplus>\<^sub>c (\<ominus> b) "

lemma cogyrominus_closed:
  shows "\<forall>a\<in>dom. \<forall>b\<in>dom. a \<ominus>\<^sub>c\<^sub>b b \<in> dom"
  by (simp add: ax1 cogyrominus_def cogyroplus_closed)

(*
definition cogyroinv ("\<ominus>\<^sub>c") where
  "\<ominus>\<^sub>c a = (if a\<in>dom then 0\<^sub>g \<ominus>\<^sub>c\<^sub>b a else undefined)"
*)

definition cogyroinv ("\<ominus>\<^sub>c") where
  "\<ominus>\<^sub>c a = 0\<^sub>g \<ominus>\<^sub>c\<^sub>b a "

lemma cogyroinv_closed:
  shows "\<forall>a\<in>dom. \<ominus>\<^sub>c a \<in> dom"
  by (simp add: cogyroinv_def cogyrominus_closed zero_in_dom)

text \<open>Thm 2.8, (1)\<close>
lemma gyro_left_cancel:
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom" "a \<oplus> b = a \<oplus> c"
  shows "b = c"
  using assms
(*  by (metis gyr_inj local.gyro_left_assoc local.gyro_left_id local.gyro_left_inv) *)
proof-
  have "\<ominus>a \<in> dom"
    using assms(1) ax1[of a]
    by blast
  from assms
  have "(\<ominus>a) \<oplus> (a \<oplus> b) = (\<ominus>a) \<oplus> (a \<oplus> c)"
    by simp
  then have "(\<ominus>a \<oplus> a) \<oplus> gyr (\<ominus>a) a b = (\<ominus>a \<oplus> a) \<oplus> gyr (\<ominus>a) a c"
    using gyro_left_assoc assms
    by (metis \<open>\<ominus> a \<in> dom\<close>)

  then have "gyr (\<ominus>a) a b = gyr (\<ominus>a) a c"
 
    by (smt (verit, del_insts) assms(1) assms(2) assms(3) gyrogroup.axioms(2) gyrogroup_axioms gyrogroup_axioms_def)
  then show "b = c"
    using gyr_inj
    by (meson \<open>\<ominus> a \<in> dom\<close> assms(1) assms(2) assms(3))
qed


text \<open>Thm 2.8, (2)\<close>

definition gyro_is_left_id where
  "gyro_is_left_id z \<longleftrightarrow> (z\<in>dom \<and> (\<forall> x\<in>dom. z \<oplus> x = x))"

lemma gyro_is_left_id_0 [simp]:
  shows "gyro_is_left_id 0\<^sub>g"
proof-
  have " 0\<^sub>g\<in>dom"
    using zero_in_dom
    by blast
  then have "(\<forall> x\<in>dom.  0\<^sub>g \<oplus> x = x)"
    using local.gyro_left_id by blast
  then show ?thesis 
    using gyro_is_left_id_def local.zero_in_dom by presburger
qed
 

lemma gyr_id_1':
  assumes "a\<in>dom"
  assumes "gyro_is_left_id z"
  shows "\<forall>x\<in>dom. (gyr z a x) = x"
  using assms
  unfolding gyro_is_left_id_def
  by (smt (verit, ccfv_threshold) bij_betwE gyro_left_cancel local.gyr_gyroaut local.gyro_left_assoc local.gyroaut_def local.gyroplus_closed)
 

lemma gyr_id_1 [simp]:
  assumes "a\<in>dom"
  shows "\<forall>x\<in>dom.(gyr 0\<^sub>g a x) = x"
  using assms gyr_id_1' gyro_is_left_id_0 by blast

text \<open>Thm 2.8, (3)\<close>

definition gyro_is_left_inv where
  "gyro_is_left_inv x a \<longleftrightarrow> (x\<in>dom \<and> a\<in>dom \<and> x \<oplus> a = 0\<^sub>g )"

definition gyro_is_right_inv where
  "gyro_is_right_inv x a \<longleftrightarrow> (x\<in>dom \<and> a\<in>dom \<and> a \<oplus> x = 0\<^sub>g)"

lemma gyro_is_left_inv [simp]:
  assumes "a\<in>dom"
  shows "gyro_is_left_inv (\<ominus>a) a"
  by (simp add: assms gyro_is_left_inv_def local.ax1)
  
lemma gyr_inv_1':
  assumes "x\<in>dom" "a\<in>dom"
  assumes "gyro_is_left_inv x a"
  shows "\<forall>y\<in>dom. (gyr x a y = y)"
  using assms gyr_left_loop[of x a]
  by (simp add: gyro_is_left_inv_def)

lemma gyr_inv_1 [simp]:
  assumes "a\<in>dom"
  shows "\<forall>x\<in>dom. gyr (\<ominus>a) a x = x"
  using gyr_left_loop[of "\<ominus>a" a]
  by (simp add: assms local.ax1)

text \<open>Thm 2.8, (4)\<close>
lemma gyr_id [simp]:
  assumes "a\<in>dom"
  shows "\<forall>x\<in>dom. gyr a a x= x"
  using assms gyr_id_1 local.gyr_left_loop local.zero_in_dom by auto
  

text \<open>Thm 2.8, (5)\<close>
lemma gyro_right_id [simp]:
  assumes "a\<in>dom"
  shows "a \<oplus> 0\<^sub>g = a"
proof-
  have "\<ominus>a \<oplus> (a \<oplus> 0\<^sub>g) = \<ominus>a \<oplus> a"
    using gyro_left_assoc
    using assms gyr_id_1 local.ax1 local.zero_in_dom by force
  thus ?thesis
    using gyro_left_cancel[of "\<ominus>a"]
    using assms local.ax1 local.gyroplus_closed local.zero_in_dom by presburger
qed

lemma gyro_inv_id [simp]: "\<ominus> 0\<^sub>g = 0\<^sub>g"
  by (metis gyro_right_id local.ax1 local.gyro_left_inv local.zero_in_dom)
  

text \<open>Thm 2.8, (6)\<close>
lemma gyro_left_id_unique:
  assumes "gyro_is_left_id z" "z\<in>dom"
  shows "z = 0\<^sub>g"
proof-
  have "0\<^sub>g = z \<oplus> 0\<^sub>g"
    using assms
    using gyro_is_left_id_def local.zero_in_dom by force
  thus ?thesis
    using gyro_right_id[of z]
    using assms(2) by argo
qed

text \<open>Thm 2.8, (7)\<close>
lemma gyro_left_inv_right_inv:
  assumes "x\<in>dom" "a\<in>dom"
  assumes "gyro_is_left_inv x a"
  shows "gyro_is_right_inv x a"
  using assms
  by (metis gyr_inv_1 gyro_is_left_inv_def gyro_is_right_inv_def gyro_right_id local.ax1 local.gyro_left_assoc local.gyro_left_id local.gyro_left_inv)
  
lemma gyro_rigth_inv [simp]:
  assumes "a\<in>dom"
  shows "a \<oplus> (\<ominus>a) = 0\<^sub>g"
  using gyro_is_right_inv_def gyro_left_inv_right_inv
  using assms gyro_is_left_inv local.ax1 by presburger

text \<open>Thm 2.8, (8)\<close>
lemma
  assumes "gyro_is_left_inv x a" "x\<in>dom" "a\<in>dom"
  shows "x = \<ominus>a"
  using assms
  using gyro_is_right_inv_def gyro_left_cancel gyro_left_inv_right_inv gyro_rigth_inv local.ax1 by presburger
 
text \<open>Thm 2.8, (9)\<close>
lemma gyro_left_cancel':
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<ominus> a \<oplus> (a \<oplus> b) = b"
  using assms(1) assms(2) local.ax1 local.gyro_left_assoc by force
  

text \<open>Thm 2.8, (10)\<close>
lemma gyr_def:
  assumes "a\<in>dom" "b\<in>dom" "x\<in>dom"
  shows "gyr a b x = \<ominus> (a \<oplus> b) \<oplus> (a \<oplus> (b \<oplus> x))"
  using  local.gyro_left_assoc local.gyro_left_cancel'
  by (smt (verit, ccfv_threshold) assms bij_betw_apply local.gyr_gyroaut local.gyroaut_def local.gyroplus_closed)

lemma gyr_def_closed:
  assumes "a\<in>dom" "b\<in>dom" "x\<in>dom"
  shows "gyr a b x \<in> dom"
  by (meson assms(1) assms(2) assms(3) bij_betw_apply gyr_gyroaut gyroaut_def)

text \<open>Thm 2.8, (11)\<close>
lemma gyr_id_3:
  assumes "a\<in>dom" "b\<in>dom"
  shows "gyr a b 0\<^sub>g = 0\<^sub>g"
  by (simp add: assms(1) assms(2) gyr_def local.gyroplus_closed local.zero_in_dom)


text \<open>Thm 2.8, (12)\<close>
lemma gyr_inv_3:
  assumes "a\<in>dom" "b\<in>dom" "x\<in>dom"
  shows "gyr a b (\<ominus>x) = \<ominus> (gyr a b x)"
proof-
  have "gyr a b (\<ominus>x) \<oplus> gyr a b x = gyr a  b (\<ominus>x \<oplus>x)"
    using assms(1) assms(2) assms(3) gyr_distrib local.ax1 by presburger
  then have "gyr a b (\<ominus>x\<oplus>x) = gyr a b 0\<^sub>g"
    using assms(3) local.gyro_left_inv by presburger
  then have " gyr a b 0\<^sub>g = 0\<^sub>g"
    using assms(1) assms(2) gyr_id_3 by blast
  then show ?thesis
    by (smt (verit, ccfv_threshold) assms(1) assms(2) assms(3) bij_betw_apply gyro_left_cancel' gyro_right_id local.ax1 local.gyr_gyroaut local.gyro_left_inv local.gyroaut_def)
qed
text \<open>Thm 2.8, (13)\<close>
lemma gyr_id_2 [simp]:
  assumes "a\<in>dom"
  shows "\<forall>x\<in>dom. (gyr a 0\<^sub>g x = x)"
  by (simp add: assms gyr_def gyro_left_cancel' local.zero_in_dom)

lemma gyr_distrib_gyrominus: 
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom" "d\<in>dom"
  shows "gyr a b (c \<ominus>\<^sub>b d) = gyr a b c \<ominus>\<^sub>b gyr a b d"
  using assms gyr_def gyr_distrib gyr_inv_3 local.ax1 local.gyrominus_def local.gyroplus_closed by force


lemma gyro_inv_idem [simp]: 
  assumes "a\<in>dom"
  shows "\<ominus> (\<ominus> a) = a"
  by (metis assms gyro_left_cancel' gyro_rigth_inv local.ax1 local.gyro_left_inv)

lemma gyr_inv_2 [simp]:
  assumes "a\<in>dom"
  shows "\<forall>x\<in>dom. (gyr a (\<ominus> a) x = x)"
  using gyr_inv_1[of "\<ominus>a"]
  by (simp add: assms local.ax1)

text \<open>(2.3.a)\<close>
lemma cogyro_left_id:
  assumes "a\<in>dom"
  shows "0\<^sub>g \<oplus>\<^sub>c a = a"
  by (simp add: assms cogyroplus_def local.ax1 local.zero_in_dom)

text \<open>(2.3.b)\<close>
lemma cogyro_rigth_id:
  assumes "a\<in>dom"
  shows "a \<oplus>\<^sub>c 0\<^sub>g = a"
  by (simp add: assms cogyroplus_def local.zero_in_dom)
  
text \<open>(2.4)\<close>
lemma cogyrominus:
  assumes "a\<in>dom" "b\<in>dom"
  shows "a \<ominus>\<^sub>c\<^sub>b b = a \<ominus>\<^sub>b gyr a b b"
  by (simp add: assms(1) assms(2) cogyrominus_def cogyroplus_def gyr_inv_3 gyrominus_def)
  
text \<open>(2.7)\<close>
lemma cogyro_right_inv:
  assumes "a\<in>dom"
  shows "a \<oplus>\<^sub>c (\<ominus>\<^sub>c a) = 0\<^sub>g"
  by (metis assms cogyro_left_id cogyroinv_def cogyrominus_def cogyroplus_def gyr_id gyro_inv_idem gyro_rigth_inv local.ax1)
text \<open>(2.6)\<close>
lemma cogyro_left_inv:
  assumes "a\<in>dom"
  shows "(\<ominus>\<^sub>c a) \<oplus>\<^sub>c a = 0\<^sub>g"
  by (simp add: assms cogyroinv_def cogyrominus_def cogyroplus_def local.ax1 local.zero_in_dom)


text \<open>(2.8)\<close>
lemma cogyro_gyro_inv: 
  assumes "a\<in>dom"
  shows "\<ominus>\<^sub>c a = \<ominus> a"
  by (simp add: assms cogyro_left_id cogyroinv_def cogyrominus_def local.ax1 local.zero_in_dom)
  
text \<open>Thm 2.9, (2.9)\<close>
lemma gyr_nested_1:
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom"
  shows "\<forall>x.(x\<in>dom \<longrightarrow> (gyr a (b \<oplus> c) \<circ> gyr b c)x = (gyr (a \<oplus> b) (gyr a b c) \<circ> gyr a b)x)" 
proof
  fix x
  show "x\<in>dom \<longrightarrow> (gyr a (b \<oplus> c) \<circ> gyr b c)x = (gyr (a \<oplus> b) (gyr a b c) \<circ> gyr a b)x"
  proof
    assume "x\<in>dom"
    show "(gyr a (b \<oplus> c) \<circ> gyr b c)x = (gyr (a \<oplus> b) (gyr a b c) \<circ> gyr a b)x"
    proof-
      have "a \<oplus> (b \<oplus> (c \<oplus> x)) = (a \<oplus> b) \<oplus> gyr a b (c \<oplus> x)"

        by (meson \<open>x \<in> dom\<close> assms(1) assms(2) assms(3) gyro_left_assoc gyroplus_closed)
        
  
        also have "... = (a \<oplus> b \<oplus> (gyr a b c \<oplus> gyr a b x))"
            by (simp add: \<open>x \<in> dom\<close> assms(1) assms(2) assms(3))
        also have "... = ((a \<oplus> b) \<oplus> gyr a b c) \<oplus> gyr (a \<oplus> b) (gyr a b c) (gyr a b x)"

          by (metis \<open>x \<in> dom\<close> assms(1) assms(2) assms(3) ax1 gyr_def gyro_left_assoc gyroplus_closed)
        also have "... = (a \<oplus> (b \<oplus> c)) \<oplus> gyr (a \<oplus> b) (gyr a b c) (gyr a b x)"
     
          by (simp add: assms(1) assms(2) assms(3) gyro_left_assoc)
  finally 
  have 1: "a \<oplus> (b \<oplus> (c \<oplus> x)) = (a \<oplus> (b \<oplus> c)) \<oplus> gyr (a \<oplus> b) (gyr a b c) (gyr a b x)"
    .

  have "a \<oplus> (b \<oplus> (c \<oplus> x)) = a \<oplus> (b \<oplus> c \<oplus> gyr b c x)"

    by (simp add: \<open>x \<in> dom\<close> assms(2) assms(3) gyro_left_assoc)
  also have "... = (a \<oplus> (b \<oplus> c)) \<oplus> gyr a (b \<oplus> c) (gyr b c x)"
  
    by (metis \<open>x \<in> dom\<close> assms(1) assms(2) assms(3) ax1 gyr_def gyro_left_assoc gyroplus_closed)

  finally have 2: "a \<oplus> (b \<oplus> (c \<oplus> x)) = (a \<oplus> (b \<oplus> c)) \<oplus> gyr a (b \<oplus> c) (gyr b c x)"
    .

  have "gyr (a \<oplus> b) (gyr a b c) (gyr a b x) = gyr a (b \<oplus> c) (gyr b c x)"
    using 1 2
    by (smt (verit, ccfv_threshold) \<open>x \<in> dom\<close> assms(1) assms(2) assms(3) gyr_def local.ax1 local.gyro_left_assoc local.gyroplus_closed)

  thus "?thesis"
    by simp
    qed
  qed
qed

text \<open>Thm 2.9, (2.15)\<close>
lemma gyr_nested_1': 
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. ((gyr (a \<oplus> b) (\<ominus> (gyr a b b)) \<circ> gyr a b)x = x)"
  by (smt (verit, ccfv_threshold) assms(1) assms(2) comp_apply gyr_id_2 gyr_inv_2 gyr_inv_3 gyr_nested_1 gyro_rigth_inv local.ax1)
  
text \<open>Thm 2.9, (2.10)\<close>
lemma gyr_nested_2: 
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. ((gyr a (\<ominus> (gyr a b b)) \<circ> gyr a b)x = x)"
proof-
  have "\<forall>x\<in>dom. (gyr (a \<oplus> b) (gyr a b (\<ominus> b)) x= gyr a (\<ominus> (gyr a b b))x)"
    using  gyr_inv_3 gyro_left_assoc gyr_left_loop gyro_right_id gyro_rigth_inv
    by (smt (verit, ccfv_threshold) assms(1) assms(2) gyr_def local.ax1 local.gyroplus_closed)
    
  thus ?thesis
    using gyr_nested_1[of a b "\<ominus> b"]
    by (smt (verit) assms(1) assms(2) bij_betw_apply comp_apply gyr_inv_3 gyr_nested_1' local.gyr_gyroaut local.gyroaut_def)
qed

text \<open>Thm 2.9, (2.11)\<close>
lemma gyr_auto_id1: 
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. ((gyr (\<ominus> a) (a \<oplus> b) \<circ> gyr a b)x = x)"
  using gyr_nested_1[of "\<ominus> a" a b]
  by (simp add: assms(1) assms(2) local.ax1)

text \<open>Thm 2.9, (2.12)\<close>
lemma gyr_auto_id2:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. ((gyr b (a \<oplus> b) \<circ> gyr a b)x = x)"
proof-
  have "\<forall>x\<in>dom. ((gyr (\<ominus>a) (a \<oplus> b)  \<circ> gyr a b)x = x)"
    using assms(1) assms(2) gyr_auto_id1 by blast
  also have "\<forall>x\<in>dom. ((gyr ((\<ominus>a)\<oplus> (a \<oplus> b)) (a \<oplus> b)  \<circ> gyr a b)x=x)"
    using gyr_left_loop 

    by (metis assms(1) assms(2) bij_betw_apply calculation comp_apply gyr_gyroaut gyroaut_def gyrogroup.ax1 gyrogroup_axioms gyroplus_closed)
  
  then show ?thesis 
    by (simp add: assms(1) assms(2) gyro_left_cancel')
qed

text \<open>Thm 2.10, (2.18)\<close>
lemma gyro_plus_def_co:
  assumes "a\<in>dom" "b\<in>dom"
  shows "a \<oplus> b = a \<oplus>\<^sub>c gyr a b b"
proof-
  have "a \<oplus>\<^sub>c gyr a b b = a\<oplus>(gyr a (\<ominus>(gyr a b b)) (gyr a b b))"
    using assms(1) assms(2) cogyroplus_def gyr_def local.ax1 local.gyroplus_closed by presburger
  then show ?thesis 
    using assms(1) assms(2) gyr_nested_2 by auto
qed

text \<open>Thm 2.11, (2.21)\<close>
lemma gyro_polygonal_addition_lemma:
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom"
  shows "(\<ominus> a \<oplus> b) \<oplus> gyr (\<ominus>a) b (\<ominus> b \<oplus> c) = \<ominus> a \<oplus> c"
proof-
  have "gyr (\<ominus>a) b (\<ominus> b \<oplus> c) = gyr (\<ominus>a) b (\<ominus> b) \<oplus> gyr (\<ominus> a) b c"
    by (simp add: assms(1) assms(2) assms(3) local.ax1)
  hence "(\<ominus> a \<oplus> b) \<oplus> gyr (\<ominus>a) b (\<ominus> b \<oplus> c) = 
        (\<ominus> a \<oplus> b) \<oplus> (gyr (\<ominus>a) b (\<ominus> b) \<oplus> gyr (\<ominus> a) b c)"
    by simp
  also have "... = ((\<ominus> a \<oplus> b) \<ominus>\<^sub>b gyr (\<ominus> a) b b) \<oplus> (gyr ((\<ominus> a) \<oplus> b) (\<ominus> (gyr (\<ominus> a) b b)) \<circ> gyr (\<ominus> a) b) c"
    using calculation gyr_inv_3 gyr_nested_1' gyro_left_cancel' gyrominus_def gyro_right_id id_apply gyro_left_assoc
    by (smt (z3) assms(1) assms(2) assms(3) ax1 comp_def gyr_inv_2 gyr_nested_1 gyroplus_closed)
    
  
  also have "... = (\<ominus> a \<oplus> (b \<ominus>\<^sub>b b)) \<oplus> c"

    by (metis assms(1) assms(2) assms(3) ax1 calculation gyro_inv_idem gyro_left_assoc gyro_left_cancel' gyro_rigth_inv gyrominus_def gyroplus_closed)
  also have "... = \<ominus> a \<oplus> c"
    by (simp add: assms(1) assms(2) local.ax1 local.gyrominus_def)

  finally
  show ?thesis
    .
qed

text \<open>Thm 2.12, (2.23)\<close>
lemma gyro_translation_1: 
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom"
  shows "\<ominus> (\<ominus>a \<oplus> b) \<oplus> (\<ominus>a \<oplus> c) = gyr (\<ominus> a) b (\<ominus>b \<oplus> c)"
  by (metis assms(1) assms(2) assms(3) gyr_def gyro_left_cancel' local.ax1 local.gyroplus_closed)

text \<open>Thm 3.13, (3.33a)\<close>
lemma gyro_translation_2a:
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom"
  shows "\<ominus> (a \<oplus> b) \<oplus> (a \<oplus> c) = gyr a b (\<ominus>b \<oplus> c)"
  by (metis assms(1) assms(2) assms(3) gyro_inv_idem gyro_translation_1 local.ax1)


definition gyro_polygonal_add ("\<oplus>\<^sub>p") where
  "\<oplus>\<^sub>p a b c = (\<ominus> a \<oplus> b) \<oplus> gyr (\<ominus> a) b (\<ominus> b \<oplus> c)"

lemma gyro_polygonal_add_closed:
  shows "\<forall>a\<in>dom. (\<forall>b\<in>dom. (\<forall>c\<in>dom. ((\<oplus>\<^sub>p a b c) \<in>dom)))" 
  using ax1 gyro_polygonal_add_def gyro_polygonal_addition_lemma gyroplus_closed by force
(* ----------------------- *)

text \<open>Thm 2.15, (2.34, 2.35)\<close>
lemma gyro_equation_right:
  assumes "a\<in>dom" "x\<in>dom" "b\<in>dom"
  shows "a \<oplus> x = b \<longleftrightarrow> x = \<ominus>a \<oplus> b"
  by (metis assms(1) assms(2) assms(3) gyro_inv_idem gyro_left_cancel' local.ax1)


lemma gyro_equation_left:
  assumes "x\<in>dom" "a\<in>dom" "b\<in>dom"
  shows "x \<oplus> a = b \<longleftrightarrow> x = b \<ominus>\<^sub>c\<^sub>b a"
proof
  show "x \<oplus> a = b \<Longrightarrow> x = b \<ominus>\<^sub>c\<^sub>b a"
    by (metis assms(1) assms(2) assms(3) ax1 cogyrominus gyr_inv_3 gyr_left_loop gyro_inv_idem gyro_left_assoc gyro_left_inv gyro_right_id gyrominus_def)
next
  show " x = b \<ominus>\<^sub>c\<^sub>b a \<Longrightarrow> x \<oplus> a = b"
  proof-
    assume "x = b \<ominus>\<^sub>c\<^sub>b a"
    show " x \<oplus> a = b"
    proof-
      have "x \<oplus> a =  (b \<ominus>\<^sub>c\<^sub>b a) \<oplus> a"
        using \<open>x = b \<ominus>\<^sub>c\<^sub>b a\<close> by blast
      also  have "... = (b  \<oplus> (\<ominus> (gyr b a a)))  \<oplus> a"
        by (simp add: assms(2) assms(3) cogyrominus gyrominus_def)
      also have " ... = (b  \<oplus> (\<ominus> (gyr b a a)))  \<oplus> (gyr b (\<ominus> (gyr b a a)) (gyr b a a))"
        using assms(2) assms(3) gyr_nested_2 by auto
      also have "... = b \<oplus> (\<ominus> (gyr b a a) \<oplus> (gyr b a a))"
        using assms(2) assms(3) ax1 gyr_def gyro_left_assoc gyroplus_closed by presburger
      finally show ?thesis 
        by (smt (verit, del_insts) assms(2) assms(3) gyro_right_id gyrogroup.axioms(2) gyrogroup_axioms gyrogroup_axioms_def)
    qed
  qed
qed

lemma oplus_ominus_cancel [simp]:
  assumes "y\<in>dom" "x\<in>dom"
  shows "y = x \<oplus> (\<ominus> x \<oplus> y)"
  by (metis assms(1) assms(2) gyro_equation_right local.ax1 local.gyroplus_closed)
  
text \<open>(2.39)\<close>
lemma cogyro_right_cancel':
  assumes "b\<in>dom" "a\<in>dom"
  shows "(b \<ominus>\<^sub>c\<^sub>b a) \<oplus> a = b"
  using assms(1) assms(2) cogyrominus gyr_def gyro_equation_left local.ax1 local.gyrominus_def local.gyroplus_closed by presburger
text \<open>(2.40)\<close>
lemma gyro_right_cancel'_dual:
  assumes "b\<in>dom" "a\<in>dom"
  shows "(b \<ominus>\<^sub>b a) \<oplus>\<^sub>c a = b"
  by (metis assms(1) assms(2) ax1 cogyrominus_def gyro_equation_left gyro_inv_idem gyrominus_def gyroplus_closed)


(* ----------------------- *)

text \<open>Thm 2.19 (2.48)\<close>
lemma gyroaut_gyr_commute_lemma:
  assumes "gyroaut A" "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. (A \<circ> gyr a b)x = (gyr (A a) (A b) \<circ> A)x" 
proof
  fix x
  assume "x\<in>dom"
  show " (A \<circ> gyr a b)x = (gyr (A a) (A b) \<circ> A)x"
  proof-
  have "(A a \<oplus> A b) \<oplus> (A \<circ> gyr a b) x = A((a \<oplus> b) \<oplus> gyr a b x)"
    using assms gyroaut_def
    by (simp add: \<open>x \<in> dom\<close> gyr_def local.ax1 local.gyroplus_closed)
  also have "... = A (a \<oplus> (b \<oplus> x))"
  
    by (simp add: \<open>x \<in> dom\<close> assms(2) assms(3) gyro_left_assoc)
   
  also have "... = A a \<oplus> (A b \<oplus> A x)"
    using assms gyroaut_def
    using \<open>x \<in>dom\<close> local.gyroplus_closed by force
  also have "... = (A a \<oplus> A b) \<oplus> (gyr (A a) (A b) (A x))"

    by (meson \<open>x \<in> dom\<close> assms(1) assms(2) assms(3) bij_betwE gyro_left_assoc gyroaut_def)
  finally
  show "?thesis"
    using gyro_left_cancel
      by (smt (verit, del_insts) \<open>x \<in> dom\<close> assms(1) assms(2) assms(3) bij_betwE comp_def local.gyr_gyroaut local.gyroaut_def local.gyroplus_closed)

qed
qed


  text \<open>Thm 2.20\<close>
lemma gyroaut_gyr_commute: 
  assumes "gyroaut A" "a\<in>dom" "b\<in>dom"
  shows "((\<forall>x\<in>dom. (gyr a b x = gyr (A a) (A b) x)) \<longleftrightarrow> (\<forall>y\<in>dom. ((A \<circ> gyr a b)y = (gyr a b \<circ> A)y)))"
proof
  show " \<forall>x\<in>dom. gyr a b x = gyr (A a) (A b) x \<Longrightarrow>
    \<forall>y\<in>dom. (A \<circ> gyr a b) y = (gyr a b \<circ> A) y"
    by (metis assms(1) assms(2) assms(3) bij_betwE comp_apply gyroaut_def gyroaut_gyr_commute_lemma)
next
  show "\<forall>y\<in>dom. (A \<circ> gyr a b) y = (gyr a b \<circ> A) y \<Longrightarrow>
    \<forall>x\<in>dom. gyr a b x = gyr (A a) (A b) x"
  proof-
    assume "\<forall>y\<in>dom. (A \<circ> gyr a b) y = (gyr a b \<circ> A) y"
    show "  \<forall>x\<in>dom. gyr a b x = gyr (A a) (A b) x"
    proof
      fix x
      assume "x\<in>dom"
      show " gyr a b x = gyr (A a) (A b) x"
      proof-
        have "(A \<circ> gyr a b)x = (gyr  (A a) (A b) \<circ> A)x"
          using \<open>x \<in> dom\<close> assms(1) assms(2) assms(3) gyroaut_gyr_commute_lemma by blast
        moreover have "(A \<circ> gyr a b)x =  (gyr a b \<circ> A) x"
          using \<open>\<forall>y\<in>dom. (A \<circ> gyr a b) y = (gyr a b \<circ> A) y\<close> \<open>x \<in> dom\<close> by blast
        moreover have "((gyr a b \<circ> A)  \<circ> (inv_into dom A)) x =  (gyr  (A a) (A b) \<circ> A  \<circ> (inv_into dom A))x"
          by (metis \<open>\<forall>y\<in>dom. (A \<circ> gyr a b) y = (gyr a b \<circ> A) y\<close> \<open>x \<in> dom\<close> assms(1) assms(2) assms(3) bij_betwE bij_betw_inv_into comp_apply gyroaut_def gyroaut_gyr_commute_lemma)
        ultimately show ?thesis 
          by (metis \<open>x \<in> dom\<close> assms(1) bij_betw_def comp_apply f_inv_into_f gyroaut_def)
      qed
    qed
  qed
qed

 

text \<open>2.50\<close>
lemma gyr_commute_misc_1:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. (gyr (gyr a b a) (gyr a b b) x = gyr a b x)"
  by (metis assms(1) assms(2) gyroaut_gyr_commute local.gyr_gyroaut)


text \<open>Thm 2.21 (2.52)\<close>
definition
  "cogyroaut f \<longleftrightarrow> (\<forall>a b. (a\<in>dom \<and> b\<in>dom \<longrightarrow> f (a \<oplus>\<^sub>c b) = f a \<oplus>\<^sub>c f b) 
    \<and> bij_betw f dom dom)"


interpretation  semigroup_add_on_with "{f::'a\<Rightarrow>'a. gyroaut f}" "\<lambda>f1 f2. f1\<circ>f2"
proof
  show " \<And>a b c.
       a \<in> Collect gyroaut \<Longrightarrow>
       b \<in> Collect gyroaut \<Longrightarrow> c \<in> Collect gyroaut \<Longrightarrow> a \<circ> b \<circ> c = a \<circ> (b \<circ> c)"
    using comp_assoc by blast
next
  show "\<And>a b. a \<in> Collect gyroaut \<Longrightarrow>
           b \<in> Collect gyroaut \<Longrightarrow> a \<circ> b \<in> Collect gyroaut"
  proof
    fix a b
    assume "a\<in>Collect gyroaut"
    show "b \<in> Collect gyroaut \<Longrightarrow> gyroaut (a \<circ> b) "
    proof-
      assume "b \<in> Collect gyroaut"
      show "gyroaut (a \<circ> b)"
        by (smt (verit) \<open>a \<in> Collect gyroaut\<close> \<open>b \<in> Collect gyroaut\<close> bij_betwE bij_betw_trans comp_def gyroaut_def mem_Collect_eq)
    qed
  qed
qed
interpretation  monoid_add_on_with "{f::'a\<Rightarrow>'a. gyroaut f}" "\<lambda>f1 f2. f1\<circ>f2" "id"
proof
  show "\<And>a. a \<in> Collect gyroaut \<Longrightarrow> id \<circ> a = a"
  proof
    fix a x
    assume " a \<in> Collect gyroaut"
    show "(id \<circ> a) x = a x"
      using gyroaut_def
      by auto
  qed
next
  show " id \<in> Collect gyroaut"
    by (simp add: gyroaut_def)
qed

lemma cogyroaut_zero:
  assumes "cogyroaut f"
  shows "f gyrozero = gyrozero"
proof-
  have "0\<^sub>g \<oplus> f 0\<^sub>g = f 0\<^sub>g"
    by (meson assms bij_betw_apply cogyroaut_def gyro_left_id zero_in_dom)
  also have "... = f (0\<^sub>g \<oplus>\<^sub>c 0\<^sub>g)"
    using cogyro_left_id zero_in_dom by auto
  also have "... = (f 0\<^sub>g) \<oplus>\<^sub>c (f 0\<^sub>g)"
    using assms cogyroaut_def zero_in_dom by blast
  also have "... =  (f 0\<^sub>g) \<oplus> (f 0\<^sub>g) "
    by (metis assms bij_betw_apply cogyroaut_def gyr_id gyro_plus_def_co zero_in_dom)
  finally show ?thesis
    by (metis \<open>0\<^sub>g \<oplus> f 0\<^sub>g = f 0\<^sub>g\<close> assms bij_betw_apply cogyroaut_def gyro_left_cancel gyro_right_id zero_in_dom)
qed

lemma gyrozero_co_neutral:
  assumes "a\<in>dom"
  shows "(\<ominus>a) \<oplus>\<^sub>c a = gyrozero"
  using assms cogyro_gyro_inv cogyro_left_inv by presburger

lemma cogyro_inv_unique:
  assumes "a\<in>dom" "b\<in>dom"
  "a\<oplus>\<^sub>c b = gyrozero"
shows "b=\<ominus>a"
  using assms(1) assms(2) assms(3) cogyroplus_def gyr_def_closed gyr_left_loop gyro_inv_id gyro_inv_idem gyro_left_id gyro_polygonal_addition_lemma gyro_rigth_inv gyrogroup.ax1 gyrogroup_axioms gyroplus_closed oplus_ominus_cancel
  by (smt (z3) ax1 gyr_inv_3 gyro_plus_def_co)


lemma cogyroaut_inv:
  assumes "cogyroaut f" "a\<in>dom"
  shows "f (\<ominus>\<^sub>c a) = \<ominus>\<^sub>c (f a)"
proof-
  have "0\<^sub>g = f 0\<^sub>g "
    by (simp add: assms(1) cogyroaut_zero)
  moreover have "f gyrozero = f (a \<ominus>\<^sub>c\<^sub>b a)"
    using assms(2) gyro_equation_left gyro_left_id zero_in_dom by blast
  moreover have " f (a \<ominus>\<^sub>c\<^sub>b a) = f (a\<oplus>\<^sub>c (\<ominus>\<^sub>c a))"
    by (simp add: \<open>f 0\<^sub>g = f (a \<ominus>\<^sub>c\<^sub>b a)\<close> assms(2) cogyro_right_inv)
  moreover have "f (a\<oplus>\<^sub>c (\<ominus>\<^sub>c a)) = (f a) \<oplus>\<^sub>c (f (\<ominus>\<^sub>c a))"
    using assms(1) assms(2) cogyroinv_closed gyrogroup.cogyroaut_def gyrogroup_axioms by fastforce
  moreover have *:"0\<^sub>g = (f a) \<oplus>\<^sub>c (f (\<ominus>\<^sub>c a))"
    using calculation(1) calculation(2) calculation(3) calculation(4) by argo
  ultimately show ?thesis
    by (metis assms(1) assms(2) bij_betw_apply cogyro_gyro_inv cogyro_inv_unique cogyroinv_closed gyrogroup.cogyroaut_def gyrogroup_axioms)
qed


lemma cogyroaut_minus:
  assumes "cogyroaut f" "a\<in>dom" "b\<in>dom"
  shows "f (a \<ominus>\<^sub>c\<^sub>b b) = (f a) \<ominus>\<^sub>c\<^sub>b (f b)"
  by (smt (verit, best) assms(1) assms(2) assms(3) bij_betwE cogyroaut_def cogyrominus_def gyro_is_left_inv gyro_is_left_inv_def gyrogroup.cogyro_gyro_inv gyrogroup.cogyroaut_inv gyrogroup_axioms)

lemma gyro_coaut_iff_gyro_aut:
  shows "gyroaut f \<longleftrightarrow> cogyroaut f"
proof
  show " gyroaut f \<Longrightarrow> cogyroaut f"
  proof-
  assume *:"gyroaut f"
  thus "cogyroaut f"
  proof-
    have " (\<forall>a b. (a \<in> dom \<and> b \<in> dom \<longrightarrow> f (a \<oplus>\<^sub>c b) = f a \<oplus>\<^sub>c f b))"
    proof
      fix a
      show " \<forall>b. a \<in> dom \<and> b \<in> dom \<longrightarrow> f (a \<oplus>\<^sub>c b) = f a \<oplus>\<^sub>c f b"
      proof
        fix b
        show "a \<in> dom \<and> b \<in> dom \<longrightarrow> f (a \<oplus>\<^sub>c b) = f a \<oplus>\<^sub>c f b"
        proof
          assume "a\<in>dom \<and> b\<in>dom"
          show "f (a \<oplus>\<^sub>c b) = f a \<oplus>\<^sub>c f b"
          proof-
            have "f (a \<oplus>\<^sub>c b) = f (a \<oplus> gyr a (\<ominus>b) b)"
              using cogyroplus_def by force
            also have "... = f a \<oplus> f (gyr a (\<ominus>b) b)"
              by (metis "*" \<open>a \<in> dom \<and> b \<in> dom\<close> ax1 bij_betw_iff_bijections gyr_gyroaut gyroaut_def)
            also have "... = f a \<oplus> (gyr (f a)   (f (\<ominus>b)) (f b))"
              using "*" \<open>a \<in> dom \<and> b \<in> dom\<close> ax1 gyroaut_gyr_commute_lemma by auto
            finally show ?thesis 
            proof-
              have "f (\<ominus>b \<oplus> b) = f(\<ominus>b) \<oplus> (f b)"
                by (meson "*" \<open>a \<in> dom \<and> b \<in> dom\<close> gyroaut_def gyrogroup.ax1 gyrogroup_axioms)
              moreover have "f(\<ominus>b) = \<ominus> (f b)"
                using "*" \<open>a \<in> dom \<and> b \<in> dom\<close> gyroaut_def[of f] bij_betw_apply calculation gyro_left_cancel' gyro_right_id gyrogroup.ax1 gyrogroup_axioms zero_in_dom
                by (metis gyro_left_inv)
                ultimately show ?thesis
                using \<open>f (a \<oplus> gyr a (\<ominus> b) b) = f a \<oplus> f (gyr a (\<ominus> b) b)\<close> \<open>f a \<oplus> f (gyr a (\<ominus> b) b) = f a \<oplus> gyr (f a) (f (\<ominus> b)) (f b)\<close> cogyroplus_def by presburger
            qed

          qed
        qed
      qed
    qed
    then show ?thesis 
      using "*" cogyroaut_def gyroaut_def by blast
  qed
qed
next
  show "cogyroaut f \<Longrightarrow> gyroaut f"
  proof-
  assume "cogyroaut f"
  thus  "gyroaut f"
  proof-
    have "(\<forall>a\<in>dom. \<forall>b\<in>dom. f (a \<oplus> b) = f a \<oplus> f b)"
    proof
      fix a
      assume "a\<in>dom"
      show " \<forall>b\<in>dom. f (a \<oplus> b) = f a \<oplus> f b"
      proof
        fix b
        assume *:"b\<in>dom"
        show " f (a \<oplus> b) = f a \<oplus> f b"
        proof-
          have "f a = f ((a\<oplus>b)\<ominus>\<^sub>c\<^sub>b b)"
            by (metis "*" \<open>a \<in> dom\<close> gyro_equation_left gyroplus_closed)
          moreover have " f ((a\<oplus>b)\<ominus>\<^sub>c\<^sub>b b) = (f (a\<oplus>b)) \<ominus>\<^sub>c\<^sub>b (f b)"
            by (simp add: "*" \<open>a \<in> dom\<close> \<open>cogyroaut f\<close> cogyroaut_minus gyroplus_closed)
          moreover have "f a =  (f (a\<oplus>b)) \<ominus>\<^sub>c\<^sub>b (f b)"
            by (simp add: calculation(1) calculation(2))
          ultimately show ?thesis 
            by (metis "*" \<open>a \<in> dom\<close> \<open>cogyroaut f\<close> bij_betw_apply cogyro_right_cancel' cogyroaut_def gyroplus_closed)
        qed
      qed
    qed
    then show ?thesis 
      using \<open>cogyroaut f\<close> cogyroaut_def gyroaut_def by blast
  qed
qed
qed
    

(* ----------------------- *)

text \<open>Thm 2.25, (2.76)\<close>
lemma gyroplus_inv:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<ominus> (a \<oplus> b) = gyr a b (\<ominus> b \<ominus>\<^sub>b a)"
  using  gyr_def[OF assms] gyro_equation_right[OF assms]
    gyrominus_def gyro_rigth_inv[OF assms(1)]
  by (metis assms(1) assms(2) gyro_right_id gyro_translation_2a local.ax1 local.gyroplus_closed)
 

lemma inv_gyr_help:
  assumes "a\<in>dom" "b\<in>dom"
  shows "((inv_into dom) (gyr a b) (\<ominus> (a\<oplus>b))) = gyr (\<ominus>b) (\<ominus>a) (\<ominus> (a\<oplus>b) ) "
proof-
have "\<ominus> (a \<oplus> b) = gyr a b (\<ominus> b \<ominus>\<^sub>b a)"
       using gyroplus_inv[OF assms]
       by blast
    moreover have "\<ominus>b \<ominus>\<^sub>b a =((inv_into dom) (gyr a b) (\<ominus> (a\<oplus>b)))"
      by (metis assms(1) assms(2) ax1 bij_betw_inv_into_left calculation gyr_gyroaut gyroaut_def gyrominus_closed)
    moreover have "(inv_into dom) (gyr a b) (\<ominus> (a\<oplus>b)) = gyr (\<ominus>b) (\<ominus>a) (\<ominus> (a\<oplus>b))"
      by (smt (verit) assms(1) assms(2) ax1 calculation(2) gyr_inv_3 gyro_inv_idem gyrominus_def gyroplus_closed gyroplus_inv)
    moreover have "\<ominus>b \<ominus>\<^sub>b a =  gyr (\<ominus>b) (\<ominus>a) (\<ominus> (a\<oplus>b))"
      by (simp add: calculation(2) calculation(3))
    ultimately show ?thesis 
      by meson
  qed


definition gyrosem_dom::"('a\<times> ('a\<Rightarrow>'a)) set" where
  "gyrosem_dom = {(x, X). x\<in>dom \<and> gyroaut X  \<and> (\<forall>y. (\<not>y\<in>dom \<longrightarrow> X y = undefined))}"

(*(x, X)(y, Y ) = (x + Xy, gyr[x, Xy]XY )*)
definition gyrosem_op::"('a\<times> ('a\<Rightarrow>'a)) => ('a\<times> ('a\<Rightarrow>'a)) => ('a\<times> ('a\<Rightarrow>'a))" where
  "gyrosem_op X Y = (if X\<in> gyrosem_dom \<and> Y \<in> gyrosem_dom then (fst X \<oplus> (snd X) (fst Y),
 (\<lambda>t. (if t\<in>dom then (gyr (fst X) ((snd X)(fst Y)) \<circ> (snd X) \<circ> (snd Y)) t else undefined)
)) else undefined)"

lemma zero_id_in_gyrosem_dom:
  shows "(gyrozero, \<lambda>y. if y \<in> dom then y else undefined) \<in> gyrosem_dom"
proof-
  have "gyroaut (\<lambda>y. if y \<in> dom then y else undefined)"
  proof-
    have "bij_betw (\<lambda>y. if y \<in> dom then y else undefined) dom dom"
      using bij_betw_iff_bijections by fastforce
    moreover have "\<forall>a\<in>dom. \<forall>b\<in>dom. (\<lambda>y. if y \<in> dom then y else undefined) (a\<oplus>b) =
  (\<lambda>y. if y \<in> dom then y else undefined)a \<oplus>(\<lambda>y. if y \<in> dom then y else undefined)b"
      by (simp add: gyroplus_closed)
    ultimately show ?thesis 
      using gyroaut_def by blast
  qed
  then show ?thesis
    by (simp add: gyrosem_dom_def zero_in_dom)
qed

lemma gyroaut_closed:
  assumes "gyroaut A" "x\<in>dom"
  shows "A x \<in> dom"
  using assms(1) assms(2) bij_betwE gyroaut_def by blast

lemma neutral_gyrosemi:
  assumes "(a,A) \<in>  gyrosem_dom"
  shows "gyrosem_op  (gyrozero,  \<lambda>y. if y \<in> dom then y else undefined) (a,A) = (a,A)"
proof
  show " fst (gyrosem_op (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined) (a, A)) =
    fst (a, A)"
    using assms gyrosem_dom_def gyrosem_op_def zero_id_in_gyrosem_dom by auto
next
  show " snd (gyrosem_op (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined) (a, A)) =
    snd (a, A)"
  proof
    fix x
    show "snd (gyrosem_op  (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined) (a, A)) x =
         snd (a, A) x"
    proof-
      have "x\<in>dom\<or> \<not>x\<in>dom"
        by blast
      moreover {
        assume "\<not>x\<in>dom"
        then have ?thesis 
          using assms gyrosem_dom_def gyrosem_op_def zero_id_in_gyrosem_dom by auto
      }
      moreover {
        assume "x\<in>dom"
        then have "snd (gyrosem_op (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined) (a, A)) x = ( \<lambda>t. if t \<in> dom
                    then (gyr (fst (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined))
                           (snd (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)
                             (fst (a, A))) \<circ>
                          snd (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined) \<circ>
                          snd (a, A))
                          t
                    else undefined) x"

          unfolding gyrosem_op_def
          using assms zero_id_in_gyrosem_dom by fastforce
        moreover have "  ( \<lambda>t. if t \<in> dom then (gyr (fst (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined))
                           (snd (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)
                             (fst (a, A))) \<circ>
                          snd (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined) \<circ>
                          snd (a, A))
                          t
                    else undefined) x = ((gyr gyrozero ((\<lambda>y. if y \<in> dom then y else undefined) a))\<circ> (\<lambda>y. if y \<in> dom then y else undefined) \<circ> A) x"
          using \<open>x \<in> dom\<close> by fastforce
        moreover have "((gyr gyrozero ((\<lambda>y. if y \<in> dom then y else undefined) a))\<circ> (\<lambda>y. if y \<in> dom then y else undefined) \<circ> A)  x = 
 A x"
        proof-
          have "((gyr gyrozero ((\<lambda>y. if y \<in> dom then y else undefined) a))\<circ> (\<lambda>y. if y \<in> dom then y else undefined) \<circ> A)  x
    = ((gyr gyrozero ((\<lambda>y. if y \<in> dom then y else undefined) a))\<circ> (\<lambda>y. if y \<in> dom then y else undefined)) (A x)"
            by fastforce
          moreover have "A x \<in> dom"
          proof-
            have "gyroaut A"
              using assms gyrosem_dom_def by auto
            then show ?thesis
              using \<open>x \<in> dom\<close> assms gyroaut_closed by auto
          qed
          moreover have "((gyr gyrozero ((\<lambda>y. if y \<in> dom then y else undefined) a))\<circ> (\<lambda>y. if y \<in> dom then y else undefined)) (A x) = ((gyr gyrozero ((\<lambda>y. if y \<in> dom then y else undefined) a))) (A x)"
            using calculation(2) by force
          ultimately show ?thesis
            using assms gyrosem_dom_def by auto
          
        qed
        ultimately have ?thesis 
          by force
      }
      ultimately show ?thesis 
        by blast
  qed
qed
qed



lemma gyroaut_inv:
  assumes "gyroaut A"
  shows "gyroaut (inv_into dom A)"
proof-
  have "\<forall>a\<in>dom. \<forall>b\<in>dom. (inv_into dom A) (a\<oplus>b) = (inv_into dom A)a\<oplus>(inv_into dom A) b"
  proof
    fix a
    assume "a\<in>dom"
    show "\<forall>b\<in>dom. inv_into dom A (a \<oplus> b) = inv_into dom A a \<oplus> inv_into dom A b"
    proof
      fix b
      assume "b\<in>dom"
     show " inv_into dom A (a \<oplus> b) = inv_into dom A a \<oplus> inv_into dom A b"
     proof-
       obtain "x1" where "x1\<in>dom \<and> A x1 = a"
         by (metis \<open>a \<in> dom\<close> assms bij_betw_iff_bijections gyroaut_def)
       moreover obtain "x2" where "x2\<in>dom \<and> A x2 = b"
         by (metis \<open>b \<in> dom\<close> assms bij_betw_iff_bijections gyroaut_def)
       moreover have "inv_into dom A (a \<oplus> b) = inv_into dom A (A x1 \<oplus> A x2)"
         using calculation(1) calculation(2) by force
       moreover have " inv_into dom A (A x1 \<oplus> A x2) =  inv_into dom A (A (x1 \<oplus>  x2))"
         using assms calculation(1) calculation(2) gyroaut_def by auto
       moreover have " inv_into dom A (A (x1 \<oplus>  x2)) = x1 \<oplus> x2"
         by (meson assms bij_betw_inv_into_left calculation(1) calculation(2) gyroaut_def gyroplus_closed)
       ultimately show ?thesis
         by (metis assms bij_betw_inv_into_left gyroaut_def)
     qed
   qed
 qed
  then show ?thesis
    using \<open>\<forall>a\<in>dom. \<forall>b\<in>dom. inv_into dom A (a \<oplus> b) = inv_into dom A a \<oplus> inv_into dom A b\<close> assms bij_betw_inv_into gyroaut_def by blast
qed

lemma inv_in_gyrosemi:
  assumes "(a,A)\<in>gyrosem_dom"
  shows " (\<ominus> (if a \<in> dom then inv_into dom A a else undefined),
   \<lambda>x. if x \<in> dom then inv_into dom A x else undefined) \<in> gyrosem_dom"
 using gyrosem_dom_def
  proof-
    have "(\<ominus> (if a \<in> dom then inv_into dom A a else undefined))\<in>dom"
      by (smt (verit, best) assms ax1 bij_betw_iff_bijections bij_betw_inv_into gyroaut_def gyrosem_dom_def mem_Collect_eq old.prod.case)
    moreover have "gyroaut  (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined)"
    proof-
      have "gyroaut (inv_into dom A)"
        using assms gyroaut_inv gyrosem_dom_def by auto
      moreover have "bij_betw  (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined) dom dom"
        by (smt (verit, del_insts) bij_betw_cong calculation gyroaut_def)
      moreover have "\<forall>a\<in>dom.\<forall>b\<in>dom. ( (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined)(a\<oplus>b) =  (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined)a \<oplus>  (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined)b)"
        using calculation(1) gyroaut_def gyroplus_closed by auto
      ultimately show ?thesis 
        using gyroaut_def by blast
    qed
    moreover have "\<forall>y. \<not>y\<in>dom \<longrightarrow> ( \<lambda>x. if x \<in> dom then inv_into dom A x else undefined) y = undefined"
      by presburger
    ultimately show ?thesis
      using gyrosem_dom_def by blast
  qed

lemma inv_gyrosemi:
  assumes "(a,A) \<in>  gyrosem_dom" 
  shows "gyrosem_op (\<ominus> ((\<lambda>x. if x\<in>dom then (inv_into dom A) x else undefined) a), (\<lambda>x. if x\<in>dom then (inv_into dom A) x else undefined)) (a,A) = (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)"
proof-
  have "(\<ominus> (if a \<in> dom then inv_into dom A a else undefined),
             \<lambda>x. if x \<in> dom then inv_into dom A x else undefined)
            \<in> gyrosem_dom"
    using assms inv_in_gyrosemi by blast
  moreover have  "fst (gyrosem_op
          (\<ominus> (if a \<in> dom then inv_into dom A a else undefined),
           \<lambda>x. if x \<in> dom then inv_into dom A x else undefined)
          (a, A)) =
    fst (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)"
    using assms calculation gyroaut_closed gyrosem_dom_def gyrosem_op_def by fastforce
 moreover have  "snd (gyrosem_op
          (\<ominus> (if a \<in> dom then inv_into dom A a else undefined),
           \<lambda>x. if x \<in> dom then inv_into dom A x else undefined)
          (a, A)) =
    snd (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)"
 proof-
   have "snd (gyrosem_op
          (\<ominus> (if a \<in> dom then inv_into dom A a else undefined),
           \<lambda>x. if x \<in> dom then inv_into dom A x else undefined)
          (a, A)) =( \<lambda>t. (if t \<in> dom then ((gyr (\<ominus> (if a \<in> dom then inv_into dom A a else undefined)) 
                    (( \<lambda>x. if x \<in> dom then inv_into dom A x
                                      else undefined) a)) \<circ> (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined)\<circ> A)t else undefined))"
     
   proof-
     have "(\<lambda>t. if t \<in> dom
                    then (gyr (fst (\<ominus> (if a \<in> dom then inv_into dom A a
                                        else undefined),
                                    \<lambda>x. if x \<in> dom then inv_into dom A x
else undefined))
                           (snd (\<ominus> (if a \<in> dom then inv_into dom A a
                                     else undefined),
                                 \<lambda>x. if x \<in> dom then inv_into dom A x
                                      else undefined)
                             (fst (a, A))) \<circ>
                          snd (\<ominus> (if a \<in> dom then inv_into dom A a
                                   else undefined),
                               \<lambda>x. if x \<in> dom then inv_into dom A x
                                    else undefined) \<circ>
                          snd (a, A))
                          t
                    else undefined) =( \<lambda>t. (if t \<in> dom then ((gyr (\<ominus> (if a \<in> dom then inv_into dom A a else undefined)) 
                    (( \<lambda>x. if x \<in> dom then inv_into dom A x
                                      else undefined) a)) \<circ> (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined)\<circ> A)t else undefined))"
       by auto
     then show ?thesis unfolding gyrosem_op_def
       using assms calculation(1) by fastforce
   qed
   moreover have "( \<lambda>t. (if t \<in> dom then ((gyr (\<ominus> (if a \<in> dom then inv_into dom A a else undefined)) 
                    (( \<lambda>x. if x \<in> dom then inv_into dom A x
                                      else undefined) a)) \<circ> (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined)\<circ> A)t else undefined)) =  (\<lambda>y. if y \<in> dom then y else undefined)"
   proof
     fix t
     show "(if t \<in> dom
          then (gyr (\<ominus> (if a \<in> dom then inv_into dom A a else undefined))
                 (if a \<in> dom then inv_into dom A a else undefined) \<circ>
                (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined) \<circ>
                A)
                t
          else undefined) =
         (if t \<in> dom then t else undefined)"
     proof-
       have "t\<in>dom\<or>\<not>t\<in>dom" by blast
       moreover {
         assume "\<not>t\<in>dom"
         then have ?thesis 
           by force
       }
       moreover {
         assume "t\<in>dom"
         then have "(if t \<in> dom
          then (gyr (\<ominus> (if a \<in> dom then inv_into dom A a else undefined))
                 (if a \<in> dom then inv_into dom A a else undefined) \<circ>
                (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined) \<circ>
                A)
                t
          else undefined) = (gyr (\<ominus> (if a \<in> dom then inv_into dom A a else undefined))
                 (if a \<in> dom then inv_into dom A a else undefined) \<circ>
                (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined) \<circ>
                A)
                t"
           by presburger
         then have " (gyr (\<ominus> (if a \<in> dom then inv_into dom A a else undefined))
                 (if a \<in> dom then inv_into dom A a else undefined) \<circ>
                (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined) \<circ>
                A)
                t = (gyr (\<ominus> ( inv_into dom A a))
     ( inv_into dom A a)  (inv_into dom A (A t)))"
           using \<open>t \<in> dom\<close> assms gyroaut_closed gyrosem_dom_def by force
         then have "(gyr (\<ominus> ( inv_into dom A a))
     ( inv_into dom A a)  (inv_into dom A (A t))) = t"
           by (metis (no_types, lifting) Product_Type.Collect_case_prodD \<open>t \<in> dom\<close> assms bij_betwE bij_betw_inv_into bij_betw_inv_into_left fst_conv gyr_inv_1 gyroaut_def gyrosem_dom_def snd_conv)
         then have ?thesis
           using \<open>(gyr (\<ominus> (if a \<in> dom then inv_into dom A a else undefined)) (if a \<in> dom then inv_into dom A a else undefined) \<circ> (\<lambda>x. if x \<in> dom then inv_into dom A x else undefined) \<circ> A) t = gyr (\<ominus> (inv_into dom A a)) (inv_into dom A a) (inv_into dom A (A t))\<close> by argo
       }
       ultimately show ?thesis 
         by fastforce
     qed
   qed
   ultimately show ?thesis 
     by simp
 qed
  ultimately show ?thesis 
    using prod_eqI by blast
qed

lemma gyroaut_gyro:
  assumes "x\<in>dom" "y\<in>dom" "z\<in>dom"
      "gyroaut A"
    shows "(A\<circ> (gyr x y)) z = gyr (A x) (A y) (A z)"
  using assms(1) assms(2) assms(3) assms(4) gyroaut_gyr_commute_lemma by auto


lemma assoc_help1:
  assumes "(b,B)\<in> gyrosem_dom"
          "(c,C)\<in> gyrosem_dom"
  shows "(b\<oplus>B c,   (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined))\<in> gyrosem_dom"
   
proof-
  have "b\<oplus>B c\<in>dom" 
    using assms(1) assms(2) gyroaut_closed gyroplus_closed gyrosem_dom_def by auto
  moreover have "gyroaut (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined)"
  proof-
    have "gyroaut  (gyr b (B c) \<circ> B\<circ>C)"
      using add_mem assms(1) assms(2) gyr_gyroaut gyroaut_closed gyrosem_dom_def by force
    moreover have "bij_betw (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined) dom dom"
    proof-
      have "inj_on (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined) dom"
        by (smt (verit, best) bij_betw_def calculation gyroaut_def inj_on_def)
      moreover have " (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined) ` dom = dom"
      proof
        show "(\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B \<circ> C) t else undefined) ` dom \<subseteq> dom"
          using \<open>gyroaut (gyr b (B c) \<circ> B \<circ> C)\<close> gyroaut_closed by fastforce
      next
        show "dom \<subseteq> (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B \<circ> C) t else undefined) ` dom "
        proof
          fix x
          assume "x\<in>dom"
          show "x \<in> (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B \<circ> C) t else undefined) ` dom "
          proof-
          obtain "t" where "t\<in>dom \<and> x = (gyr b (B c) \<circ> B \<circ> C) t"
            by (smt (verit, ccfv_threshold) \<open>gyroaut (gyr b (B c) \<circ> B \<circ> C)\<close> \<open>x \<in> dom\<close> bij_betw_iff_bijections gyro_coaut_iff_gyro_aut gyrogroup.cogyroaut_def gyrogroup_axioms)
          then show ?thesis 
            by simp  
        qed
      qed
    qed
    ultimately show ?thesis
      by (simp add: bij_betw_def)
  qed
  ultimately show ?thesis
    by (simp add: gyroaut_def gyroplus_closed)
  qed
  moreover have " (\<forall>y. y \<notin> dom \<longrightarrow> ( (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined)) y = undefined)"
    by presburger
  ultimately show ?thesis  using gyrosem_dom_def 
    by blast
qed

lemma assoc_law_gyrosemi:
  assumes "(a,A)\<in> gyrosem_dom"
          "(b,B)\<in> gyrosem_dom"
          "(c,C)\<in> gyrosem_dom"
        shows "gyrosem_op (a,A) (gyrosem_op (b,B) (c,C)) = gyrosem_op (gyrosem_op (a,A) (b,B)) (c,C)"

proof-
  have "gyrosem_op (a,A) (gyrosem_op (b,B) (c,C)) = gyrosem_op (a,A) (b\<oplus>B c,   (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined))"
     using gyrosem_op_def[of "(b,B)" "(c,C)"] assms
  proof -
    have "(b \<oplus> snd (b, B) c, \<lambda>a. if a \<in> dom then (gyr b (snd (b, B) c) \<circ> B \<circ> C) a else undefined) = gyrosem_op (b, B) (c, C)"
      using \<open>gyrosem_op (b, B) (c, C) = (if (b, B) \<in> gyrosem_dom \<and> (c, C) \<in> gyrosem_dom then (fst (b, B) \<oplus> snd (b, B) (fst (c, C)), \<lambda>t. if t \<in> dom then (gyr (fst (b, B)) (snd (b, B) (fst (c, C))) \<circ> snd (b, B) \<circ> snd (c, C)) t else undefined) else undefined)\<close> assms(2) assms(3) by force
    then show ?thesis
      by (metis snd_conv)
  qed
  moreover have "(b\<oplus>B c,   (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined))\<in> gyrosem_dom"
    using gyrosem_dom_def
    using assms(2) assms(3) assoc_help1 by blast
  moreover have " gyrosem_op (a,A) (b\<oplus>B c,   (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined)) = 
(a \<oplus> A (b \<oplus> B c),  (\<lambda>x. if x \<in> dom then ((gyr a (A (b\<oplus>B c)))\<circ>A\<circ> (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined))x else undefined))"
    using gyrosem_op_def[of "(a,A)" "(b\<oplus>B c,   (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined))"]
    using assms(1) calculation(2) by auto
  moreover have "gyroaut A"
    using assms(1) gyrosem_dom_def by auto
  moreover have "(a \<oplus> A (b \<oplus> B c),  (\<lambda>x. if x \<in> dom then ((gyr a (A (b\<oplus>B c)))\<circ>A\<circ> (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined))x else undefined)) = 
(a\<oplus> ((A b) \<oplus> (A\<circ>B)c),  (\<lambda>x. if x \<in> dom then ((gyr a ((A b) \<oplus> (A\<circ>B) c)) \<circ>
 (\<lambda>t. if t \<in> dom then (gyr (A b) ((A\<circ>B) c) \<circ> A\<circ> B\<circ>C)t else undefined))x else undefined))"
  proof-
    have "a \<oplus> A (b \<oplus> B c) = a \<oplus> (A b \<oplus> (A \<circ> B) c)"
      using `gyroaut A`
      using assms(2) assms(3) gyroaut_closed gyroaut_def gyrosem_dom_def by force
    moreover have "\<forall>x\<in>dom. gyr a (A (b\<oplus>B c))x = (gyr a ((A b) \<oplus> (A\<circ>B) c))x"
      by (smt (verit, best) Product_Type.Collect_case_prodD assms(1) assms(2) assms(3) calculation fst_conv gyro_left_cancel gyroaut_closed gyroplus_closed gyrosem_dom_def o_apply snd_conv)
    moreover have "\<forall>x\<in>dom. (A\<circ> (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined))x =(gyr (A b) ((A\<circ>B) c) \<circ> A\<circ> B\<circ>C)x"
    proof
      fix x
      assume "x\<in>dom"
      show "(A\<circ> (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined))x =(gyr (A b) ((A\<circ>B) c) \<circ> A\<circ> B\<circ>C)x"
      proof-

        have " (A\<circ> (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined))x =  (A\<circ> (gyr b (B c) \<circ> B\<circ>C))x"
          by (simp add: \<open>x \<in> dom\<close>)
        moreover have "(gyr b (B c) \<circ> B \<circ> C) x = ((gyr b (B c)) \<circ> B) (C x)"
          by simp
        moreover have " ((gyr b (B c)) \<circ> B) (C x) =  (gyr b (B c)) (B(C x))"
          by auto
        moreover have " (gyr b (B c)) (B(C x)) =  (gyr b (B c)) ((B\<circ>C) x)"
          by simp
        moreover have " (A \<circ> (gyr b (B c) \<circ> B \<circ> C)) x = A ((gyr b (B c) \<circ> B \<circ> C) x)"
          by auto
        moreover have "A ((gyr b (B c) \<circ> B \<circ> C) x) = gyr (A b) (A (B c)) (A ((B\<circ>C) x))"
          using \<open>gyroaut A\<close> \<open>x \<in> dom\<close> assms(2) assms(3) gyroaut_closed gyroaut_gyro gyrosem_dom_def by force
        ultimately show ?thesis 
          by (metis comp_def)
      qed
    qed
    moreover have " (\<lambda>x. if x \<in> dom then ((gyr a (A (b\<oplus>B c)))\<circ>A\<circ> (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B\<circ>C)t else undefined))x else undefined) =
(\<lambda>x. if x \<in> dom then ((gyr a ((A b) \<oplus> (A\<circ>B) c)) \<circ>
 (\<lambda>t. if t \<in> dom then (gyr (A b) ((A\<circ>B) c) \<circ> A\<circ> B\<circ>C)t else undefined))x else undefined)"
    proof
      fix x
      show "(if x \<in> dom
          then (gyr a (A (b \<oplus> B c)) \<circ> A \<circ>
                (\<lambda>t. if t \<in> dom then (gyr b (B c) \<circ> B \<circ> C) t else undefined))
                x
          else undefined) =
         (if x \<in> dom
          then (gyr a (A b \<oplus> (A \<circ> B) c) \<circ>
                (\<lambda>t. if t \<in> dom then (gyr (A b) ((A \<circ> B) c) \<circ> A \<circ> B \<circ> C) t
                      else undefined))
                x
          else undefined)"
        by (smt (verit) Product_Type.Collect_case_prodD assms(1) assms(2) assms(3) calculation(1) calculation(3) comp_apply fst_conv gyro_left_cancel gyroaut_closed gyroplus_closed gyrosem_dom_def snd_conv)
    qed
      ultimately show ?thesis 
        by blast
    qed
   
    moreover have " gyrosem_op (gyrosem_op (a,A) (b,B)) (c,C) =
 gyrosem_op (a\<oplus>A b,   (\<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A\<circ>B)t else undefined))
  (c, C)"
         using gyrosem_op_def[of "(a,A)" "(b,B)"] assms
    proof -
      have "(a \<oplus> snd (a, A) b, \<lambda>aa. if aa \<in> dom then (gyr a (snd (a, A) b) \<circ> A \<circ> B) aa else undefined) = gyrosem_op (a, A) (b, B)"
        using \<open>gyrosem_op (a, A) (b, B) = (if (a, A) \<in> gyrosem_dom \<and> (b, B) \<in> gyrosem_dom then (fst (a, A) \<oplus> snd (a, A) (fst (b, B)), \<lambda>t. if t \<in> dom then (gyr (fst (a, A)) (snd (a, A) (fst (b, B))) \<circ> snd (a, A) \<circ> snd (b, B)) t else undefined) else undefined)\<close> assms(1) assms(2) by auto
      then show ?thesis
        by (metis (no_types) snd_conv)
    qed
    moreover have "  gyrosem_op
   (a \<oplus> A b, \<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t else undefined)
   (c, C) =
  (if (a \<oplus> A b, \<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t else undefined)
      \<in> gyrosem_dom \<and>
      (c, C) \<in> gyrosem_dom
   then (fst (a \<oplus> A b,
              \<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t else undefined) \<oplus>
         snd (a \<oplus> A b,
              \<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t else undefined)
          (fst (c, C)),
         \<lambda>t. if t \<in> dom
              then (gyr (fst (a \<oplus> A b,
                              \<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t
                                   else undefined))
                     (snd (a \<oplus> A b,
                           \<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t
                                else undefined)
                       (fst (c, C))) \<circ>
                    snd (a \<oplus> A b,
                         \<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t
                              else undefined) \<circ>
                    snd (c, C))
                    t
              else undefined)
   else undefined)"
      using gyrosem_op_def[of "(a\<oplus>A b,   (\<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A\<circ>B)t else undefined))"
    "(c,C)"]
      by blast
    moreover have "(a \<oplus> A b, \<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t else undefined)
      \<in> gyrosem_dom"
      using assms(1) assms(2) assoc_help1 by blast
        moreover have "  gyrosem_op
   (a \<oplus> A b, \<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t else undefined)
   (c, C) =
   ((a \<oplus> A b) \<oplus>
         
              (\<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t else undefined)
          c,
         \<lambda>t. if t \<in> dom
              then (gyr (a \<oplus> A b)
                     (
                           (\<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t
                                else undefined)
                       c) \<circ>
                    
                         (\<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t
                              else undefined) \<circ>
                     C)
                    t
              else undefined)
  
   " 
          using assms(3) calculation(7) calculation(8) by fastforce
        moreover have "(a \<oplus> A b) \<oplus>
         
              (\<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t else undefined)
          c = (a \<oplus> (A b \<oplus> (A \<circ> B) c))"
          using assms(1) assms(2) assms(3) gyro_left_assoc gyroaut_closed gyrosem_dom_def by auto
        moreover have " (\<lambda>t. if t \<in> dom
              then (gyr (a \<oplus> A b)
                     (
                           (\<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t
                                else undefined)
                       c) \<circ>
                    
                         (\<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t
                              else undefined) \<circ>
                     C)
                    t
              else undefined) = ( \<lambda>x. if x \<in> dom
           then (gyr a (A b \<oplus> (A \<circ> B) c) \<circ>
                 (\<lambda>t. if t \<in> dom then (gyr (A b) ((A \<circ> B) c) \<circ> A \<circ> B \<circ> C) t
                       else undefined))
                 x
           else undefined)"
        proof
          fix t
          show "(if t \<in> dom
          then (gyr (a \<oplus> A b)
                 (if c \<in> dom then (gyr a (A b) \<circ> A \<circ> B) c else undefined) \<circ>
                (\<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t else undefined) \<circ>
                C)
                t
          else undefined) =
         (if t \<in> dom
          then (gyr a (A b \<oplus> (A \<circ> B) c) \<circ>
                (\<lambda>t. if t \<in> dom then (gyr (A b) ((A \<circ> B) c) \<circ> A \<circ> B \<circ> C) t
                      else undefined))
                t
          else undefined) "
          proof-
            have "t\<in>dom \<or> \<not>t\<in>dom" by blast
            moreover {
              assume "t\<in>dom"
              then have "(if t \<in> dom
          then (gyr (a \<oplus> A b)
                 (if c \<in> dom then (gyr a (A b) \<circ> A \<circ> B) c else undefined) \<circ>
                (\<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t else undefined) \<circ>
                C)
                t
          else undefined) = (gyr (a \<oplus> A b)
                 (if c \<in> dom then (gyr a (A b) \<circ> A \<circ> B) c else undefined) \<circ>
                (\<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t else undefined) \<circ>
                C)
                t"
                by argo
              moreover have " (gyr (a \<oplus> A b)
                 (if c \<in> dom then (gyr a (A b) \<circ> A \<circ> B) c else undefined) \<circ>
                (\<lambda>t. if t \<in> dom then (gyr a (A b) \<circ> A \<circ> B) t else undefined) \<circ>
                C)
                t = (gyr (a \<oplus> A b) ((gyr a (A b) \<circ> A \<circ> B) c)) 
                 ((gyr a (A b) \<circ> A \<circ> B) (C t))"
                using \<open>t \<in> dom\<close> assms(3) gyroaut_closed gyrosem_dom_def by force
          moreover have "(if t \<in> dom
          then (gyr a (A b \<oplus> (A \<circ> B) c) \<circ>
                (\<lambda>t. if t \<in> dom then (gyr (A b) ((A \<circ> B) c) \<circ> A \<circ> B \<circ> C) t
                      else undefined))
                t
          else undefined)  = (gyr a (A b \<oplus> (A \<circ> B) c) \<circ>
                (\<lambda>t. if t \<in> dom then (gyr (A b) ((A \<circ> B) c) \<circ> A \<circ> B \<circ> C) t
                      else undefined))
                t"
            using \<open>t \<in> dom\<close> by argo
          moreover have " (gyr a (A b \<oplus> (A \<circ> B) c) \<circ>
                (\<lambda>t. if t \<in> dom then (gyr (A b) ((A \<circ> B) c) \<circ> A \<circ> B \<circ> C) t
                      else undefined))
                t =(gyr a (A b \<oplus> (A \<circ> B) c) ( (gyr (A b) ((A \<circ> B) c) \<circ> A \<circ> B \<circ> C) t))"
            by (simp add: \<open>t \<in> dom\<close>)
          moreover have "(gyr (a \<oplus> A b) ((gyr a (A b) \<circ> A \<circ> B) c)) 
                 ((gyr a (A b) \<circ> A \<circ> B) (C t)) = (gyr a (A b \<oplus> (A \<circ> B) c) ( (gyr (A b) ((A \<circ> B) c) \<circ> A \<circ> B \<circ> C) t))"
          proof-
            have "a\<in>dom"
              using assms(1) gyrosem_dom_def by auto
            moreover have "A b\<in>dom"
              using \<open>gyroaut A\<close> assms(2) gyroaut_closed gyrosem_dom_def by auto
            moreover have "((A \<circ> B) c)\<in>dom"
              using \<open>gyroaut A\<close> assms(2) assms(3) gyroaut_closed gyrosem_dom_def by force
            moreover have " (A \<circ> B\<circ> C) t\<in>dom"
              using \<open>gyroaut A\<close> \<open>t \<in> dom\<close> assms(2) assms(3) gyroaut_closed gyrosem_dom_def by fastforce
            ultimately show ?thesis 
              using  gyr_nested_1[of "a" "A b" "((A \<circ> B) c)", OF `a\<in>dom`
                      `A b\<in>dom` `((A \<circ> B) c)\<in>dom`]
              by simp
          qed
           
            
          ultimately have ?thesis 
            by argo
        }
        moreover {
          assume "\<not>t\<in>dom"
          then have ?thesis 
            by force

        }
        ultimately show ?thesis 
          by fastforce
      qed
    qed
    ultimately show ?thesis 
        by argo    
qed

(*((a1 , A1 )(a2 , A2 ))(a3 , A3 )
= (a1 + A1 a2 , gyr[a1 , A1 a2 ]A1 A2 )(a3 , A3 )
= ((a1 + A1 a2 ) + gyr[a1 , A1 a2 ]A1 A2 a3 ,
gyr[a1 + A1 a2 , gyr[a1 , A1 a2 ]A1 A2 a3 ]gyr[a1 , A1 a2 ]A1 A2 A3 )*)

lemma inv_unique_gyrosemi:
  assumes "(a,A)\<in> gyrosem_dom"
          "(b,B)\<in> gyrosem_dom"
          "(c,C)\<in> gyrosem_dom"
"gyrosem_op (b,B) (a,A) = (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)"
"gyrosem_op (c,C) (a,A) = (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)" 
shows "(b,B) = (c,C)"
  by (smt (verit, ccfv_SIG) Product_Type.Collect_case_prodD assms(1) assms(2) assms(3) assms(4) assms(5) assoc_law_gyrosemi gyrosem_dom_def inv_gyrosemi inv_in_gyrosemi neutral_gyrosemi zero_id_in_gyrosem_dom)

lemma inv_of_a_I1:
  shows "\<forall>a\<in>dom. (a, \<lambda>y. if y \<in> dom then y else undefined)\<in> gyrosem_dom"
  using gyrosem_dom_def zero_id_in_gyrosem_dom by auto

lemma inv_of_a_I2:
  assumes "a\<in>dom"
  shows "gyrosem_op (\<ominus>a,  \<lambda>y. if y \<in> dom then y else undefined) (a, \<lambda>y. if y \<in> dom then y else undefined) = (0\<^sub>g,  \<lambda>y. if y \<in> dom then y else undefined)"
  by (smt (verit, best) assms inv_gyrosemi inv_in_gyrosemi inv_of_a_I1 inv_unique_gyrosemi neutral_gyrosemi snd_conv zero_id_in_gyrosem_dom)

lemma inv_of_a_I3:
  assumes "a\<in>dom" "b\<in>dom"
  shows "gyrosem_op (gyrosem_op  (a,  \<lambda>y. if y \<in> dom then y else undefined)  (b,  \<lambda>y. if y \<in> dom then y else undefined))
  (gyrosem_op (\<ominus>b,  \<lambda>y. if y \<in> dom then y else undefined)  (\<ominus>a,  \<lambda>y. if y \<in> dom then y else undefined)) =  (0\<^sub>g,  \<lambda>y. if y \<in> dom then y else undefined)"
proof-
  have "(\<ominus>b,  \<lambda>y. if y \<in> dom then y else undefined) \<in> gyrosem_dom"
    using assms(2) ax1 inv_of_a_I1 by blast
  moreover  have "(\<ominus>a,  \<lambda>y. if y \<in> dom then y else undefined) \<in> gyrosem_dom"
    using assms(1) ax1 inv_of_a_I1 by blast
  moreover  have "(b,  \<lambda>y. if y \<in> dom then y else undefined) \<in> gyrosem_dom"
    using assms(2) ax1 inv_of_a_I1 by blast
  moreover have "(a,  \<lambda>y. if y \<in> dom then y else undefined) \<in> gyrosem_dom"
    using assms(1) ax1 inv_of_a_I1 by blast
  moreover have "gyrosem_op (gyrosem_op  (a,  \<lambda>y. if y \<in> dom then y else undefined)  (b,  \<lambda>y. if y \<in> dom then y else undefined))
  (gyrosem_op (\<ominus>b,  \<lambda>y. if y \<in> dom then y else undefined)  (\<ominus>a,  \<lambda>y. if y \<in> dom then y else undefined)) =
    gyrosem_op (gyrosem_op  (a,  \<lambda>y. if y \<in> dom then y else undefined) (gyrosem_op (b,  \<lambda>y. if y \<in> dom then y else undefined)
   (\<ominus>b,  \<lambda>y. if y \<in> dom then y else undefined)))  (\<ominus>a,  \<lambda>y. if y \<in> dom then y else undefined)"
    by (smt (z3) assoc_law_gyrosemi calculation(1) calculation(2) calculation(3) calculation(4) gyrosem_op_def neutral_gyrosemi zero_id_in_gyrosem_dom)
    
  ultimately show ?thesis

    by (metis (no_types, lifting) assms(1) assms(2) assoc_law_gyrosemi ax1 gyro_inv_idem inv_of_a_I2 neutral_gyrosemi)
qed


lemma inv_of_a_I4:
  assumes "a\<in>dom" "b\<in>dom"
  shows "(gyrosem_op (\<ominus>b,  \<lambda>y. if y \<in> dom then y else undefined)  (\<ominus>a,  \<lambda>y. if y \<in> dom then y else undefined))
=  (\<ominus>b \<ominus>\<^sub>b a, \<lambda>t. if t\<in>dom then gyr (\<ominus>b) (\<ominus>a) t else undefined)"

proof-
   have "(\<ominus>b,  \<lambda>y. if y \<in> dom then y else undefined) \<in> gyrosem_dom"
    using assms(2) ax1 inv_of_a_I1 by blast
  moreover  have "(\<ominus>a,  \<lambda>y. if y \<in> dom then y else undefined) \<in> gyrosem_dom"
    using assms(1) ax1 inv_of_a_I1 by blast

  moreover have "(if (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined) \<in> gyrosem_dom \<and>
        (\<ominus> a, \<lambda>y. if y \<in> dom then y else undefined) \<in> gyrosem_dom
     then (fst (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined) \<oplus>
           snd (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined)
            (fst (\<ominus> a, \<lambda>y. if y \<in> dom then y else undefined)),
           \<lambda>t. if t \<in> dom
                then (gyr (fst (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined))
                       (snd (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined)
                         (fst (\<ominus> a, \<lambda>y. if y \<in> dom then y else undefined))) \<circ>
                      snd (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined) \<circ>
                      snd (\<ominus> a, \<lambda>y. if y \<in> dom then y else undefined))
                      t
                else undefined)
     else undefined) = (fst (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined) \<oplus>
           snd (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined)
            (fst (\<ominus> a, \<lambda>y. if y \<in> dom then y else undefined)),
           \<lambda>t. if t \<in> dom
                then (gyr (fst (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined))
                       (snd (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined)
                         (fst (\<ominus> a, \<lambda>y. if y \<in> dom then y else undefined))) \<circ>
                      snd (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined) \<circ>
                      snd (\<ominus> a, \<lambda>y. if y \<in> dom then y else undefined))
                      t
                else undefined)"
    using calculation(1) calculation(2) by argo
  moreover have "(fst (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined) \<oplus>
           snd (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined)
            (fst (\<ominus> a, \<lambda>y. if y \<in> dom then y else undefined)),
           \<lambda>t. if t \<in> dom
                then (gyr (fst (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined))
                       (snd (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined)
                         (fst (\<ominus> a, \<lambda>y. if y \<in> dom then y else undefined))) \<circ>
                      snd (\<ominus> b, \<lambda>y. if y \<in> dom then y else undefined) \<circ>
                      snd (\<ominus> a, \<lambda>y. if y \<in> dom then y else undefined))
                      t
                else undefined) = (\<ominus>b \<oplus> ( \<lambda>y. if y \<in> dom then y else undefined)(\<ominus>a),
           \<lambda>t. if t \<in> dom then ((gyr (\<ominus>b) ((\<lambda>y. if y \<in> dom then y else undefined) (\<ominus>a)))\<circ> 
   (\<lambda>y. if y \<in> dom then y else undefined) \<circ>  (\<lambda>y. if y \<in> dom then y else undefined)) t else undefined)"
    by (simp add: ext)
  moreover have "(\<ominus>b \<oplus> ( \<lambda>y. if y \<in> dom then y else undefined)(\<ominus>a),
           \<lambda>t. if t \<in> dom then ((gyr (\<ominus>b) ((\<lambda>y. if y \<in> dom then y else undefined) (\<ominus>a)))\<circ> 
   (\<lambda>y. if y \<in> dom then y else undefined) \<circ>  (\<lambda>y. if y \<in> dom then y else undefined)) t else undefined) =
  (\<ominus>b \<ominus>\<^sub>b a, \<lambda>t. if t\<in>dom then gyr (\<ominus>b) (\<ominus>a) t else undefined) "
    using assms(1) ax1 gyrominus_def by auto
  ultimately  show ?thesis 
    using gyrosem_op_def by presburger
qed

lemma inv_of_a_I5:
  assumes "a\<in>dom" "b\<in>dom"
  shows "(gyrosem_op (a,  \<lambda>y. if y \<in> dom then y else undefined)  (b,  \<lambda>y. if y \<in> dom then y else undefined))
=  (a \<oplus> b, \<lambda>t. if t\<in>dom then gyr (a) (b) t else undefined)"
  using inv_of_a_I4[of "\<ominus>b" "\<ominus>a"]
  using assms(1) assms(2) ax1 gyrominus_def by force


lemma inv_help2:
  assumes "a\<in>dom" "b\<in>dom"
  shows "bij_betw (\<lambda>t. if t \<in> dom then gyr a b t else undefined) dom dom"
      proof-
        have "inj_on (\<lambda>t. if t \<in> dom then gyr a b t else undefined) dom"
          by (smt (verit, best) assms(1) assms(2) gyr_inj inj_onCI)
        moreover have "(\<lambda>t. if t \<in> dom then gyr a b t else undefined) `dom = dom"
        proof
          show "(\<lambda>t. if t \<in> dom then gyr a b t else undefined) ` dom \<subseteq> dom"
            by (simp add: assms(1) assms(2) gyr_def_closed image_subset_iff)
        next
          show "dom \<subseteq> (\<lambda>t. if t \<in> dom then gyr a b t else undefined) ` dom"
          proof
            fix x
            assume "x\<in>dom"
            show "x \<in> (\<lambda>t. if t \<in> dom then gyr a b t else undefined) ` dom"
            proof-
              obtain "t" where "t\<in> dom \<and> gyr a b t = x"
                by (metis \<open>x \<in> dom\<close> assms(1) assms(2) bij_betw_iff_bijections gyr_gyroaut gyroaut_def)
              have "(if t \<in> dom then gyr a b t else undefined)= gyr a b t"
                using \<open>t \<in> dom \<and> gyr a b t = x\<close> by presburger
              then show ?thesis 
                using \<open>t \<in> dom \<and> gyr a b t = x\<close> by force
            qed
          qed
        qed
        ultimately show ?thesis 
          by (simp add: bij_betw_def)
      qed

lemma inv_help1:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. inv_into dom (\<lambda>t. if t \<in> dom then gyr a b t else undefined) x 
  = (inv_into dom (gyr a b))x"
proof
  fix x
  assume "x\<in>dom"
  show "inv_into dom (\<lambda>t. if t \<in> dom then gyr a b t else undefined) x 
  = (inv_into dom (gyr a b))x"
  proof-
    obtain "t" where *: "t\<in>dom \<and> x = (\<lambda>t. if t \<in> dom then gyr a b t else undefined)t"
      by (metis \<open>x \<in> dom\<close> assms(1) assms(2) bij_betw_iff_bijections gyroaut_def gyrogroup.gyr_gyroaut gyrogroup_axioms)
    moreover have "x = gyr a b t"
      using calculation by presburger
    moreover have " (inv_into dom (gyr a b))x = t"
      by (metis assms(1) assms(2) bij_betw_inv_into_left calculation(1) gyroaut_def gyrogroup.gyr_gyroaut gyrogroup_axioms)
    moreover have "inv_into dom (\<lambda>t. if t \<in> dom then gyr a b t else undefined) x  = t"
    proof-
      have "bij_betw (\<lambda>t. if t \<in> dom then gyr a b t else undefined) dom dom"
        using assms(1) assms(2) inv_help2 by blast
      then show ?thesis using * 
        by (meson bij_betw_inv_into_left)
    qed
    ultimately show ?thesis 
      by argo  
  qed
qed

lemma inv_of_a_Ihelp:
  assumes "a\<in>dom" "b\<in>dom"
  shows "(a \<oplus> b, \<lambda>t. if t\<in>dom then gyr (a) (b) t else undefined)\<in> gyrosem_dom"
  proof-
    have "a\<oplus>b\<in>dom"
      using assms(1) assms(2) gyroplus_closed by blast
    moreover have "bij_betw (\<lambda>t. if t\<in>dom then gyr (a) (b) t else undefined) dom dom"
      by (simp add: assms(1) assms(2) inv_help2)
    moreover have "\<forall>x\<in>dom. \<forall>y\<in>dom. (\<lambda>t. if t\<in>dom then gyr (a) (b) t else undefined) (x\<oplus>y) = 
(\<lambda>t. if t\<in>dom then gyr (a) (b) t else undefined)x \<oplus> (\<lambda>t. if t\<in>dom then gyr (a) (b) t else undefined) y"
      using assms(1) assms(2) gyroplus_closed by auto
    moreover have "\<forall>y. \<not>y\<in>dom \<longrightarrow> ( \<lambda>t. if t\<in>dom then gyr (a) (b) t else undefined)y = undefined"
      by presburger
    moreover have "gyroaut (\<lambda>t. if t\<in>dom then gyr (a) (b) t else undefined)"
      using calculation(2) calculation(3) gyroaut_def by blast
    ultimately show ?thesis
      using gyrosem_dom_def
      by blast
      
  qed
lemma inv_of_a_I6:
  assumes "a\<in>dom" "b\<in>dom"
  shows "gyrosem_op (\<ominus> ((inv_into dom (gyr a b))(a \<oplus> b)), 
(\<lambda>t. if t\<in>dom then (inv_into dom (gyr a b))t  else undefined))
(a \<oplus> b, \<lambda>t. if t\<in>dom then gyr (a) (b) t else undefined)
  = (0\<^sub>g,  \<lambda>y. if y \<in> dom then y else undefined)"
 
proof-
  have *:"(a \<oplus> b, \<lambda>t. if t\<in>dom then gyr (a) (b) t else undefined)\<in> gyrosem_dom"

    using assms(1) assms(2) inv_of_a_Ihelp by blast
 
  moreover have "a \<oplus> b \<in> dom"
    using assms(1) assms(2) gyroplus_closed by blast
  moreover have "(\<ominus> (if a \<oplus> b \<in> dom
          then inv_into dom (\<lambda>t. if t \<in> dom then gyr a b t else undefined)
                (a \<oplus> b)
          else undefined),
      \<lambda>x. if x \<in> dom
           then inv_into dom (\<lambda>t. if t \<in> dom then gyr a b t else undefined) x
           else undefined) = (\<ominus> ((inv_into dom (gyr a b))(a \<oplus> b)), 
(\<lambda>t. if t\<in>dom then (inv_into dom (gyr a b))t  else undefined))"
  proof-
   have "a \<oplus> b \<in> dom"
    using assms(1) assms(2) gyroplus_closed by blast
  moreover have "\<ominus> (if a \<oplus> b \<in> dom
        then inv_into dom (\<lambda>t. if t \<in> dom then gyr a b t else undefined) (a \<oplus> b)
        else undefined) =
    \<ominus> ((inv_into dom (gyr a b)) (a \<oplus> b))"
  proof-
have "\<ominus> (if a \<oplus> b \<in> dom
        then inv_into dom (\<lambda>t. if t \<in> dom then gyr a b t else undefined) (a \<oplus> b)
        else undefined) = \<ominus> ( inv_into dom (\<lambda>t. if t \<in> dom then gyr a b t else undefined) (a \<oplus> b))"
  using calculation by presburger
  moreover have " \<ominus> ( inv_into dom (\<lambda>t. if t \<in> dom then gyr a b t else undefined) (a \<oplus> b)) =\<ominus> ((inv_into dom (gyr a b)) (a\<oplus>b))"
    by (simp add: \<open>a \<oplus> b \<in> dom\<close> assms(1) assms(2) inv_help1)
    
  
  ultimately show ?thesis 
    using inv_gyrosemi[of "a \<oplus> b" "\<lambda>t. if t\<in>dom then gyr (a) (b) t else undefined", OF *]
    by argo
qed
  moreover have "(\<lambda>x. if x \<in> dom
           then inv_into dom (\<lambda>t. if t \<in> dom then gyr a b t else undefined) x
           else undefined) = (\<lambda>t. if t\<in>dom then (inv_into dom (gyr a b))t  else undefined)"
    using assms(1) assms(2) inv_help1 by fastforce
    ultimately show ?thesis 
      by presburger
  qed
  ultimately show ?thesis 
    using inv_gyrosemi by force
qed

lemma inv_a_I_8:
  assumes "a\<in>dom" "b\<in>dom"
  shows "gyrosem_op
     (gyrosem_op (\<ominus>b, \<lambda>y. if y \<in> dom then y else undefined)
       (\<ominus>a, \<lambda>y. if y \<in> dom then y else undefined))
     (gyrosem_op (a, \<lambda>y. if y \<in> dom then y else undefined)
       (b, \<lambda>y. if y \<in> dom then y else undefined)) =
    (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)"
  by (metis (no_types, lifting) assms(1) assms(2) ax1 gyro_inv_idem inv_of_a_I3)

lemma inv_a_I_help2:
  assumes "a\<in>dom" "b\<in>dom"
 shows  "     (\<ominus> (inv_into dom (gyr a b) (a \<oplus> b)),
      \<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined)\<in> gyrosem_dom"
    proof-
      have " \<ominus> (inv_into dom (gyr a b) (a \<oplus> b))\<in>dom"
        by (meson assms(1) assms(2) gyr_gyroaut gyroaut_closed gyroaut_inv gyrogroup.ax1 gyrogroup_axioms gyroplus_closed)
      moreover have "bij_betw (\<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined) dom dom"
      proof-
        have "inj_on (\<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined) dom"
          by (smt (verit, best) assms(1) assms(2) bij_betw_inv_into_right inj_onI inv_help1 inv_help2)
        moreover have "(\<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined) `dom = dom"
        proof
          show "(\<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined) ` dom \<subseteq> dom"
            by (smt (verit, del_insts) assms(1) assms(2) bij_betw_def image_subset_iff inv_help1 inv_help2 inv_into_into)
        next
          show "dom \<subseteq> (\<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined) ` dom "
          proof
            fix x
            assume "x\<in>dom"
            show  "x \<in> (\<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined) `
              dom "
              by (smt (verit, del_insts) \<open>x \<in> dom\<close> assms(1) assms(2) f_inv_into_f gyr_def_closed gyr_inj image_iff inv_help2 inv_into_into)
          qed
        qed
        ultimately show ?thesis 
          by (simp add: bij_betw_def)
      qed
        moreover have "\<forall>x\<in>dom. \<forall>y\<in>dom. ( (\<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined)(x\<oplus>y) =
   (\<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined)x \<oplus>  (\<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined)y)"
        proof
          fix x 
          assume "x\<in>dom"
          show "  \<forall>y\<in>dom.
            (if x \<oplus> y \<in> dom then inv_into dom (gyr a b) (x \<oplus> y)
             else undefined) =
            (if x \<in> dom then inv_into dom (gyr a b) x else undefined) \<oplus>
            (if y \<in> dom then inv_into dom (gyr a b) y else undefined)"
          proof
            fix y
            assume "y\<in>dom"
 show " 
            (if x \<oplus> y \<in> dom then inv_into dom (gyr a b) (x \<oplus> y)
             else undefined) =
            (if x \<in> dom then inv_into dom (gyr a b) x else undefined) \<oplus>
            (if y \<in> dom then inv_into dom (gyr a b) y else undefined)"

   using \<open>x \<in> dom\<close> \<open>y \<in> dom\<close> 
   using assms(1) assms(2) gyr_gyroaut gyroaut_def gyroaut_inv gyroplus_closed by auto       
 qed
qed
  moreover have "\<forall>x. \<not>x\<in>dom \<longrightarrow>  (\<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined)x = undefined"
    by auto
  moreover have "gyroaut  (\<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined)"
  using calculation(2) calculation(3) gyroaut_def by presburger
  ultimately show ?thesis 
    using gyrosem_dom_def
    by blast
qed
lemma inv_a_I_7:
  assumes "a\<in>dom" "b\<in>dom"
  shows "(\<ominus> ((inv_into dom (gyr a b))(a \<oplus> b)), 
(\<lambda>t. if t\<in>dom then (inv_into dom (gyr a b))t  else undefined)) = (\<ominus>b \<ominus>\<^sub>b a, \<lambda>t. if t\<in>dom then gyr (\<ominus>b) (\<ominus>a) t else undefined)"
  using  inv_unique_gyrosemi  inv_of_a_I6[of a b, OF assms]
proof-
  have "gyrosem_op
 (\<ominus> b \<ominus>\<^sub>b a, \<lambda>t. if t \<in> dom then gyr (\<ominus> b) (\<ominus> a) t else undefined)
    (a \<oplus> b, \<lambda>t. if t \<in> dom then gyr a b t else undefined)
 =     (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)"
    using inv_of_a_I4[of a b, OF assms]
inv_of_a_I3[of a b, OF assms]
inv_of_a_I5[of a b, OF assms]
inv_a_I_8[of a b, OF assms]
    by argo
  moreover have " gyrosem_op
     (\<ominus> (inv_into dom (gyr a b) (a \<oplus> b)),
      \<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined)
     (a \<oplus> b, \<lambda>t. if t \<in> dom then gyr a b t else undefined) =
    (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)"
    using \<open>gyrosem_op (\<ominus> (inv_into dom (gyr a b) (a \<oplus> b)), \<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined) (a \<oplus> b, \<lambda>t. if t \<in> dom then gyr a b t else undefined) = (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)\<close> by blast
  ultimately show ?thesis 
  proof-
    have "(a \<oplus> b, \<lambda>t. if t \<in> dom then gyr a b t else undefined)\<in> gyrosem_dom"
      using assms(1) assms(2) inv_of_a_Ihelp by blast
    moreover have " (\<ominus> b \<ominus>\<^sub>b a, \<lambda>t. if t \<in> dom then gyr (\<ominus> b) (\<ominus> a) t else undefined)\<in>gyrosem_dom"
      using assms(1) assms(2) ax1 gyrominus_def inv_of_a_Ihelp by presburger
    moreover have "     (\<ominus> (inv_into dom (gyr a b) (a \<oplus> b)),
      \<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined)\<in> gyrosem_dom"
      using assms(1) assms(2) inv_a_I_help2 by blast
    ultimately show ?thesis
      using \<open>gyrosem_op (\<ominus> (inv_into dom (gyr a b) (a \<oplus> b)), \<lambda>t. if t \<in> dom then inv_into dom (gyr a b) t else undefined) (a \<oplus> b, \<lambda>t. if t \<in> dom then gyr a b t else undefined) = (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)\<close> \<open>gyrosem_op (\<ominus> b \<ominus>\<^sub>b a, \<lambda>t. if t \<in> dom then gyr (\<ominus> b) (\<ominus> a) t else undefined) (a \<oplus> b, \<lambda>t. if t \<in> dom then gyr a b t else undefined) = (0\<^sub>g, \<lambda>y. if y \<in> dom then y else undefined)\<close> inv_unique_gyrosemi by blast
  qed
qed



    text \<open>Thm 2.25, (2.77)\<close>
lemma inv_gyr:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. ((inv_into dom) (gyr a b)) x = gyr (\<ominus>b) (\<ominus>a) x"
proof-
  have "(\<lambda>t. if t\<in>dom then (inv_into dom (gyr a b))t  else undefined) = (\<lambda>t. if t\<in>dom then gyr (\<ominus>b) (\<ominus>a) t else undefined )"
    using  inv_a_I_7[of a b, OF assms] 
    by force
  then show ?thesis 
    by meson
qed

text \<open>Thm 2.26, (2.86)\<close>
lemma gyr_aut_inv_1:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. (inv_into dom) (gyr a b) x = gyr a (\<ominus> (gyr a b b)) x"
proof
  fix x
  assume "x\<in>dom"
  show "(inv_into dom) (gyr a b) x = gyr a (\<ominus> (gyr a b b)) x"
  proof-
    have " gyr a (\<ominus> (gyr a b b)) x \<in> dom"
    proof-
      have *:"(\<ominus> (gyr a b b))\<in>dom"
        by (meson assms(1) assms(2) ax1 bij_betwE gyr_gyroaut gyroaut_def)
      then show ?thesis
        using * \<open>x \<in> dom\<close> assms 
        gyr_def_closed[OF assms(1) * `x\<in>dom`]
        by meson
    qed
      have "(gyr a (\<ominus> (gyr a b b)) \<circ> gyr a b)x = x"
      using \<open>x \<in> dom\<close> assms(1) assms(2) gyr_nested_2 by blast
    moreover have " (gyr a b  \<circ> gyr a (\<ominus> (gyr a b b)))x = x"
    proof -
      have f1: "b \<in> dom"
        using assms(2) by blast
      have f2: "a \<in> dom"
        using assms(1) by fastforce
      have f3: "\<forall>a aa. a \<in> dom \<longrightarrow> aa \<in> dom \<longrightarrow> (\<forall>ab. ab \<in> dom \<longrightarrow> (gyr a (\<ominus> (gyr a aa aa)) \<circ> gyr a aa) ab = ab)"
        using gyr_nested_2 by blast
      have "\<forall>f fa fb a. f \<circ> fa = fb \<longrightarrow> f (fa (a::'a)::'a) = (fb a::'a)"
        using comp_eq_dest_lhs by blast
      then show ?thesis
        using f3 f2 f1 \<open>gyr a (\<ominus> (gyr a b b)) x \<in> dom\<close> \<open>x \<in> dom\<close> ax1 gyr_def_closed by moura
    qed
    ultimately show ?thesis
      using inv_into_def[of dom "gyr a b"]
      using \<open>gyr a (\<ominus> (gyr a b b)) x \<in> dom\<close> assms(1) assms(2) gyr_nested_2 by auto
  qed
qed

text \<open>Thm 2.26, (2.87)\<close>
lemma gyr_aut_inv_2:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x. (x\<in>dom \<longrightarrow> (inv_into dom) (gyr a b) x= gyr (\<ominus> a) (a \<oplus> b)x)"
  by (smt (verit, ccfv_threshold) assms(1) assms(2) bij_betw_iff_bijections bij_betw_inv_into_left comp_apply gyr_auto_id1 gyr_gyroaut gyroaut_def)

text \<open>Thm 2.26, (2.88)\<close>
lemma gyr_aut_inv_3:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. ((inv_into dom) (gyr a b) x = gyr b (a \<oplus> b) x)"
proof
  fix x
  assume "x\<in>dom"
  show " ((inv_into dom) (gyr a b) x = gyr b (a \<oplus> b) x)"
    by (smt (z3) \<open>x \<in> dom\<close> assms(1) assms(2) gyr_aut_inv_2 gyro_inv_idem gyrogroup.ax1 gyrogroup.gyr_left_loop gyrogroup_axioms gyroplus_closed oplus_ominus_cancel)
qed      

text \<open>Thm 2.26, (2.89)\<close>
lemma gyr_1:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. (gyr a b x = gyr b (\<ominus>b \<ominus>\<^sub>b a) x)"
  by (metis assms(1) assms(2) gyr_aut_inv_2 gyro_inv_idem gyro_is_left_inv gyro_is_left_inv_def gyrominus_def inv_gyr) 


text \<open>Thm 2.26, (2.90)\<close>
lemma gyr_2:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. (gyr a b x = gyr (\<ominus>a) (\<ominus>b \<ominus>\<^sub>b a) x)"
  using inv_gyr gyr_aut_inv_3 gyrominus_def 
  by (simp add: assms(1) assms(2) ax1)

text \<open>Thm 2.26, (2.91)\<close>
lemma gyr_3:
   assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. (gyr a b x = gyr (\<ominus> (a \<oplus> b)) a x)"
  by (metis (no_types, lifting) assms(1) assms(2) gyr_1 gyro_inv_idem gyrogroup.ax1 gyrogroup_axioms gyrominus_def gyroplus_closed oplus_ominus_cancel)

lemma inv_gyr_bij:
  assumes "a\<in>dom" "b\<in>dom"
  shows "bij_betw ((inv_into dom) (gyr a b)) dom dom"
  by (meson assms(1) assms(2) bij_betw_inv_into gyr_gyroaut gyroaut_def)

lemma thm2_27_help:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. (gyr a (\<ominus> (\<ominus>b \<ominus>\<^sub>b a)) x =  (gyr (\<ominus>a) (\<ominus>b \<ominus>\<^sub>b a)) x)"
proof
  fix x
  assume "x\<in>dom"
  show "(gyr a (\<ominus> (\<ominus>b \<ominus>\<^sub>b a))) x =  (gyr (\<ominus>a) (\<ominus>b \<ominus>\<^sub>b a)) x"
  proof-
    have "\<forall>x\<in>dom. inv_into dom (gyr a b) x = gyr (\<ominus>b) (\<ominus>a) x"
      using assms(1) assms(2) inv_gyr by auto
    moreover have "\<forall>x\<in>dom. inv_into dom (gyr a b) x = gyr (\<ominus>b \<ominus>\<^sub>b a) (\<ominus>a) x"
      by (simp add: assms(1) assms(2) ax1 gyr_left_loop gyrominus_def inv_gyr)
    moreover have "\<forall>x\<in>dom. inv_into dom (gyr a b) x =  inv_into dom (gyr a (\<ominus> (\<ominus>b \<ominus>\<^sub>b a))) x"
      by (metis assms(1) assms(2) ax1 calculation(2) gyro_inv_idem gyrogroup.gyrominus_closed gyrogroup_axioms inv_gyr)
    moreover have "\<forall>y\<in>dom. \<exists>x\<in>dom. y = gyr a b x"
      by (metis assms(1) assms(2) bij_betw_iff_bijections gyr_gyroaut gyroaut_def)
    moreover have "\<forall>y\<in>dom. \<exists>x\<in>dom. y = (gyr a (\<ominus> (\<ominus>b \<ominus>\<^sub>b a))) x"
      using assms(1) assms(2) ax1 bij_betw_iff_bijections gyr_gyroaut gyroaut_def gyrominus_closed
    proof -
      { fix aa :: 'a
        have "\<forall>f. bij_betw f dom dom \<or> \<not> gyroaut f"
          using gyroaut_def by blast
        then have "aa \<notin> dom \<or> aa \<notin> dom \<or> (\<exists>ab. aa = gyr a (\<ominus> (\<ominus> b \<ominus>\<^sub>b a)) ab \<and> ab \<in> dom)"
          by (smt (z3) assms(1) assms(2) ax1 bij_betw_iff_bijections gyr_gyroaut gyrominus_closed) }
      then show ?thesis
        by blast
    qed
    moreover obtain "y1" where "y1 =  gyr a b x \<and> y1\<in>dom"
      by (simp add: \<open>x \<in> dom\<close> assms(1) assms(2) gyr_def_closed)
    moreover obtain "y2" where "y2 = (gyr a (\<ominus> (\<ominus>b \<ominus>\<^sub>b a))) x \<and> y2 \<in> dom"
      by (simp add: \<open>x \<in> dom\<close> assms(1) assms(2) ax1 gyr_def_closed gyrominus_closed)
    moreover have "x = inv_into dom (gyr a b) y1"
      by (metis \<open>x \<in> dom\<close> assms(1) assms(2) calculation(6) f_inv_into_f gyr_inj image_eqI inv_into_into)
    moreover have "x = inv_into dom (gyr a (\<ominus> (\<ominus>b \<ominus>\<^sub>b a))) y2"
        by (metis \<open>x \<in> dom\<close> assms(1) assms(2) ax1 bij_betw_inv_into_left calculation(7) gyr_gyroaut gyroaut_def gyrominus_closed)
      moreover have "y1=y2"
        by (metis assms(1) assms(2) calculation(3) calculation(4) calculation(6) calculation(7) calculation(9) comp_def gyr_aut_inv_3 gyr_auto_id2)

      moreover have "gyr a b x = (gyr a (\<ominus> (\<ominus>b \<ominus>\<^sub>b a))) x"
        using calculation(10) calculation(6) calculation(7) by fastforce
      moreover have " (gyr a (\<ominus> (\<ominus>b \<ominus>\<^sub>b a))) x =  (gyr (\<ominus>a) (\<ominus>b \<ominus>\<^sub>b a)) x"
        using \<open>x \<in> dom\<close> assms(1) assms(2) calculation(11) gyr_2 by force 
      ultimately show ?thesis 
        by meson
    qed
qed
    
text \<open>Thm 2.27, (2.92)\<close>
lemma gyr_even:
   assumes "a\<in>dom" "b\<in>dom"
   shows "\<forall>x\<in>dom.(gyr (\<ominus> a) (\<ominus> b) x = gyr a b x)"
proof-
  obtain "c" where "c\<in>dom \<and> b = \<ominus> (\<ominus>c \<ominus>\<^sub>b a)"
    by (metis assms(1) assms(2) ax1 cogyro_right_cancel' cogyrominus_closed gyro_inv_idem gyrominus_def)
  moreover have "\<ominus> b =(\<ominus>c \<ominus>\<^sub>b a)"
      using assms(1) ax1 calculation gyro_inv_idem gyrominus_closed by blast
    ultimately show ?thesis 
      by (simp add: assms(1) thm2_27_help)
qed

text \<open>Thm 2.27, (2.93)\<close>
lemma inv_gyr_sym:
   assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. (inv_into dom) (gyr a b) x = gyr b a x"
  by (simp add: assms(1) assms(2) gyr_even inv_gyr)

text \<open>Thm 2.27, (2.94a)\<close>
lemma gyr_nested_3:
   assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. gyr b (\<ominus> (gyr b a a)) x = gyr a b x"
  using gyr_aut_inv_1 inv_gyr_sym
  by (metis assms(1) assms(2))

text \<open>Thm 2.27, (2.94b)\<close>
lemma gyr_nested_4:
   assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. gyr b (gyr b (\<ominus> a) a) x = gyr a (\<ominus> b) x"
  by (smt (z3) assms(1) assms(2) ax1 gyr_def_closed gyr_nested_3 gyro_inv_idem inv_gyr inv_gyr_sym)
text \<open>Thm 2.27, (2.94c)\<close>
lemma gyr_nested_5:
   assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. gyr (\<ominus> (gyr a b b)) a x= gyr a b x"
  by (smt (z3) assms(1) assms(2) ax1 gyr_3 gyr_def gyr_inv_3 gyro_right_id gyro_rigth_inv gyrogroup.gyr_left_loop gyrogroup_axioms gyroplus_closed)

text \<open>Thm 2.27, (2.94d)\<close>
lemma gyr_nested_6:
   assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. gyr (gyr a (\<ominus> b) b) a x = gyr a (\<ominus> b) x"
  by (metis assms(1) assms(2) gyr_inv_3 gyr_nested_5 gyro_inv_idem gyrogroup.ax1 gyrogroup_axioms)

text \<open>Thm 2.28, (i)\<close>
lemma gyro_right_assoc:
   assumes "a\<in>dom" "b\<in>dom" "c\<in>dom"
   shows "(a \<oplus> b) \<oplus> c = a \<oplus> (b \<oplus> gyr b a c)"
proof-
  have "a \<oplus> (b \<oplus> gyr b a c) = (a\<oplus>b) \<oplus> gyr a b (gyr b a c)"
    by (simp add: assms(1) assms(2) assms(3) gyr_def_closed gyro_left_assoc)
  then show ?thesis
    using assms(1) assms(2) assms(3) gyr_aut_inv_3 gyr_auto_id2 gyr_def_closed inv_gyr_sym by auto
qed

text \<open>Thm 2.28, (ii)\<close>
lemma gyr_right_loop:
   assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. (gyr a b x = gyr a (b \<oplus> a) x)"
  using assms(1) assms(2) gyr_aut_inv_3 inv_gyr_sym by auto

text \<open>Thm 2.29, (a)\<close>
lemma gyr_left_coloop:
   assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. gyr a b x= gyr (a \<ominus>\<^sub>c\<^sub>b b) b x"
  by (simp add: assms(1) assms(2) cogyro_right_cancel' cogyrominus_closed gyr_left_loop)
text \<open>Thm 2.29, (b)\<close>
lemma gyr_rigth_coloop:
   assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. gyr a b x = gyr a (b \<ominus>\<^sub>c\<^sub>b a) x"
  by (simp add: assms(1) assms(2) cogyro_right_cancel' cogyrominus_closed gyr_right_loop)

text \<open>Thm 2.30, (2.101a)\<close>
lemma gyr_misc_1:
   assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. gyr (a \<oplus> b) (\<ominus> a) x = gyr a b x"
  by (metis assms(1) assms(2) gyr_3 gyr_even gyro_inv_idem gyrogroup.ax1 gyrogroup_axioms gyroplus_closed)

text \<open>Thm 2.30, (2.101b)\<close>
lemma gyr_misc_2:
   assumes "a\<in>dom" "b\<in>dom"
  shows "\<forall>x\<in>dom. gyr (\<ominus> a) (a \<oplus> b) x = gyr b a x"
  using assms(1) assms(2) gyr_aut_inv_2 inv_gyr_sym by force

text \<open>Thm 2.31, (2.103)\<close>
lemma coautomorphic_inverse:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<ominus> (a \<oplus>\<^sub>c b) = (\<ominus> b) \<oplus>\<^sub>c (\<ominus> a)"
  by (smt (verit, ccfv_SIG) assms(1) assms(2) ax1 cogyrominus_def cogyroplus_closed gyro_equation_left gyro_inv_idem gyro_left_cancel')

text \<open>Thm 2.32, (2.105a)\<close>
lemma gyr_misc_3:
   assumes "a\<in>dom" "b\<in>dom"
  shows "gyr a b b = \<ominus> (\<ominus> (a \<oplus> b) \<oplus> a)"
  by (metis assms(1) assms(2) gyr_def gyr_inv_3 gyro_inv_idem gyro_is_left_inv gyro_is_left_inv_def gyro_right_id)
text \<open>Thm 2.32, (2.105b)\<close>
lemma gyr_misc_4: 
   assumes "a\<in>dom" "b\<in>dom"
  shows "gyr a (\<ominus> b) b = \<ominus> (a \<ominus>\<^sub>b b) \<oplus> a"
  by (simp add: assms(1) assms(2) ax1 gyr_def gyrominus_def)

text \<open>Thm 2.35, (2.124)\<close>
lemma mixed_gyroassoc_law: 
  assumes "c\<in>dom" "a\<in>dom" "b\<in>dom"
  shows"(a \<oplus>\<^sub>c b) \<oplus> c = a \<oplus> gyr a (\<ominus> b) (b \<oplus> c)"
  by (smt (z3) assms(1) assms(2) assms(3) ax1 cogyroplus_def gyr_distrib gyro_right_assoc gyrogroup.gyr_misc_4 gyrogroup.gyr_nested_6 gyrogroup_axioms gyrominus_closed gyroplus_closed)
(* ------------------------------------------------- *)

text \<open>Thm 3.2\<close>
lemma gyrocommute_iff_gyroatomorphic_inverse:
  shows "(\<forall> a b.((a\<in>dom\<and>b\<in>dom)\<longrightarrow> \<ominus> (a \<oplus> b) = \<ominus> a \<ominus>\<^sub>b b)) \<longleftrightarrow> ((\<forall> a b. (a\<in>dom\<and>b\<in>dom) \<longrightarrow> a\<oplus>b = gyr a b (b \<oplus> a)))"
  by (smt (verit) gyr_even gyro_inv_idem gyrogroup.ax1 gyrogroup.gyrominus_closed gyrogroup_axioms gyrominus_def gyroplus_inv)

lemma surjective_gyr_lemma_3_3:
  assumes "b\<in>dom"
  shows "\<forall>x\<in>dom. \<exists>a\<in>dom. x=gyr b (\<ominus>a) a"
  by (metis assms comp_apply gyr_def_closed gyr_nested_2)

lemma cogyro_commute_iff_gyrocommute: 
   "(\<forall> a b. (a\<in>dom\<and>b\<in>dom \<longrightarrow> a \<oplus>\<^sub>c b = b \<oplus>\<^sub>c a)) \<longleftrightarrow> (\<forall> a b.(a\<in>dom\<and>b\<in>dom\<longrightarrow>  a\<oplus>b = gyr a b (b \<oplus> a)))"
proof
  show "\<forall>a b. a \<in> dom \<and> b \<in> dom \<longrightarrow> a \<oplus>\<^sub>c b = b \<oplus>\<^sub>c a \<Longrightarrow>
    \<forall>a b. a \<in> dom \<and> b \<in> dom \<longrightarrow> a \<oplus> b = gyr a b (b \<oplus> a)"
  proof-
  assume "(\<forall> a b. (a\<in>dom\<and>b\<in>dom \<longrightarrow> a \<oplus>\<^sub>c b = b \<oplus>\<^sub>c a))"
  show "(\<forall> a b.(a\<in>dom\<and>b\<in>dom\<longrightarrow>  a\<oplus>b = gyr a b (b \<oplus> a)))"
  proof-
    have "\<forall>a b. (a\<in>dom\<and>b\<in>dom \<longrightarrow>a \<oplus>\<^sub>c b = \<ominus> (\<ominus>b \<ominus>\<^sub>b (gyr b (\<ominus>a) a)))"
    by (metis ax1 coautomorphic_inverse cogyrominus cogyrominus_def gyr_even gyro_inv_idem)
  moreover have "\<forall>a b. (a\<in>dom\<and>b\<in>dom \<longrightarrow> b\<oplus>\<^sub>c a = b \<oplus> gyr b (\<ominus>a) a)"
    using cogyroplus_def by force
  moreover have "\<forall>a b. (a\<in>dom\<and>b\<in>dom \<longrightarrow> \<ominus> (\<ominus>b \<ominus>\<^sub>b (gyr b (\<ominus>a) a)) =  b \<oplus> gyr b (\<ominus>a) a)"
    using \<open>\<forall>a b. a \<in> dom \<and> b \<in> dom \<longrightarrow> a \<oplus>\<^sub>c b = b \<oplus>\<^sub>c a\<close> calculation(1) cogyroplus_def by auto
  moreover have "\<forall> a b.((a\<in>dom\<and>b\<in>dom)\<longrightarrow> \<ominus> (a \<oplus> b) = \<ominus> a \<ominus>\<^sub>b b)"
    by (smt (verit) ax1 calculation(3) gyro_inv_idem gyrominus_def surjective_gyr_lemma_3_3)
  ultimately show ?thesis
    using gyrocommute_iff_gyroatomorphic_inverse by blast
qed
qed

next
    show "\<forall>a b. a \<in> dom \<and> b \<in> dom \<longrightarrow> a \<oplus> b = gyr a b (b \<oplus> a) \<Longrightarrow>
    \<forall>a b. a \<in> dom \<and> b \<in> dom \<longrightarrow> a \<oplus>\<^sub>c b = b \<oplus>\<^sub>c a"
      by (smt (z3) ax1 cogyro_right_cancel' cogyrominus_def cogyroplus_closed gyro_inv_idem gyro_left_cancel' gyro_right_cancel'_dual gyrocommute_iff_gyroatomorphic_inverse gyroplus_closed)
  qed

(*
text \<open>Thm 3.4\<close>
lemma cogyro_commute_iff_gyrocommute: 
   "(\<forall> a b. a \<oplus>\<^sub>c b = b \<oplus>\<^sub>c a) \<longleftrightarrow> (\<forall> a b. a\<oplus>b = gyr a b (b \<oplus> a))" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  have "\<forall> a b. a \<oplus>\<^sub>c b = b \<oplus>\<^sub>c a \<longleftrightarrow> \<ominus> (\<ominus>b \<ominus>\<^sub>b gyr b (\<ominus> a) a) = b \<oplus> gyr b (\<ominus> a) a"
    by (metis coautomorphic_inverse cogyroplus_def gyr_even gyr_inv_3 gyro_inv_idem gyrominus_def)
  thus ?thesis
    by (smt (verit, ccfv_threshold) cogyroplus_def gyr_even gyro_equation_right gyro_inv_idem gyrominus_def gyro_right_cancel'_dual gyroplus_inv)
qed
*)
end

locale gyrocommutative_gyrogroup = gyrogroup + 
  assumes gyro_commute: "\<forall>a\<in>dom.\<forall>b\<in>dom. (a \<oplus> b = gyr a b (b \<oplus> a))"
begin

lemma gyroautomorphic_inverse:
  assumes "a\<in>dom" "b\<in>dom"
  shows "\<ominus> (a \<oplus> b) = \<ominus> a \<ominus>\<^sub>b b"
  using gyro_commute gyrocommute_iff_gyroatomorphic_inverse 
  using assms(1) assms(2) by blast

lemma cogyro_commute:
  assumes "a\<in>dom" "b\<in>dom"
  shows "a \<oplus>\<^sub>c b = b \<oplus>\<^sub>c a"
  using assms(1) assms(2) cogyro_commute_iff_gyrocommute gyro_commute by blast

text \<open>Thm 3.5 (3.15)\<close>
lemma gyr_commute_misc_2:
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom"
  shows "\<forall>x\<in>dom. ((gyr a b \<circ> gyr (b \<oplus> a) c) x  = (gyr a (b \<oplus> c) \<circ> gyr b c)x)"
  by (metis assms(1) assms(2) assms(3) gyr_gyroaut gyr_nested_1 gyro_commute gyroaut_gyr_commute_lemma gyroplus_closed)

(*
text \<open>Thm 3.6 (3.17, 3.18)\<close>
lemma gyr_parallelogram:
  assumes "d = (b \<oplus>\<^sub>c c) \<ominus>\<^sub>b a"
  shows "gyr a (\<ominus> b) \<circ> gyr b (\<ominus> c) \<circ> gyr c (\<ominus> d) = gyr a (\<ominus> d)"
proof-
  have *: "\<forall> a' b' c'. gyr a' (b' \<oplus> a') \<circ> gyr (b' \<oplus> a') c' = gyr a' (b' \<oplus> c') \<circ> gyr (b' \<oplus> c') c'"
    using gyr_commute_misc_2 gyr_left_loop gyr_right_loop
    by auto
  let ?a' = "\<ominus> c"
  let ?c' = "\<ominus> a"
  let ?b' = "b \<ominus>\<^sub>c\<^sub>b ?a'"

  have "?b' \<oplus> ?c' = d"
    by (simp add: assms cogyrominus_def gyrominus_def)
  moreover
  have "b \<ominus>\<^sub>c\<^sub>b \<ominus> c \<oplus> \<ominus> c = b"
    by (simp add: cogyro_right_cancel')
  ultimately
  have "gyr (\<ominus> c) b \<circ> gyr b (\<ominus> a) = gyr (\<ominus> c) d \<circ> gyr d (\<ominus> a)"
    using  *[rule_format, of "?a'" "?b'" "?c'"]
    by simp
  then show ?thesis
    by (smt bij_is_inj gyroaut_def gyr_gyroaut inv_gyr_sym gyr_even gyro_inv_idem o_inv_distrib o_inv_o_cancel)
qed

text \<open>Thm 3.8 (3.23, 3.24)\<close>
lemma gyr_parallelogram_iff:
  "d = (b \<ominus>\<^sub>c\<^sub>b c) \<ominus>\<^sub>b a \<longleftrightarrow> \<ominus>c \<oplus> d = gyr c (\<ominus>b) (b \<ominus>\<^sub>b a)"
  oops
*)

text \<open>Thm 3.9 (3.26)\<close>
lemma gyr_commute_misc_3:
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom"
  shows "gyr a b (b \<oplus> (a \<oplus> c)) = (a \<oplus> b) \<oplus> c"
  using gyr_distrib gyro_commute gyro_left_assoc gyro_right_assoc
  by (smt (verit, ccfv_threshold) assms(1) assms(2) assms(3) gyr_def_closed gyroplus_closed)


text \<open>Thm 3.10 (3.28)\<close>
lemma gyro_left_right_cancel:
  assumes "a\<in>dom" "b\<in>dom"
shows "(a \<oplus> b) \<ominus>\<^sub>b a = gyr a b b"
  by (metis assms(1) assms(2) gyr_commute_misc_3 gyro_right_id gyro_rigth_inv gyrogroup.ax1 gyrogroup_axioms gyrominus_def)
text \<open>Thm 3.11 (3.29)\<close>
lemma cogyro_plus_def:
  assumes "a\<in>dom" "b\<in>dom"
  shows "a \<oplus>\<^sub>c b = a \<oplus> ((\<ominus> a \<oplus> b) \<oplus> a)"
  by (metis assms(1) assms(2) ax1 cogyroplus_def gyr_even gyro_inv_idem gyro_left_right_cancel gyrominus_def)
text \<open>Thm 3.12 (3.31)\<close>
lemma cogyro_commute_misc1:
  assumes "a\<in>dom" "b\<in>dom"
  shows "a \<oplus>\<^sub>c (a \<oplus> b) = a \<oplus> (b \<oplus> a)"
  by (simp add: assms(1) assms(2) cogyro_plus_def local.gyro_left_cancel' local.gyroplus_closed)
text \<open>Thm 3.13 (3.33b)\<close>
lemma gyro_translation_2b:
  assumes "a\<in>dom" "b\<in>dom" "c\<in>dom"
  shows "(a \<oplus> b) \<ominus>\<^sub>b (a \<oplus> c) = gyr a b (b \<ominus>\<^sub>b c)"
  by (smt (verit, del_insts) assms(1) assms(2) assms(3) gyroautomorphic_inverse local.ax1 local.gyr_inv_3 local.gyro_inv_idem local.gyro_translation_2a local.gyroplus_closed)




(*
text \<open>Thm 3.14 (3.34)\<close>

text \<open>(3.37)\<close>
lemma gyr_commute_misc_4':
  shows "gyr a (b \<oplus> c) = gyr a b \<circ> gyr (b \<oplus> a) c \<circ> gyr c b"
proof-
  have "gyr a b \<circ> gyr (b \<oplus> a) c = gyr (a \<oplus> b) (gyr a b c) \<circ> gyr a b"
    by (simp add: gyr_commute_misc_2 local.gyr_nested_1)
  hence "gyr a (b \<oplus> c) \<circ> gyr b c = gyr a b \<circ> gyr (b \<oplus> a) c"
    by (simp add: gyr_commute_misc_2)
  thus ?thesis
    by (metis comp_assoc comp_id local.gyr_auto_id2 local.gyr_right_loop)
qed

text \<open>(3.38)\<close>
lemma gyr_commute_misc_4'':
  shows "gyr (\<ominus>b \<oplus> d) (b \<oplus> c) = gyr (\<ominus> b) d \<circ> gyr d c \<circ> gyr c b"
  by (metis gyr_commute_misc_4' local.gyr_misc_1 local.gyro_inv_idem local.gyro_left_cancel')

text \<open>Thm 3.14 (3.34)\<close>
lemma gyro_commute_misc_4:
  shows "gyr (\<ominus> a \<oplus> b) (a \<ominus>\<^sub>b c) = gyr a (\<ominus> b) \<circ> gyr b (\<ominus> c) \<circ> gyr c (\<ominus> a)"
  by (metis gyr_commute_misc_4' gyr_even gyr_misc_1 gyro_inv_idem gyro_left_cancel' gyrominus_def)

text \<open>Thm 3.15 (3.40)\<close>
lemma gyr_inv_2:
  shows "gyr a (\<ominus>b) = gyr (\<ominus> a \<oplus> b) (a \<oplus> b) \<circ> gyr a b"
  by (metis comp_id gyr_commute_misc_2 local.gyr_even local.gyr_id local.gyr_misc_1 local.gyro_inv_idem local.gyro_left_cancel')

text \<open>Thm 3.17 (3.48)\<close>
lemma gyr_master':
  shows "gyr a x \<circ> gyr (\<ominus> (x \<oplus> a)) (x \<oplus> b) \<circ> gyr x b = gyr (\<ominus> a) b"
  by (metis gyr_commute_misc_4' gyroautomorphic_inverse gyr_even gyr_misc_1 gyro_left_cancel' gyrominus_def)

text \<open>(3.51)\<close>
lemma gyr_master:
  shows "gyr a x \<circ> gyr (x \<oplus> a) (\<ominus> (x \<oplus> b)) \<circ> gyr x b = gyr (\<ominus> a) b"
  by (metis gyr_master' gyr_even gyro_inv_idem)

text \<open>(3.52a)\<close>
lemma gyr_master_misc1':
  shows "gyr (\<ominus> a) b = gyr (\<ominus> (a \<oplus> a)) (a \<oplus> b) \<circ> gyr a b"
  by (metis fun.map_id gyr_master' local.gyr_id)

text \<open>(3.52b)\<close>
lemma gyr_master_misc1'':
  shows "gyr (\<ominus> a) b = gyr a b \<circ> gyr (b \<oplus> a) (\<ominus> (b \<oplus> b))"
  by (metis comp_id gyr_master gyr_id)

text \<open>(3.53a)\<close>
lemma gyr_master_misc2':
  shows "gyr (\<ominus>a \<oplus> b) (a \<oplus> b) = gyr (\<ominus> a) b \<circ> gyr b a"
  by (simp add: gyr_commute_misc_4'')

text \<open>(3.53b)\<close>
lemma gyr_master_misc2'':
  shows "gyr (\<ominus>a \<oplus> b) (a \<oplus> b) = gyr (\<ominus> a \<oplus> b) b \<circ> gyr b (a \<oplus> b)"
  using gyr_master_misc2' local.gyr_left_loop local.gyr_right_loop
  by auto


text \<open>Thm 3.18 (3.60)\<close>
lemma "gyr a x \<circ> gyr (\<ominus> (gyr x a (a \<ominus>\<^sub>b b))) (x \<oplus> b) \<circ> gyr x b = gyr a (\<ominus> b)"
  by (metis gyr_master gyro_translation_2b gyr_even gyr_left_loop gyro_inv_idem gyrominus_def)

definition gyro_covariant :: "nat \<Rightarrow> ('a list \<Rightarrow> 'a) \<Rightarrow> bool" where
  "gyro_covariant n T \<longleftrightarrow> (\<forall> \<tau> xs. length xs = n \<and> gyroaut \<tau> \<longrightarrow> (\<tau> (T xs)) = T (map \<tau> xs)) \<and> 
                        (\<forall> x xs. length xs = n \<longrightarrow> x \<oplus> T xs = T (map (\<lambda> a. x \<oplus> a) xs))"

definition gyro_covariant_3 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "gyro_covariant_3 T \<longleftrightarrow> (\<forall> \<tau> a b c. gyroaut \<tau> \<longrightarrow> (\<tau> (T a b c)) = T (\<tau> a) (\<tau> b) (\<tau> c)) \<and> 
                          (\<forall> x a b c. x \<oplus> T a b c = T (x \<oplus> a) (x \<oplus> b) (x \<oplus> c))"

lemma gyro_covariant_3: 
  shows "gyro_covariant_3 T \<longleftrightarrow> gyro_covariant 3 (\<lambda> xs. T (xs ! 0) (xs ! 1) (xs ! 2))"
  unfolding gyro_covariant_3_def gyro_covariant_def
  apply safe
     apply simp
    apply simp
   apply (erule_tac x="\<tau>" in allE, erule_tac x="[a, b, c]" in allE, simp)
  apply (erule_tac x="x" in allE, erule_tac x="[a, b, c]" in allE, simp)
  done

text \<open>Thm 3.19 (3.62)\<close>
lemma gyro_covariant_3_parallelogram:                
  shows "gyro_covariant_3 (\<lambda> a b c. (b \<oplus>\<^sub>c c) \<ominus>\<^sub>b a)"  
  unfolding gyro_covariant_3_def
proof safe
  fix \<tau> a b c
  assume "gyroaut \<tau>"
  then show "\<tau> ((b \<oplus>\<^sub>c c) \<ominus>\<^sub>b a) = (\<tau> b \<oplus>\<^sub>c \<tau> c) \<ominus>\<^sub>b \<tau> a"
    by (smt (verit, ccfv_threshold) cogyroaut_def gyro_coaut_iff_gyro_aut local.gyro_left_cancel' local.gyro_left_inv local.gyroaut_def local.gyrominus_def)
next
  fix x a b c
  have "((x \<oplus> b) \<oplus>\<^sub>c (x \<oplus> c)) \<ominus>\<^sub>b (x \<oplus> a) = (x \<oplus> b) \<oplus> gyr (x \<oplus> b) (\<ominus> (x \<oplus> c)) ((x \<oplus> c) \<ominus>\<^sub>b (x \<oplus> a))"
    by (simp add: gyrominus_def mixed_gyroassoc_law)
  also have "... = (x \<oplus> b) \<oplus> gyr (x \<oplus> b) (\<ominus> (x \<oplus> c)) (gyr x c (c \<ominus>\<^sub>b a))"
    by (simp add: gyro_translation_2b)
  also have "... = x \<oplus> (b \<oplus> gyr b x (gyr (x \<oplus> b) (\<ominus> (x \<oplus> c)) (gyr x c (c \<ominus>\<^sub>b a))))"
    using local.gyro_right_assoc by auto
  also have "... = x \<oplus> (b \<oplus> gyr b x (gyr x b (gyr b (\<ominus> c) (gyr c x (gyr x c (c \<ominus>\<^sub>b a))))))"
    unfolding gyrominus_def
    using gyro_commute_misc_4[of "\<ominus> x" b c]
    by (simp add: gyroautomorphic_inverse local.gyr_even)
  also have "... = x \<oplus> (b \<oplus> gyr b (\<ominus> c) (c \<ominus>\<^sub>b a))"
    by (metis local.gyr_auto_id2 local.gyr_right_loop pointfree_idE)
  finally show "x \<oplus> ((b \<oplus>\<^sub>c c) \<ominus>\<^sub>b a) = ((x \<oplus> b) \<oplus>\<^sub>c (x \<oplus> c)) \<ominus>\<^sub>b (x \<oplus> a)"
    using gyrominus_def mixed_gyroassoc_law 
    by auto
qed

lemma gyro_commute_misc6':
  shows "x \<oplus> ((b \<oplus>\<^sub>c c) \<ominus>\<^sub>b a) = ((x \<oplus> b) \<oplus>\<^sub>c (x \<oplus> c)) \<ominus>\<^sub>b (x \<oplus> a)"
  using gyro_covariant_3_parallelogram
  unfolding gyro_covariant_3_def
  by simp
  
text \<open>(3.66)\<close>
lemma gyro_commute_misc6:
  shows "(x \<oplus> b) \<oplus>\<^sub>c (x \<oplus> c) = x \<oplus> ((b \<oplus>\<^sub>c c) \<oplus> x)"
  using gyro_commute_misc6'[of x b c "\<ominus> x"]
  by (simp add: gyrominus_def)

text \<open>(3.67)\<close>
lemma gyro_commute_misc6'':
  shows "(x \<oplus> b) \<oplus>\<^sub>c (x \<ominus>\<^sub>b b) = x \<oplus> x"
  using gyro_commute_misc6 cogyro_gyro_inv cogyro_right_inv gyro_left_id gyrominus_def 
  by presburger

end

type_synonym 'a rooted_gyrovec = "'a \<times> 'a"

context gyrogroup
begin

text \<open>Def 5.2.\<close>
fun head :: "'a rooted_gyrovec \<Rightarrow> 'a" where
  "head (p, q) = q"
fun tail :: "'a rooted_gyrovec \<Rightarrow> 'a" where
  "tail (p, q) = p"
fun val :: "'a rooted_gyrovec \<Rightarrow> 'a" where
  "val (p, q) = \<ominus> p \<oplus> q"
definition ort :: "'a \<Rightarrow> 'a rooted_gyrovec" where
  "ort p = (0\<^sub>g, p)"

fun equiv_rooted_gyro_vec (infixl "\<sim>" 100) where
  "(p, q) \<sim> (p', q') \<longleftrightarrow> \<ominus>p \<oplus> q = \<ominus>p' \<oplus> q'"

lemma equivp_equiv_rooted_gyro_vec [simp]:
  shows "equivp (\<sim>)"
  unfolding equivp_def
  by fastforce

end

text \<open>Def 5.4.\<close>
quotient_type (overloaded) 'a gyrovec = "'a :: gyrogroup \<times> 'a" / equiv_rooted_gyro_vec
  by auto
                  
lift_definition vec :: "'a::gyrogroup \<Rightarrow> 'a \<Rightarrow> 'a gyrovec" is "\<lambda> p q. (p, q)"
  done

definition ort :: "'a::gyrogroup \<Rightarrow> 'a gyrovec" where
  "ort A = vec 0\<^sub>g A"

context gyrocommutative_gyrogroup
begin

text \<open>Thm 5.5. (5.4)\<close>
lemma equiv_rooted_gyro_vec_ex_t:
  shows "(p, q) \<sim> (p', q') \<longleftrightarrow> (\<exists> t. p' = gyr p t (t \<oplus> p) \<and> q' = gyr p t (t \<oplus> q))" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  let ?t = "\<ominus>p \<oplus> p'"

  have "\<ominus>(?t \<oplus> p) \<oplus> (?t \<oplus> q) = gyr ?t p (\<ominus>p \<oplus> q)"
    by (metis gyr_def gyro_equation_right)

  hence "\<ominus>p \<oplus> q = gyr (\<ominus> p) (\<ominus> ?t) (\<ominus>(?t \<oplus> p) \<oplus> (?t \<oplus> q))"
    by (metis gyr_aut_inv_2 gyr_auto_id1 gyr_even inv_gyr_sym pointfree_idE)
  hence "\<ominus>p \<oplus> q = gyr p ?t (\<ominus>(?t \<oplus> p) \<oplus> (?t \<oplus> q))"
    using gyr_even by presburger

  show ?thesis
  proof
    assume "(p, q) \<sim> (p', q')"
    hence *: "\<ominus>p \<oplus> q = \<ominus>p' \<oplus> q'"
      by simp

    have "p' = gyr p ?t (?t \<oplus> p)" 
      using *
      using gyro_commute gyro_equation_right gyro_left_cancel by blast

    moreover

    have "q' = gyr p ?t (?t \<oplus> q)"
    proof-
      have "q' = p' \<oplus> (\<ominus> p \<oplus> q)"
        by (metis "*" gyro_left_cancel')
      also have "... = gyr p ?t (?t \<oplus> p) \<oplus> (\<ominus> p \<oplus> q)"
        using \<open>p' = gyr p (\<ominus> p \<oplus> p') (\<ominus> p \<oplus> p' \<oplus> p)\<close> 
        by auto
      also have "... = (gyr p ?t ?t \<oplus> gyr p ?t p) \<oplus> (\<ominus> p \<oplus> q)"
        by simp
      also have "... = gyr p ?t ?t \<oplus> (gyr p ?t p \<oplus> gyr (gyr p ?t p) (gyr p ?t ?t) (\<ominus> p \<oplus> q))"
        using gyro_right_assoc by blast
      also have "... = gyr p ?t ?t \<oplus> (gyr p ?t p \<oplus> gyr p ?t (\<ominus> p \<oplus> q))"
        using gyr_commute_misc_1
        by presburger
      also have "... = gyr p ?t ?t \<oplus> gyr p ?t q"
        by (metis gyr_distrib gyro_equation_right)
      finally show "q' = gyr p ?t (?t \<oplus> q)"
        by simp
    qed

    ultimately

    show ?rhs
      by blast

  next

    assume ?rhs
    then obtain t where t: "p' = gyr p t (t \<oplus> p) \<and> q' = gyr p t (t \<oplus> q)"
      by auto

    have "\<ominus> p \<oplus> q = gyr p t (\<ominus> (t \<oplus> p) \<oplus> (t \<oplus> q))"
      by (metis gyro_left_assoc gyro_left_cancel gyro_right_assoc gyro_translation_2a)
    also have "... = \<ominus> (gyr p t (t \<oplus> p)) \<oplus> gyr p t (t \<oplus> q)"
      by (simp add: gyr_inv_3)
    finally show ?lhs
      using t
      by auto
  qed
qed

text \<open>Thm 5.5. (5.5)\<close>
lemma gyro_translate_commute:
  assumes "p' = gyr p t (t \<oplus> p) \<and> q' = gyr p t (t \<oplus> q)"
  shows "t = \<ominus>p \<oplus> p'"
  using assms
  using gyro_commute gyro_equation_right by blast

text \<open>Def 5.6.\<close>
fun gyrovec_translation :: "'a \<Rightarrow> 'a rooted_gyrovec \<Rightarrow> 'a rooted_gyrovec" where
  "gyrovec_translation t (p, q) = (gyr p t (t \<oplus> p), gyr p t (t \<oplus> q))"
end

lift_definition gyrovec_translation' :: "('a::gyrocommutative_gyrogroup) gyrovec \<Rightarrow> 'a rooted_gyrovec \<Rightarrow> 'a rooted_gyrovec" is 
  "\<lambda> (tp, tq) (p, q). gyrovec_translation (\<ominus> tp \<oplus> tq) (p, q)"
  by force

text \<open>(5.14)\<close>
lemma
  shows "tail (gyrovec_translation t (p, q)) = p \<oplus> t"
  by (metis gyrovec_translation.simps gyro_commute tail.simps)

text \<open>(5.15)\<close>
lemma gyrovec_translation_id:
  shows "gyrovec_translation 0\<^sub>g (p, q) = (p, q)"
  by simp

text \<open>Thm 5.7.\<close>
lemma equiv_rooted_gyrovec_t:
  shows "(p, q) \<sim> (p', q') \<longleftrightarrow> (p', q') = gyrovec_translation (\<ominus>p \<oplus> p') (p, q)"
  using equiv_rooted_gyro_vec_ex_t gyro_translate_commute
  by (metis gyrovec_translation.simps)

text \<open>Thm 5.8.\<close>
lemma gyrovec_translation_head:
  assumes "(p', x) = gyrovec_translation t (p, q)"  
  shows "x = p' \<oplus> (\<ominus>p \<oplus> q)"
  by (metis assms equiv_rooted_gyro_vec_ex_t gyrovec_translation.simps equiv_rooted_gyro_vec.simps gyro_equation_right)

text \<open>(5.24)\<close>

context gyrocommutative_gyrogroup
begin

definition gyrovec_translation_inv' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "gyrovec_translation_inv' p t = \<ominus> (gyr p t t)"

lemma gyrovec_translation_inv':
  shows "gyrovec_translation (gyrovec_translation_inv' p t) (gyrovec_translation t (p, q)) = (p, q)"
  unfolding gyrovec_translation_inv'_def
proof -
  have f1: "\<forall>a aa. gyr (aa::'a) a (a \<oplus> aa) = aa \<oplus> a"
    by (metis (no_types) cogyro_commute cogyro_commute_iff_gyrocommute)
  have "\<forall>a aa. \<ominus> (gyr (aa::'a) a a) = \<ominus> (aa \<oplus> a) \<oplus> aa"
    by (simp add: gyr_misc_3)
  then have "\<forall>a aa ab. (ab::'a, ab \<oplus> (\<ominus> (ab \<oplus> aa) \<oplus> a)) = gyrovec_translation (\<ominus> (gyr ab aa aa)) (ab \<oplus> aa, a)"
    using f1 by (metis gyrovec_translation.simps gyr_commute_misc_3 gyro_left_cancel')
  then have "\<forall>a aa ab. gyrovec_translation (\<ominus> (gyr (ab::'a) aa aa)) (gyrovec_translation aa (ab, a)) = (ab, a)"
    using f1 by (metis gyrovec_translation.simps gyr_commute_misc_3 gyro_left_cancel')
  then show "gyrovec_translation (\<ominus> (gyr p t t)) (gyrovec_translation t (p, q)) = (p, q)"
    by blast
qed

definition gyrovec_translation_compose' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "gyrovec_translation_compose' p t1 t2 = t1 \<oplus> gyr t1 p t2"

lemma gyrovec_translation_compose':
  "gyrovec_translation t2 (gyrovec_translation t1 (p, q)) =
        gyrovec_translation (gyrovec_translation_compose' p t1 t2) (p, q)"
  by (smt (verit) comp_eq_dest_lhs gyrovec_translation_compose'_def local.gyr_auto_id2 local.gyr_commute_misc_3 local.gyr_distrib local.gyr_nested_1 local.gyr_right_loop local.gyro_commute local.gyro_right_assoc local.gyrovec_translation.simps pointfree_idE prod.inject)

fun equiv_translate (infixl "~\<^sub>t" 100) where
  "(p1, q1) ~\<^sub>t (p2, q2) \<longleftrightarrow> (\<exists> t. gyrovec_translation t (p1, q1) = (p2, q2))"

lemma equivp_equiv_translate:
  "equivp (~\<^sub>t)"
proof (rule equivpI)
  show "reflp (~\<^sub>t)"
  proof
    fix x
    show "x ~\<^sub>t x"
      by (metis equiv_translate.elims(3) gyr_commute_misc_3 gyr_id_2 gyro_left_id gyrovec_translation.simps)
  qed
next
  show "symp (~\<^sub>t)"
  proof
    fix a b
    assume "a ~\<^sub>t b"
    thus "b ~\<^sub>t a"
      using gyrovec_translation_inv' 
      by (cases a, cases b, fastforce)
  qed
next
  show "transp (~\<^sub>t)"
  proof
    fix x y z
    assume "x ~\<^sub>t y" "y ~\<^sub>t z"
    thus "x ~\<^sub>t z"
      using gyrovec_translation_compose'
      by (cases x, cases y, cases z, fastforce)
  qed
qed

text \<open>(5.39)\<close>
definition vec :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "vec a b = \<ominus> a \<oplus> b"

text \<open>(5.40)\<close>
lemma "vec 0\<^sub>g b = b"
  by (simp add: vec_def)

text \<open>(5.41)\<close>
lemma
  assumes "vec a b = v" 
  shows "b = a \<oplus> v"
  by (metis assms local.gyro_left_cancel' local.vec_def)

text \<open>(5.42)\<close>
lemma
  "(a \<oplus> v) \<oplus> u = a \<oplus> (v \<oplus> gyr v a u)"
  by (rule gyro_right_assoc)

text \<open>(5.43)\<close>
lemma
  assumes "vec a b = v"
  shows "a = \<ominus>v \<oplus>\<^sub>c b"
  using assms
  using cogyro_commute cogyrominus_def gyro_equation_left gyro_left_cancel' vec_def
  by force

lemma
  shows "(\<ominus> a \<oplus> b) \<oplus> gyr (\<ominus>a) b (\<ominus> b \<oplus> c) = \<ominus>a \<oplus> c"
  by (rule gyro_polygonal_addition_lemma)  


definition torsion_elem::"'a\<Rightarrow> bool" where
  "torsion_elem g \<longleftrightarrow> g\<oplus>g = 0\<^sub>g"

end

(*torsion_free two_divisible*)
class tf_tw_group = gyrocommutative_gyrogroup +
  assumes a1:"\<forall>a. torsion_elem a \<longrightarrow> a =  0\<^sub>g"
  assumes a2:"\<forall>a. \<exists>b. (b\<oplus>b = a)"
begin

text "T3.32"
lemma unique_half:
  shows "(a\<oplus>a = c \<and> b\<oplus>b = c) \<longrightarrow> a=b"
proof
  assume "(a\<oplus>a = c \<and> b\<oplus>b = c)"
  show "a=b"
  proof-
    have "a\<oplus>a = b\<oplus>b"
      by (simp add: \<open>a \<oplus> a = c \<and> b \<oplus> b = c\<close>)
    moreover have "\<ominus> b \<oplus> (a\<oplus>a) = \<ominus> b \<oplus> (b\<oplus>b)"
      by (simp add: \<open>a \<oplus> a = c \<and> b \<oplus> b = c\<close>)
    moreover have "\<ominus> b \<oplus> a  \<oplus> (gyr (\<ominus> b) a) a =b "
      by (metis \<open>a \<oplus> a = c \<and> b \<oplus> b = c\<close> local.gyro_left_assoc local.gyro_left_cancel')
    moreover have "\<ominus> b \<oplus> a = \<ominus> (\<ominus> b \<oplus> a)"
      by (metis calculation(3) local.gyro_plus_def_co local.gyro_right_cancel'_dual local.gyroautomorphic_inverse)
    moreover have "\<ominus> b \<oplus> a  \<oplus> ( \<ominus> b \<oplus> a) =  0\<^sub>g"
      by (metis calculation(4) local.gyro_rigth_inv)
    moreover have " torsion_elem (\<ominus> b \<oplus> a)"
      using calculation(5) local.torsion_elem_def by blast
    moreover have "( \<ominus> b \<oplus> a) = 0\<^sub>g"
      using a1
      using calculation(6) by blast
    ultimately show ?thesis 
      by (metis local.gyro_left_inv local.oplus_ominus_cancel)
  qed
qed

text "T3.33"
lemma unique_gyro_half:
  assumes "gh\<oplus>gh = g"
      "gyr_h \<oplus> gyr_h = gyr a b g"
    shows "gyr a b gh = gyr_h"
  by (metis assms(1) assms(2) local.gyr_distrib unique_half)

text "3.102"
lemma gh_minus:
  assumes "gh\<oplus>gh = \<ominus> g"
        "gh2\<oplus>gh2 = g"
      shows " \<ominus> gh2 = gh"
  by (metis assms(1) assms(2) local.gyroautomorphic_inverse local.gyrominus_def unique_half)

text "T3.34"
lemma gyration_exclusion:
  assumes "\<exists>g. g\<noteq> 0\<^sub>g"
  shows "\<forall>a b.  gyr a b \<noteq>  \<ominus> \<circ> id"
proof(rule ccontr)
  assume "\<not> (\<forall>a b.  gyr a b \<noteq>  \<ominus> \<circ> id)"
  have "\<exists>a b.( gyr a b =  \<ominus> \<circ> id)"
    using \<open>\<not> (\<forall>a b. gyr a b \<noteq> \<ominus> \<circ> id)\<close> by auto
  
  moreover obtain "a" "b" where "gyr a b  = \<ominus>  \<circ> id "
    using calculation by blast
  moreover obtain "bh" where "bh \<oplus> bh = b"
    using a2
    by blast
  moreover have "a \<oplus> (b \<ominus>\<^sub>b bh) = (a  \<oplus> b)  \<oplus> bh "
  proof-
    have "a \<oplus> (b \<ominus>\<^sub>b bh) =  (a  \<oplus> b) \<ominus>\<^sub>b  gyr a b bh "
      by (simp add: local.gyr_inv_3 local.gyro_left_assoc local.gyrominus_def)
    moreover obtain "gh" where "gh \<oplus> gh =  gyr a b b"
      using local.a2 by blast
    moreover have "a \<oplus> (b \<ominus>\<^sub>b bh) = (a  \<oplus> b) \<ominus>\<^sub>b  gh"
      using \<open>bh \<oplus> bh = b\<close> calculation(1) calculation(2) unique_gyro_half by blast
    ultimately show ?thesis 
      by (simp add: \<open>gyr a b = \<ominus> \<circ> id\<close> local.gyrominus_def) 
  qed
  moreover have "a \<oplus> (b \<ominus>\<^sub>b bh) = a  \<oplus> bh"
    using calculation(3) local.gyro_left_right_cancel by force
  moreover have "b =  0\<^sub>g"
    by (metis calculation(4) calculation(5) local.cogyro_gyro_inv local.cogyroinv_def local.gyro_equation_left local.gyro_equation_right)
  moreover have "gyr a b = id"
    by (simp add: calculation(6))
  moreover have "gyr a b  = \<ominus>  \<circ> id "
    using calculation(2) by blast
  ultimately show False
    by (metis assms comp_id id_def local.gyro_rigth_inv unique_gyro_half)
qed

text "T3.35"
lemma gyration_exclusion_cons:
  shows "gyr a b b =  \<ominus> b \<longrightarrow> b = 0\<^sub>g"
proof
  assume "gyr a b b =  \<ominus> b "
  show "b = 0\<^sub>g"
  proof-
   obtain "bh" where "bh \<oplus> bh = b"
    using a2
    by blast
  moreover have "a \<oplus> (b \<ominus>\<^sub>b bh) = (a  \<oplus> b)  \<oplus> bh "
  proof-
    have "a \<oplus> (b \<ominus>\<^sub>b bh) =  (a  \<oplus> b) \<ominus>\<^sub>b  gyr a b bh "
      by (simp add: local.gyr_inv_3 local.gyro_left_assoc local.gyrominus_def)
    moreover obtain "gh" where "gh \<oplus> gh =  gyr a b b"
      using local.a2 by blast
    moreover have "a \<oplus> (b \<ominus>\<^sub>b bh) = (a  \<oplus> b) \<ominus>\<^sub>b  gh"
      using \<open>bh \<oplus> bh = b\<close> calculation(1) calculation(2) unique_gyro_half by blast
    ultimately show ?thesis 
      by (metis \<open>bh \<oplus> bh = b\<close> \<open>gyr a b b = \<ominus> b\<close> gh_minus local.gyro_inv_idem local.gyrominus_def)
  qed
  moreover have "a \<oplus> (b \<ominus>\<^sub>b bh) = a  \<oplus> bh"
    using calculation(1) local.gyro_left_right_cancel by force
  ultimately show ?thesis 
    by (metis local.gyr_right_loop local.gyro_commute local.gyro_left_cancel local.gyro_right_id)
qed
qed

text "T3.36"
lemma equation_t3_36:
  shows " x  \<ominus>\<^sub>b (y  \<ominus>\<^sub>b x) = y \<longleftrightarrow> x = y"
  by (metis gyration_exclusion_cons local.gyr_commute_misc_3 local.gyr_misc_1 local.gyr_misc_3 local.gyro_right_id local.gyro_rigth_inv local.gyrominus_def)



end
*)


end




end
