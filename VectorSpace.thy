theory VectorSpace
  imports Main HOL.Real "HOL-Types_To_Sets.Linear_Algebra_On_With"

begin

locale vector_space_with_domain =
  fixes dom :: "'a set"
    and add :: "'a ⇒ 'a ⇒ 'a"      
    and zero :: "'a"
    and smult :: "real ⇒ 'a ⇒ 'a"   
  assumes add_closed: "⟦x ∈ dom; y ∈ dom⟧ ⟹ add x y ∈ dom" 
    and zero_in_dom: "zero ∈ dom"      
    and add_assoc: "⟦x ∈ dom; y ∈ dom; z∈ dom⟧ ⟹add (add x y) z = add x (add y z)"
    and add_comm: "⟦x ∈ dom; y ∈ dom⟧ ⟹ add x y = add y x"
    and add_zero: "⟦x ∈ dom⟧ ⟹ add x zero = x"
    and add_inv: "x ∈ dom ⟹ ∃y ∈ dom. add x y = zero"
    and smult_closed: "⟦x ∈ dom⟧ ⟹ smult a x ∈ dom"
    and smult_distr_sadd: "⟦x ∈ dom⟧ ⟹smult (a + b) x = add (smult a x) (smult b x)"
    and smult_assoc: "⟦x ∈ dom⟧ ⟹ smult a  (smult b x) = smult (a * b)  x"
    and smult_one: "⟦x ∈ dom⟧ ⟹ smult 1 x = x" 
    and smult_distr_sadd2: "⟦x ∈ dom; y∈dom⟧ ⟹ smult a (add x y) = add (smult a x) (smult a y)"

begin

lemma inv_unique:
  assumes "a∈dom" "z1∈dom" "z2∈dom"
      "add a z1 = zero"
      "add a z2 = zero"
    shows "z1=z2"
  by (metis add_assoc add_comm add_zero assms)

definition inv::"'a⇒'a" where 
    "inv a = (if a∈dom then (THE z. (z∈dom ∧ add a z = zero)) else undefined)"

definition minus::"'a⇒'a⇒'a" where
    "minus a b = (if a∈dom ∧ b∈dom then add a (inv b) else undefined)"

lemma module_on_with_is_this:
  shows "module_on_with dom add minus inv zero smult"
  unfolding module_on_with_def
proof
  show "ab_group_add_on_with dom add zero local.minus local.inv"
    unfolding ab_group_add_on_with_def
  proof
    show "comm_monoid_add_on_with dom add zero"
      by (smt (verit, del_insts) ab_semigroup_add_on_with_Ball_def add_assoc add_closed add_comm add_zero comm_monoid_add_on_with_Ball_def semigroup_add_on_with_def zero_in_dom)
    next
    show "ab_group_add_on_with_axioms dom add zero local.minus local.inv"
      unfolding ab_group_add_on_with_axioms_def
    proof
      show "∀a. a ∈ dom ⟶ add (local.inv a) a = zero"
      proof-
        {fix a 
          assume "a∈dom"
          obtain "z" where "z∈dom ∧ add z a = zero"
            using ‹a ∈ dom› add_comm add_inv by blast
          moreover have "local.inv a = z"
            using ‹a ∈ dom› add_comm calculation inv_unique local.inv_def by auto
          ultimately have " add (local.inv a) a = zero"
          using `a∈dom`
          by fastforce
          
      }
      show ?thesis 
        using ‹⋀aa. aa ∈ dom ⟹ add (local.inv aa) aa = zero› by blast
    qed
  next
    show " (∀a b. a ∈ dom ⟶ b ∈ dom ⟶ local.minus a b = add a (local.inv b)) ∧
    (∀a. a ∈ dom ⟶ local.inv a ∈ dom)"
    proof
      show "∀a b. a ∈ dom ⟶ b ∈ dom ⟶ local.minus a b = add a (local.inv b)"
        using minus_def by auto
    next
      show "∀a. a ∈ dom ⟶ local.inv a ∈ dom"
      proof-
        {fix a 
        assume "a∈dom"
        have "local.inv a ∈dom"
          by (smt (z3) ‹a ∈ dom› add_assoc add_comm add_inv add_zero local.inv_def theI')
      }
      show ?thesis 
        using ‹⋀aa. aa ∈ dom ⟹ local.inv aa ∈ dom› by fastforce
        qed
      qed
  qed  
  qed
next
  show " ((∀a. ∀x∈dom. ∀y∈dom. smult a (add x y) = add (smult a x) (smult a y)) ∧
     (∀a b. ∀x∈dom. smult (a + b) x = add (smult a x) (smult b x))) ∧
    (∀a b. ∀x∈dom. smult a (smult b x) = smult (a * b) x) ∧
    (∀x∈dom. smult 1 x = x) ∧ (∀a. ∀x∈dom. smult a x ∈ dom)"
    using smult_one smult_distr_sadd smult_assoc smult_closed
      smult_distr_sadd2
    by auto
qed

lemma vector_space_on_with_is_this:
  shows "vector_space_on_with dom add minus inv zero smult"
  by (simp add: module_on_with_is_this vector_space_on_with_def)

lemma zero_smult:
  assumes "x\<in> dom"
  shows "smult 0 x = zero"
  by (smt (verit, best) add_assoc add_inv add_zero assms smult_closed
      vector_space_with_domain.smult_distr_sadd vector_space_with_domain_axioms)
  
end

locale one_dim_vector_space_with_domain =
  vector_space_with_domain + 
  assumes "∀y. ∀x. (y∈ dom ∧
 x∈ dom ∧ x≠zero ⟶ (∃!r::real. y = smult r x))"

end
