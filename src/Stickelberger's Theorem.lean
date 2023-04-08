import number_theory.cyclotomic.gal

 variables (m : ℕ+) (F : Type ) [field F][algebra ℚ F] [is_cyclotomic_extension {m} ℚ F]

open_locale big_operators 
noncomputable theory 

def monoid_algebra_ring_hom_map (G : Type ) [ group G ] (R : Type) [comm_ring R] (S:Type) [comm_ring S] 
  [algebra R S]  : monoid_algebra R G →ₐ[R] monoid_algebra S G :=  monoid_algebra.lift R G (monoid_algebra S G) (monoid_algebra.of S G) 

def Stickelberger_Element : monoid_algebra ℚ (F ≃ₐ[ℚ] F ) := ∑ i : (zmod m)ˣ ,finsupp.single (( is_cyclotomic_extension.aut_equiv_pow F  $ polynomial.cyclotomic.irreducible_rat m.2 ).symm i)⁻¹ ( ((i : zmod m).val : ℚ) / (m : ℚ))        

def is_in_Stickelberger_Ideal (a : monoid_algebra ℤ (F ≃ₐ[ℚ] F ) ) : Prop := 
∃ (b : monoid_algebra ℚ (F ≃ₐ[ℚ] F ) ) , b * Stickelberger_Element m F = monoid_algebra_ring_hom_map (F ≃ₐ[ℚ] F ) ℤ ℚ a 

def Stickelberger_Ideal : ideal (monoid_algebra ℤ (F ≃ₐ[ℚ] F ) ) := { carrier := { r | is_in_Stickelberger_Ideal m F r  },
  add_mem' := 
  begin 
    intros x y hx hy,
    cases hx with b hb,
    cases hy with c hc,
    use b + c,
    rw[add_mul],
    simp only [map_add],
    rw[hb,hc],
  end
  ,
  zero_mem' := 
  begin 
    use 0, 
    rw zero_mul, 
    rw map_zero,
  end
  ,
  smul_mem' := 
  begin
    intros r x hx,
    cases hx with b hb,
    simp only [smul_eq_mul, set.mem_set_of_eq], 
    rw[is_in_Stickelberger_Ideal],
    use (monoid_algebra_ring_hom_map (F ≃ₐ[ℚ] F ) ℤ ℚ r)* b,
    rw[mul_assoc,hb,map_mul],
  end

   } 

   