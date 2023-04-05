import number_theory.legendre_symbol.add_character
import number_theory.legendre_symbol.zmod_char
import algebra.char_p.char_and_card
import field_theory.finite.trace 
import number_theory.cyclotomic.basic
import data.zmod.basic
import ring_theory.roots_of_unity
import algebra.group_power.basic
import data.complex.basic
import analysis.normed.field.basic
import data.pnat.defs
import algebra.ring.defs
noncomputable theory
/-!
# Modified Gauss sums

We define the Gauss sum associated to a multiplicative and an additive
character of a finite field and prove some results about them.

## Main definition


Here, let 𝔽 = 𝔽_q be a finite field with q elements(q = p^f ) and let χ ζ_p be a fixed primitive root of unity and let T be the trace from 𝔽 to 
ℤ/pℤ. Define  
 ψ : 𝔽 → ℂ^× , ψ(x) = ζ_p^T(x)
 and now we define χ as a multiplicative character with these domains. 
 𝔽^× → ℂ^×     
We extend χ to all of 𝔽 by setting χ(0) = 0(even if χ is a trivial character).  
-/ 
open add_char 
open zmod
open mul_char
open_locale big_operators
open_locale classical
open_locale complex_conjugate
universes u v w
-- variables (f : ℕ)
variables {F : Type u} [field F] [fintype F] (ζ_p : ℂ) ( h0 : (is_primitive_root ζ_p (ring_char F)) )
/-- Definition of the Gauss sum associated to a multiplicative and an additive character. -/
-- structure add_char' extends add_char F ℂˣ:=
-- (ψ : F → ℂˣ )
-- (ζ_p: is_primitive_root )
-- (ψ_eq : ∀ x : F, ψ x = (ψ 1) ^ (trace x))



def add_char'(x : F) : ℂ  :=
  ζ_p^( zmod.val (algebra.trace (zmod (ring_char F)) F x))
  

def gauss_sum' (χ : mul_char F ℂ ) : ℂ := ∑ x : F,  -(add_char' ζ_p x)* (χ x)



instance char_p_non_zero : ne_zero (ring_char F) :=
{out :=  begin
  intro h,
  haveI : fact (ring_char F).prime := ⟨char_p.char_is_prime F _⟩,
  exact nat.prime.ne_zero (fact.out (ring_char F).prime) h,
end}

-- /-- Primitive root's Proprty on NMod -/
-- lemma ζ_p_helper_help (n : ℤ ): ζ_p^((n % (ring_char F)) ) = ζ_p^(n) := by
-- begin
--   rw ←  mul_inv_eq_one, 
--   rw ← zpow_neg ζ_p n, 
--   rw ← zpow_add ζ_p,  
--   rw  is_primitive_root.zpow_eq_one_iff_dvd (fact.out (is_primitive_root ζ_p (ring_char F))) ,
--   rw ← int.modeq_zero_iff_dvd,
--   have h1 : 0 = n + -n := by ring,
--   rw h1,
--   apply int.modeq.add_right,
--   apply int.mod_modeq,
-- end

include h0
variable {ζ_p}
/-- Primitive root's Property on NMod-/
lemma ζ_p_helper(n : ℕ ): ζ_p^((n % (ring_char F)) ) = ζ_p^(n) := by
begin
  nth_rewrite 1 ← nat.mod_add_div n (ring_char F),
  simp only [pow_add, pow_mul, is_primitive_root.pow_eq_one h0, one_pow, mul_one],
end

/-- add_char's property -/
lemma add_char'_mul_property (a : F) (x : F ): add_char' ζ_p (a + x) = add_char' ζ_p a * add_char' ζ_p x := by 
begin 
  unfold add_char',
  simp only [map_add],
  haveI : fact (ring_char F).prime := ⟨char_p.char_is_prime F _⟩,
  rw [zmod.val_add ],
  rw[← pow_add],
  rw[← ζ_p_helper h0 ((algebra.trace (zmod (ring_char F)) F a).val + (algebra.trace (zmod (ring_char F)) F x).val)],
end 


-- def conjugate (x : ℂˣ) : ℂ := conj (x.val)
lemma ζ_p_norm : ‖ζ_p‖ = 1 := 
begin
  haveI : fact (ring_char F).prime := ⟨char_p.char_is_prime F _⟩,
  have := nat.prime.pos (fact.out (ring_char F).prime), 
  apply norm_one_of_pow_eq_one,
  convert h0.pow_eq_one,
  swap, 
  exact ⟨ ring_char F , this⟩,
  refl,
end
lemma ζ_p_ne_zero : ζ_p ≠ 0 :=
begin
  intro h,
  have :=  ζ_p_norm h0,
  rw h at this,
  simpa only [complex.norm_eq_abs, absolute_value.map_zero, zero_ne_one] using this,
end

lemma conj_ζ_p : conj ζ_p = (ζ_p)⁻¹ := 
begin 
  apply eq_inv_of_mul_eq_one_right,
  rw complex.mul_conj,
  rw complex.norm_sq_eq_abs,
  rw ← complex.norm_eq_abs,
  rw ζ_p_norm h0,
  norm_num,
end

/-- conjugation of our primitive root of unity-/
lemma ζ_p_helper_add (n : ℤ )(x : F): conj (ζ_p^n) = ζ_p^(-n) := by 
begin 
  simp only [map_zpow₀, conj_ζ_p h0, inv_zpow'],
end

lemma neg_val_eq_val_neg (n : ℕ) [ne_zero n] {a : zmod n} : (-a).val ≡ -(a.val) [ZMOD n] :=
begin
  rw zmod.neg_val',
  rw [← eq_iff_modeq_int (zmod n)],
  simp only [int.coe_nat_mod, zmod.int_cast_mod, int.cast_coe_nat, zmod.nat_cast_val, int.cast_neg, zmod.int_cast_cast,
  zmod.cast_id', id.def],
  have : a.val < n := zmod.val_lt a,
  rw eq_neg_iff_add_eq_zero,
  nth_rewrite 1 ←zmod.nat_cast_zmod_val a,
  norm_cast,
  rw nat.sub_add_cancel this.le,
  exact zmod.nat_cast_self n,
end

lemma ζ_p_help_add' (n : ℕ )(x : F): conj (ζ_p^n) = ζ_p^(- (n : ℤ)) := by
begin 
  simpa only using ζ_p_helper_add h0 ↑n x,
end

lemma ζ_p_pow_neq_zero (a : ℤ) : ζ_p^a ≠ 0 := 
begin
  by_contra lem,
  by_cases h : a = 0,
  {rw h at lem,
  simp only [zpow_zero, one_ne_zero] at lem,
  exact lem,},
  {rw zpow_eq_zero_iff h at lem,
  exact ζ_p_ne_zero h0 lem,},
end

lemma ζ_p_pow_eq (a b : ℤ ) : ζ_p^a = ζ_p^b ↔ a ≡ b[ZMOD (ring_char F)] := by
begin 
  nth_rewrite 0 ( show b = a + (b - a), by ring),
  rw zpow_add',
  rw int.modeq_iff_dvd,
  rw ← is_primitive_root.zpow_eq_one_iff_dvd h0,
  split,
  {intro h,
  nth_rewrite 0 ← mul_one (ζ_p^a) at h, 
  simp only [is_domain.mul_left_cancel_of_ne_zero (ζ_p_pow_neq_zero h0 a) h],
  },
  {intro h,
  rw [h, mul_one], 
  },
  left,
  exact ζ_p_ne_zero h0,
end


#check neg_val_eq_val_neg h0 (ring_char F) 
lemma add_char'_conjugate (x : F ):  conj ( add_char' ζ_p x) = add_char' ζ_p (-x):= by
begin
  unfold add_char',
  rw ζ_p_help_add' h0 (algebra.trace (zmod (ring_char F)) F x).val x, 
  rw ← zpow_coe_nat,
  rw ζ_p_pow_eq h0,
  rw map_neg,
  symmetry,
  apply neg_val_eq_val_neg h0 (ring_char F) , 
end

/-- `conj_mul_char' (χ : mul_char F ℂ) ` is the complex conjugate of  `χ`, which gives us another `mul_char`-/
def conj_mul_char' (χ : mul_char F ℂ ) :mul_char F ℂ :=
{ to_fun :=  λ x, conj (χ x),
  map_nonunit' := λ x hx, by simpa only [map_eq_zero] using χ.map_nonunit hx,
  map_one' := by {
    simp only [map_one],
  },
  map_mul' := by { 
    intros x y,
    simp only [map_mul],
   }
}

lemma mul_char_minus_one (χ : mul_char F ℂ ) : conj_mul_char' h0 χ (-1) = χ (-1) := by
begin
  unfold conj_mul_char',
  have h1 : χ(-1) = 1 ∨ χ(-1) = 1 := by
    {
      have lem : χ(-1) * χ(-1) = 1 := by
      {
        sorry,
      },
      sorry,
    },
  sorry

end
/-!
## Main results
-/



/-!
Some important results are as follows.

* `gauss_sum_mul_gauss_sum_eq_card`: The product of the Gauss
  sums of `χ` and `ψ` and that of `χ⁻¹` and `ψ⁻¹` is the cardinality
  of the source ring `R` (if `χ` is nontrivial, `ψ` is primitive and `R` is a field).
* `gauss_sum_sq`: The square of the Gauss sum is `χ(-1)` times
  the cardinality of `R` if in addition `χ` is a quadratic character.
* `quad_gauss_sum_frob`: For a quadratic character `χ`, raising
  the Gauss sum to the `p`th power (where `p` is the characteristic of
  the target ring `R'`) multiplies it by `χ p`.
* `char.card_pow_card`: When `F` and `F'` are finite fields and `χ : F → F'`
  is a nontrivial quadratic character, then `(χ (-1) * #F)^(#F'/2) = χ (#F')`.
* `finite_field.two_pow_card`: For every finite field `F` of odd characteristic,
  we have `2^(#F/2) = χ₈(#F)` in `F`.

This machinery can be used to derive (a generalization of) the Law of
Quadratic Reciprocity.

## Tags

additive character, multiplicative character, Gauss sum
-/

