import number_theory.legendre_symbol.add_character
import number_theory.legendre_symbol.zmod_char
import algebra.char_p.char_and_card
import field_theory.finite.trace 
import number_theory.cyclotomic.basic
import data.zmod.basic
import data.complex.basic
import ring_theory.roots_of_unity
import algebra.group_power.basic
import data.complex.basic
import analysis.normed.field.basic
import data.pnat.defs

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
variables {F : Type u} [field F] [fintype F] (ζ_p : ℂˣ) [ fact (is_primitive_root ζ_p (ring_char F)) ]
/-- Definition of the Gauss sum associated to a multiplicative and an additive character. -/
-- structure add_char' extends add_char F ℂˣ:=
-- (ψ : F → ℂˣ )
-- (ζ_p: is_primitive_root )
-- (ψ_eq : ∀ x : F, ψ x = (ψ 1) ^ (trace x))



def add_char'(x : F) : ℂˣ  :=
  ζ_p^( zmod.val (algebra.trace (zmod (ring_char F)) F x))
  

def gauss_sum' (χ : mul_char F ℂ ) : ℂ := ∑ x : F,  -(add_char' ζ_p x)* (χ x)



instance char_p_non_zero : ne_zero (ring_char F) :=
{out :=  begin
  intro h,
  haveI : fact (ring_char F).prime := ⟨char_p.char_is_prime F _⟩,
  exact nat.prime.ne_zero (fact.out (ring_char F).prime) h,
end}

/-- Primitive root's Proprty on NMod -/
lemma ζ_p_helper_help (n : ℤ ): ζ_p^((n % (ring_char F)) ) = ζ_p^(n) := by
begin
  rw ←  mul_inv_eq_one, 
  rw ← zpow_neg ζ_p n, 
  rw ← zpow_add ζ_p,  
  rw  is_primitive_root.zpow_eq_one_iff_dvd (fact.out (is_primitive_root ζ_p (ring_char F))) ,
  rw ← int.modeq_zero_iff_dvd,
  have h1 : 0 = n + -n := by ring,
  rw h1,
  apply int.modeq.add_right,
  apply int.mod_modeq,
end

/-- Primitive root's Property on NMod-/
lemma ζ_p_helper(n : ℕ ): ζ_p^((n % (ring_char F)) ) = ζ_p^(n) := by
begin
  simpa using ζ_p_helper_help ζ_p n,
end

/-- add_char's property -/
lemma add_char'_mul_property (a : F) (x : F ): add_char' ζ_p (a + x) = add_char' ζ_p a * add_char' ζ_p x := by 
begin 
  unfold add_char',
  simp,
  haveI : fact (ring_char F).prime := ⟨char_p.char_is_prime F _⟩,
  rw [zmod.val_add ],
  rw[← pow_add],
  rw[← ζ_p_helper ζ_p ((algebra.trace (zmod (ring_char F)) F a).val + (algebra.trace (zmod (ring_char F)) F x).val)],
  assumption,
  assumption,
end 


def conjugate (x : ℂˣ) : ℂ := conj (x.val)

/-- conjugation of our primitive root of unity-/
lemma ζ_p_helper_add (n : ℤ )(x : F): conjugate (ζ_p^n) = (ζ_p^(-n)).val := by 
begin 
  unfold conjugate,
  simp[conj],
  have h1 : (ζ_p)^(ring_char F) = 1 := by 
  { 
    apply is_primitive_root.pow_eq_one,
    apply fact.out (is_primitive_root ζ_p (ring_char F)),
  },
  have h2 : ‖(ζ_p).val‖  = 1 := by 
  {
    have h3 : ring_char F > 0 := by 
    {
      haveI : fact (ring_char F).prime := ⟨char_p.char_is_prime F _⟩,
      exact nat.prime.pos (fact.out (ring_char F).prime),
    },
    set r := (ring_char F).to_pnat' with h4,
    have h5 : ((ζ_p).val)^(↑r) = 1 := by 
    {
      rw  h4, 
      simp,
      rw [nat.to_pnat',nat.succ_pnat],
      rw pnat.mk_coe,
      rw nat.succ_pred_eq_of_pos h3,
      rw [←units.coe_pow ζ_p (ring_char F),← units.coe_one ,units.eq_iff.mpr h1], 
    },
    apply norm_one_of_pow_eq_one h5,
  },
  rw complex.inv_def,
  have h3 : ‖ ((ζ_p).val)^n ‖ = 1 := by 
  {
    rw [norm_zpow , h2],
    simp,
  },
  simp at h3,
  rw ← complex.mul_self_abs,
  simp[h3], 
end

lemma ζ_p_help_add' (n : ℕ  )(x : F): conjugate (ζ_p^n) = (ζ_p^(- int.of_nat (n) )).val := by
begin 
  simpa using ζ_p_helper_add ζ_p n x,
end



lemma add_char'_conjugate (x : F ):  conjugate ( add_char' ζ_p x) = (add_char' ζ_p (-x)).val := by
begin
  unfold add_char',
  rw ζ_p_help_add' ζ_p (algebra.trace (zmod (ring_char F)) F x).val x, 
  sorry
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

lemma mul_char_minus_one (χ : mul_char F ℂ ) : conj_mul_char' χ (-1) = χ (-1) := by
begin
  unfold conj_mul_char',
  simp,
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

