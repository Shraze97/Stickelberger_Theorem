import number_theory.legendre_symbol.add_character
import number_theory.legendre_symbol.zmod_char
import algebra.char_p.char_and_card
import field_theory.finite.trace 
import number_theory.cyclotomic.basic
import data.zmod.basic
import data.complex.basic
import ring_theory.roots_of_unity
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
open_locale big_operators

universes u v w
-- variables (f : ℕ)
variables {F : Type u} [field F] [fintype F] (p : ℕ) [fact p.prime] [char_p F p](ζ_p : ℂˣ) [ fact (is_primitive_root ζ_p p) ]
/-- Definition of the Gauss sum associated to a multiplicative and an additive character. -/
-- structure add_char' extends add_char F ℂˣ:=
-- (ψ : F → ℂˣ )
-- (ζ_p: is_primitive_root )
-- (ψ_eq : ∀ x : F, ψ x = (ψ 1) ^ (trace x))



def add_char'(x : F) : ℂˣ  :=
  ζ_p^( zmod.val (algebra.trace (zmod (ring_char F)) F x))
  
def gauss_sum' (χ : mul_char F ℂ ) : ℂ := ∑ x : F,  (add_char' ζ_p x)* (χ x)

instance char_p_non_zero(p : ℕ )[fact p.prime][char_p F p] : ne_zero (ring_char F) :=
{out :=  begin
  intro h,
  have h1 : ring_char F = p := 
  begin
    apply ring_char.eq ,
  end,
  rw h1 at h,
  exact nat.prime.ne_zero (fact.out p.prime) h,
end}


lemma ζ_p_pow_eq_one (n : ℤ  ) : ζ_p^(n % p) = ζ_p^n := by
begin
  rw ←  mul_inv_eq_one, 
  rw ← zpow_neg ζ_p n, 
  rw ← zpow_add ζ_p,  
  rw  is_primitive_root.zpow_eq_one_iff_dvd (fact.out (is_primitive_root ζ_p p)) ,
  rw ← int.modeq_zero_iff_dvd,
  have h1 : 0 = n + -n := by ring,
  rw h1,
  apply int.modeq.add_right,
  apply int.mod_modeq,
end


lemma add_char'_mul_property (a : F) (x : F ){p : ℕ}: add_char' ζ_p (a + x) = add_char' ζ_p a * add_char' ζ_p x := by 
begin 
  unfold add_char',
  simp,
  have h1 : ring_char F = p := by apply ring_char.eq,
  rw [zmod.val_add char_p_non_zero p],
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

