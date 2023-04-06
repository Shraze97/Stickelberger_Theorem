import Preliminaries
import data.fintype.basic
import algebra.big_operators.ring
noncomputable theory

open add_char 
open_locale big_operators
open_locale classical
open_locale complex_conjugate
universes u v w
-- variables (f : ℕ)
variables {F : Type u} [field F] [fintype F] {ζ_p : ℂ} 

example (c :ℂ ) (X : Type) [fintype X]
  (g : X → ℂ) : (∑ (x : X), (- g x)) = - ∑ (x : X), (g x) := by simp

lemma gauss_sum_1 (χ : mul_char F ℂ ) ( h0 : (is_primitive_root ζ_p (ring_char F)) ): conj (gauss_sum' ζ_p χ) =  (χ(-1)) * (gauss_sum' ζ_p (conj_mul_char  (χ)) )  := by
begin
  rw [gauss_sum',gauss_sum'],
  simp_rw [conj_mul_char_eval],
  rw ring_hom.map_sum,
  simp_rw [map_mul, map_neg, conj_add_char' h0],
  rw[(fintype.sum_equiv (equiv.neg F) _ _ ( λ _, rfl)).symm],
  rw[finset.mul_sum],
  apply finset.sum_congr rfl,
  intros x hx,
  rw[ equiv.neg_apply,neg_neg, ← neg_one_mul x],
  rw[map_mul],
  rw[map_mul],
  simp only [mul_comm,mul_assoc,mul_left_comm,  conj_mul_char_neg_one],
  -- simp_rw equiv.neg_apply,
  -- simp_rw neg_neg,
  -- simp_rw[← neg_one_mul _],
end

lemma gauss_sum_2 (χ : mul_char F ℂ )(hχ : χ.is_nontrivial) : (gauss_sum' ζ_p χ) * (gauss_sum'(ζ_p ) (conj_mul_char  χ)) = χ(-1) * (fintype.elems F).card := by
begin
  sorry,
end

