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
variables {F : Type u} [field F] [fintype F] {ζ_p : ℂ}( h0 : (is_primitive_root ζ_p (ring_char F)) )

example (c :ℂ ) (X : Type) [fintype X]
  (g : X → ℂ) : (∑ (x : X), (- g x)) = - ∑ (x : X), (g x) := by simp

lemma gauss_sum_1 (χ : mul_char F ℂ ) ( h0 : (is_primitive_root ζ_p (ring_char F)) ): conj (gauss_sum' ζ_p χ) =  (χ(-1)) * (gauss_sum' ζ_p (conj_mul_char  (χ)) )  :=
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
end

lemma gauss_sum_2 (χ : mul_char F ℂ )(hχ : χ.is_nontrivial) : (gauss_sum' ζ_p χ) * (gauss_sum'(ζ_p ) (conj_mul_char  χ)) = χ(-1) * (fintype.elems F).card := 
begin
  rw [gauss_sum',gauss_sum'],
  simp_rw [finset.sum_mul_sum ],
  simp only [finset.univ_product_univ, neg_mul, mul_neg, neg_neg],
  sorry,
end

lemma lem_helper_1 (χ : mul_char F ℂ )(x : F × F)(hx : x.snd ≠ 0 ) : ((add_char' ζ_p x.fst ) * (add_char' ζ_p x.snd )) * ((χ x.fst) * (conj_mul_char χ x.snd )) =  (add_char' ζ_p x.fst * (χ x.fst)) * ((add_char' ζ_p x.snd ) * (conj_mul_char χ x.snd )) := 
begin
  rw [mul_assoc],
  nth_rewrite 1 [←mul_assoc ],
  nth_rewrite 2 [mul_comm],
  nth_rewrite 0 [ mul_assoc],
  nth_rewrite 0 [ mul_assoc],
end

include h0
lemma helper_1 (χ : mul_char F ℂ ) (hχ : χ.is_nontrivial)(x : F × F)(hx : x.snd ≠ 0) : (add_char' ζ_p x.fst * (χ x.fst)) * ((add_char' ζ_p x.snd ) * (conj_mul_char χ x.snd )) = add_char' ζ_p (x.fst + x.snd) * χ(x.fst * (x.snd)⁻¹ ) := 
begin 
  rw[← lem_helper_1],
  rw[← add_char'_mul_property],
  rw[conj_mul_char_eval ],
  sorry,
  assumption,
  assumption,
end