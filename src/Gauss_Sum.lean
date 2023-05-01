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

include h0
lemma helper_1 (χ : mul_char F ℂ) (x : F × F) (hx : x ∈ (finset.univ : finset F) ×ˢ finset.filter (λ (x : F), x ≠ 0) finset.univ) : (add_char' ζ_p x.fst * (χ x.fst)) * ((add_char' ζ_p x.snd ) * (conj_mul_char χ x.snd )) = add_char' ζ_p (x.fst + x.snd) * χ(x.fst * (x.snd)⁻¹ ) := 
begin 
  rw [show ((add_char' ζ_p x.fst * (χ x.fst)) * ((add_char' ζ_p x.snd ) * (conj_mul_char χ x.snd )) =
   ((add_char' ζ_p x.fst ) * (add_char' ζ_p x.snd )) * ((χ x.fst) * (conj_mul_char χ x.snd ))), by ring],
  rw[← add_char'_mul_property h0],
  rw [conj_mul_char_eq_inv, map_mul],
end

lemma gauss_sum_2_aux {F : Type u} {ζ_p : ℂ}
  [field F]
  [fintype F]
  (h0 : is_primitive_root ζ_p (ring_char F))
  (χ : mul_char F ℂ)
  (hχ : χ.is_nontrivial) :
  ∑ (x : F × F) in
      finset.univ ×ˢ finset.filter (λ (x : F), x ≠ 0) finset.univ,
      (add_char' ζ_p (x.fst * x.snd + x.snd) * χ x.fst)
         =
    χ (-1) * fintype.card F :=
begin
  admit,
end


lemma gauss_sum_2 (χ : mul_char F ℂ )(hχ : χ.is_nontrivial) : (gauss_sum' ζ_p χ) * (gauss_sum'(ζ_p ) (conj_mul_char  χ)) = χ(-1) * fintype.card F := 
begin
  rw [gauss_sum',gauss_sum'],
  have foo :  ∀ (x : F), x ∈ (finset.univ : finset F) → (-add_char' ζ_p x * (conj_mul_char χ) x) ≠ 0 → x ≠ 0,
  { intros b _ hb,
    refine mt _ hb,
    rintro rfl,
    simp only [mul_char_class.map_nonunit, not_is_unit_zero, not_false_iff, mul_zero], },
  rw ←finset.sum_filter_of_ne foo, clear foo,
  dsimp only,
  simp_rw [finset.sum_mul_sum ],
  simp only [finset.univ_product_univ, neg_mul, mul_neg, neg_neg],
  rw finset.sum_congr rfl (helper_1 h0 χ),
  rw @finset.sum_bij' _ _ _ _ _ (finset.univ ×ˢ finset.filter (λ (x : F), x ≠ 0) finset.univ) _ (λ (y : F × F), add_char' ζ_p (y.fst*y.snd+y.snd) * χ (y.fst)) (λ (x : F × F) _, (x.1 * x.2⁻¹, x.2)) _ _ (λ (y : F × F) _, (y.1*y.2, y.2)),
  rotate,
  { --dsimp only, 
    rintro ⟨a , b ⟩ ha,
    rw[finset.mem_product] at ha,
    cases ha with _ hb,
    rw[finset.mem_filter] at hb,
    cases hb with _ hb,
    dsimp only at *,
    sorry },
  { dsimp only,
    sorry },
  { dsimp only,
    sorry },
  { dsimp only,
    sorry },
  { dsimp only,
    sorry },
  apply gauss_sum_2_aux;
  assumption,
end

