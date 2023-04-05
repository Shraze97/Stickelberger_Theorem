import Preliminaries
import data.fintype.basic
noncomputable theory

open add_char 
open_locale big_operators
open_locale classical
open_locale complex_conjugate
universes u v w
-- variables (f : ℕ)
variables {F : Type u} [field F] [fintype F] (ζ_p : ℂˣ) [ fact (is_primitive_root ζ_p (ring_char F)) ]


lemma gauss_sum_1 (χ : mul_char F ℂ ) : conj (gauss_sum' ζ_p χ) =  (χ(-1)) * (gauss_sum' ζ_p (conj_mul_char' (χ)) )  := by
begin
  unfold gauss_sum',
  unfold conj_mul_char',
  simp,
  rw[map_sum],
  have h : χ(-1) = conj_mul_char' χ(-1) := by 
  { unfold conj_mul_char',sorry },
  sorry
end

lemma gauss_sum_2 (χ : mul_char F ℂ )(hχ : χ.is_nontrivial) : (gauss_sum' ζ_p χ) * (gauss_sum'(ζ_p ) (conj_mul_char' χ)) = χ(-1) * (fintype.elems F).card := by
begin
  unfold gauss_sum',
  unfold conj_mul_char',
  simp,
  sorry
end