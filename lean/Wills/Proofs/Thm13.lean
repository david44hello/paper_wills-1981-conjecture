/-
Wills/Proofs/Thm13.lean — Theorem 1.3 from its finite facts: the coefficients of `L_W`, the polynomial, and
`L_W(3..6)`.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Algebra
import Wills.Defs.Examples
import Wills.Checks.Computations

open MeasureTheory Polynomial Pointwise

namespace Wills

/-- The coefficients of a polynomial built by `polyOf`. -/
lemma polyOf_coeff (c : List ℝ) (i : ℕ) : (polyOf c).coeff i = c.getD i 0 := by
  unfold polyOf
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [List.getD_eq_default _ _ h]

/-- A polynomial of degree at most `n` equals `polyOf c` (`c` of length `n + 1`) when the first `n + 1` coefficients
agree. -/
lemma eq_polyOf_of_coeffs {n : ℕ} (p : ℝ[X]) (hp : p.natDegree ≤ n) (c : List ℝ) (hc : c.length = n + 1)
    (h : ∀ i ≤ n, p.coeff i = c.getD i 0) : p = polyOf c := by
  ext i
  rw [polyOf_coeff]
  by_cases hi : i ≤ n
  · exact h i hi
  · have hi' : n < i := Nat.lt_of_not_le hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hi'),
      List.getD_eq_default _ _ (by omega)]

/-- The six coefficients of `L_W` from `G(W)`, `L_W(2)`, `#int(2W)` and `vol(W)` (E1, E2). -/
lemma w_coeffs_of (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hVolW : VolW)
    (hmem : InW (lat 1) W) (hG : G (lat 1) W = 117) (hL2 : latCount (lat 1) W 2 = 1815)
    (hI2 : intCount (lat 1) W 2 = 243) :
    g (lat 1) W 0 = 1 ∧ g (lat 1) W 1 = 101 / 10 ∧ g (lat 1) W 2 = 127 / 12 ∧ g (lat 1) W 3 = 139 / 6 ∧
      g (lat 1) W 4 = 557 / 12 ∧ g (lat 1) W 5 = 386 / 15 := by
  have hB : (1 : Matrix (Fin 5) (Fin 5) ℝ).det ≠ 0 := by simp
  have h1 := ehrhartPoly_eval_node (lat 1) W (k := 1) (by norm_num)
  have h2 := ehrhartPoly_eval_node (lat 1) W (k := 2) (by norm_num)
  have hm1 := recip_of_inW hE2 1 hB hmem 1 le_rfl
  have hm2 := recip_of_inW hE2 1 hB hmem 2 (by norm_num)
  rw [intCount_one_of_inW hmem] at hm1
  have h5 := hE1 5 1 hB W hmem.1 (inW_interior_nonempty hmem)
  simp only [Matrix.det_one, abs_one, div_one] at h5
  rw [hVolW, ENNReal.toReal_ofReal (by norm_num)] at h5
  rw [ehrhartPoly_eval_eq_sum] at h1 h2 hm1 hm2
  rw [latCount_one, hG] at h1
  rw [hL2] at h2
  rw [hI2] at hm2
  have h0 := g0_of_inW 1 hmem
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1 h2 hm1 hm2
  push_cast at h1 h2 hm1 hm2
  refine ⟨h0, ?_, ?_, ?_, ?_, h5⟩ <;> linarith

lemma w_poly_of (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hVolW : VolW)
    (hmem : InW (lat 1) W) (hG : G (lat 1) W = 117) (hL2 : latCount (lat 1) W 2 = 1815)
    (hI2 : intCount (lat 1) W 2 = 243) : ehrhartPoly (lat 1) W = polyW := by
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := w_coeffs_of hE1 hE2 hVolW hmem hG hL2 hI2
  apply eq_polyOf_of_coeffs _ (ehrhartPoly_natDegree_le _ _) _ rfl
  intro i hi
  interval_cases i
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5

lemma polyW_eval (x : ℝ) :
    polyW.eval x = 1 + 101 / 10 * x + 127 / 12 * x ^ 2 + 139 / 6 * x ^ 3 + 557 / 12 * x ^ 4 + 386 / 15 * x ^ 5 := by
  simp [polyW, polyOf, Finset.sum_range_succ]

end Wills
