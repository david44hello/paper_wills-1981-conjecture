/-
Wills/Proofs/Dim3.lean — Wills' theorem in dimension 3 ([Wil81, Theorem (i), (ii)], cited in the proof of Corollary
1.4, l.110, and at l.67), proved from the facts E1, E2, E3: `g_i(P) ≤ 2^i binom(3,i)` for every `P ∈ W³`.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Rows1

open MeasureTheory Polynomial Pointwise

namespace Wills.Dim3

/-- `L(-1) = -1` for `P ∈ W³` (reciprocity E2 with `k = 1`: `(-1)³ · #(int P ∩ ℤ³) = -1`). -/
lemma recip_m1_dim3 (hE2 : EhrhartReciprocity) (P : Set (Pt 3)) (hP : InW (lat 1) P) :
    (ehrhartPoly (lat 1) P).eval (-1) = -1 := by
  have h := recip_of_inW hE2 (1 : Matrix (Fin 3) (Fin 3) ℝ) (by simp) hP 1 le_rfl
  rw [intCount_one_of_inW hP] at h
  norm_num at h
  exact h

/-- The case `i = 1`: `g_1(P) ≤ 6` for `P ∈ W³`. From E2, `L(-1) = -1` reads `1 - g_1 + g_2 - g_3 = -1`, so
`g_1 = 2 + g_2 - g_3`; from E3, `2 g_2 = σ ≤ 3 vol(P)`; from E1, `g_3 = vol(P) ≤ 8` (Minkowski). So
`g_1 ≤ 2 + g_3 / 2 ≤ 6`. -/
lemma g1_le_six (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) (P : Set (Pt 3))
    (hP : InW (Zn 3) P) : g (Zn 3) P 1 ≤ 6 := by
  have h8 : g (Zn 3) P 3 ≤ 8 := by
    have h := Rows1.conj_in hE1 3 P hP
    norm_num at h
    exact h
  rw [← lat_one'] at hP h8 ⊢
  have hm1 := recip_m1_dim3 hE2 P hP
  rw [ehrhartPoly_eval_eq_sum] at hm1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hm1
  norm_num at hm1
  have h0 := g0_of_inW (1 : Matrix (Fin 3) (Fin 3) ℝ) hP
  obtain ⟨m, relvol, b, hd⟩ := hE3 3 (by norm_num) 1 (by simp) P hP
  have hs := Rows1.sigma_le_n (by norm_num : 1 ≤ 3) 1 P m relvol b hd
  have hg2 : g (lat 1) P 2 = 1 / 2 * ∑ j, relvol j := hd.2.2.1
  have hg3 : g (lat 1) P 3 = (volume P).toReal / |(1 : Matrix (Fin 3) (Fin 3) ℝ).det| :=
    hE1 3 1 (by simp) P hP.1 (inW_interior_nonempty hP)
  norm_num at hs hg3
  linarith

/-- Wills' theorem in dimension 3, from E1, E2, E3: `i = 0` by `g_0 = 1`, `i = 1` by `g1_le_six`, `i = 2` by the case
`i = n - 1` (from E3), `i = 3` by Minkowski's theorem (from E1). -/
theorem wills_dim3_proof (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) :
    WillsConj 3 := by
  intro P hP i hi
  interval_cases i
  · rw [Sec2.conj_i0 3 P hP, Sec2.cube_g]
  · have h := g1_le_six hE1 hE2 hE3 P hP
    norm_num
    exact h
  · exact Rows1.conj_in1 hE3 3 (by norm_num) P hP
  · exact Rows1.conj_in hE1 3 P hP

end Wills.Dim3
