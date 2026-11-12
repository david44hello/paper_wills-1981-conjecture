/-
Wills/Proofs/Fig3.lean — the claims of Figure 3 (its caption, and l.330), and the Vieta step of l.397 (the proof that
`T` and `X` fail Henze's root condition).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Rows7

open MeasureTheory Polynomial

namespace Wills.Fig3

open Wills.Rows7 (polyT_eq polyX_eq det_one4)

/-- Figure 3: `g_1 ≤ (3G+7)/12`, by the caption's route over (E3)'s facet data: `Σ NVol(F) ≥ 3G - 13` (the proof
of Lemma 4.3) and `g_1 = (G-1)/2 - σ/2` with `σ = Σ relvol` (Lemma 4.1 and (E3)); here `NVol = 6 relvol`. -/
theorem fig3_g1_bound_proof (hE2 : EhrhartReciprocity) (hTRI : BoundaryTriangulation)
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P) :
    g (lat B) P 1 ≤ (3 * (G (lat B) P : ℝ) + 7) / 12 ∧
      ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b →
        ∑ j, 6 * relvol j ≥ 3 * (G (lat B) P : ℝ) - 13 ∧
          g (lat B) P 1 = ((G (lat B) P : ℝ) - 1) / 2 - (∑ j, relvol j) / 2 := by
  have h13 := (lem_4_1_proof hE2 B hB P hP).1
  have hlow := g3_lower_of_tri hTRI B hB P hP
  refine ⟨by linarith, fun m relvol b hd => ?_⟩
  have hg3 : g (lat B) P 3 = (1 / 2) * ∑ j, relvol j := hd.2.2.1
  rw [← Finset.mul_sum]
  constructor <;> linarith

/-- Figure 3: for `G ≥ 31` the bound `(3G+7)/12` exceeds `8`. -/
theorem fig3_bound_gt_proof (Gc : ℝ) (hG : 31 ≤ Gc) : 8 < (3 * Gc + 7) / 12 := by linarith

/-- `g_4(P) > 0` for `P ∈ W⁴`: by (E1) it is the volume of `P`, which has interior points and is compact. -/
lemma g4_pos (hE1 : EhrhartLeading) {P : Set (Pt 4)} (hP : InW (Zn 4) P) : 0 < g (Zn 4) P 4 := by
  have hP1 : InW (lat 1) P := by
    rw [lat_one']
    exact hP
  have h := hE1 4 1 det_one4 P hP1.1 (inW_interior_nonempty hP1)
  rw [lat_one', Matrix.det_one, abs_one, div_one] at h
  rw [h]
  obtain ⟨V, -, hPV⟩ := hP.1
  have hcpt : IsCompact P := by
    rw [hPV]
    exact V.finite_toSet.isCompact_convexHull ℝ
  exact ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior _ (inW_interior_nonempty hP)).ne'
    hcpt.measure_lt_top.ne

/-- l.397: if all four roots of `L_P` (`P ∈ W⁴`) have real part `-1/2`, then `g_3(P) = 2 g_4(P)` (Vieta). -/
theorem henze_vieta_proof (hE1 : EhrhartLeading) (P : Set (Pt 4)) (hP : InW (Zn 4) P)
    (hH : HenzeRoots (ehrhartPoly (Zn 4) P)) : g (Zn 4) P 3 = 2 * g (Zn 4) P 4 := by
  have hdeg : (ehrhartPoly (Zn 4) P).natDegree = 4 :=
    le_antisymm (ehrhartPoly_natDegree_le _ _) (Polynomial.le_natDegree_of_ne_zero (g4_pos hE1 hP).ne')
  exact S7C.coeff3_of_henze _ hdeg hH

/-- l.397: `L_T` has `g_3 = 16 ≠ 2 · 16 = 2 g_4`, and `L_X` has `g_3 = 8 ≠ 2 · 12 = 2 g_4`. -/
theorem henze_coeffs_proof (hE2 : EhrhartReciprocity) :
    g (Zn 4) T 3 = 16 ∧ g (Zn 4) T 4 = 16 ∧ g (Zn 4) X 3 = 8 ∧ g (Zn 4) X 4 = 12 ∧
      (16 : ℝ) ≠ 2 * 16 ∧ (8 : ℝ) ≠ 2 * 12 := by
  refine ⟨?_, ?_, ?_, ?_, by norm_num, by norm_num⟩
  · unfold g; rw [polyT_eq hE2, polyT, polyOf_coeff]; norm_num
  · unfold g; rw [polyT_eq hE2, polyT, polyOf_coeff]; norm_num
  · unfold g; rw [polyX_eq hE2, polyX, polyOf_coeff]; norm_num
  · unfold g; rw [polyX_eq hE2, polyX, polyOf_coeff]; norm_num

end Wills.Fig3
