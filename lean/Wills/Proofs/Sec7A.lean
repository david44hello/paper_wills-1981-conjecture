/-
Wills/Proofs/Sec7A.lean — Section 7 rows (cube C_4: G, volume, Ehrhart polynomial, Henze roots; g_3 from facet
distances).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import Wills.Defs.Basic
import Wills.Defs.Cases
import Wills.Defs.Examples
import Wills.Facts.Basic
import Wills.Proofs.Interp
import Wills.Proofs.Algebra
import Wills.Proofs.Sec2
import Wills.Proofs.Thm13

open MeasureTheory Pointwise

namespace Wills.S7A

/-- l.393: `C_4` has `G = 81` and volume 16. -/
theorem cube4_G_vol : G (Zn 4) (cube 4) = 81 ∧ volume (cube 4) = 16 := by
  constructor
  · rw [← latCount_one, Sec2.cube_count]; norm_num
  · rw [Sec2.cube_vol]; norm_num

/-- `polyC4 = (2X + 1)⁴` (coefficients `2^i binom(4,i)` from `Sec2.cube_g`). -/
lemma polyC4_eq : polyC4 = (Polynomial.C 2 * Polynomial.X + 1) ^ 4 := by
  rw [← Sec2.ehrhartPoly_cube]
  symm
  apply eq_polyOf_of_coeffs _ (ehrhartPoly_natDegree_le _ _) _ rfl
  intro i hi
  have hc := Sec2.cube_g 4 i
  unfold g at hc
  rw [hc]
  interval_cases i <;> norm_num [Nat.choose]

/-- l.395: `L_{C_4} = 1 + 8k + 24k² + 32k³ + 16k⁴`. -/
theorem poly_C4 : ehrhartPoly (Zn 4) (cube 4) = polyC4 ∧
    ∀ k : ℕ, (latCount (Zn 4) (cube 4) k : ℝ) = polyC4.eval (k : ℝ) := by
  refine ⟨by rw [Sec2.ehrhartPoly_cube, polyC4_eq], fun k => ?_⟩
  rw [Sec2.cube_count, polyC4_eq]
  simp

/-- Results l.88: the cube satisfies Henze's root condition. -/
theorem henze_C4 : HenzeRoots (ehrhartPoly (Zn 4) (cube 4)) := by
  intro z hz
  rw [Sec2.ehrhartPoly_cube] at hz
  have hroot := Polynomial.isRoot_of_mem_roots hz
  simp at hroot
  have hre := congrArg Complex.re hroot
  simp at hre
  linarith

/-- l.393: if every facet of `P ∈ W⁴` has lattice distance `l` (in (E3)'s facet data), then `g_3 = σ/2 = 2g_4/l`;
and Lemma 4.1 gives `g_1 = (G-1)/2 - g_3`, `g_2 = (G-1)/2 - g_4`. The proof does not use `FacetFormula` (the facet
data is a hypothesis of the first part), so that binder is named `_hE3`. -/
theorem g3_of_dist (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (P : Set (Pt 4))
    (hP : InW (Zn 4) P)
    (l : ℤ) (hl : 1 ≤ l) :
    (∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData 1 P m relvol b → (∀ j, b j = l) →
        g (Zn 4) P 3 = (1 / 2) * ∑ j, relvol j ∧ g (Zn 4) P 3 = 2 * g (Zn 4) P 4 / l) ∧
      g (Zn 4) P 1 = ((G (Zn 4) P : ℝ) - 1) / 2 - g (Zn 4) P 3 ∧
      g (Zn 4) P 2 = ((G (Zn 4) P : ℝ) - 1) / 2 - g (Zn 4) P 4 := by
  rw [← lat_one' 4] at hP ⊢
  have hdet : (1 : Matrix (Fin 4) (Fin 4) ℝ).det ≠ 0 := by simp
  obtain ⟨h13, h24⟩ := lem_4_1_proof hE2 1 hdet P hP
  refine ⟨fun m relvol b hd hb => ?_, by linarith, by linarith⟩
  have hg3 : g (lat 1) P 3 = (1 / 2) * ∑ j, relvol j := hd.2.2.1
  have hvol := hd.2.2.2
  have hg4 := hE1 4 1 hdet P hP.1 (inW_interior_nonempty hP)
  have hsum : ∑ j, (b j : ℝ) * relvol j = (l : ℝ) * ∑ j, relvol j := by
    rw [Finset.mul_sum]; simp only [hb]
  have hl0 : (l : ℝ) ≠ 0 := by
    have : (0 : ℝ) < l := by exact_mod_cast (show (0 : ℤ) < l by omega)
    exact this.ne'
  have h4 : g (lat 1) P 4 = (1 / 4) * ((l : ℝ) * ∑ j, relvol j) := by
    rw [hg4, hvol, hsum]; norm_num
  refine ⟨hg3, ?_⟩
  rw [h4, hg3]
  field_simp
  ring

end Wills.S7A
