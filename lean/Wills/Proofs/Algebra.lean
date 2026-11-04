/-
Wills/Proofs/Algebra.lean — The Ehrhart algebra of Sections 3 and 4: Proposition 3.1, Lemma 4.1, Proposition 4.2,
(star), Lemma 4.3, Remark 4.4.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Interp
import Wills.Facts.Basic

open MeasureTheory Polynomial Pointwise

namespace Wills

/-! ### Small facts about `W^n_Λ` -/

lemma inW_zero_interior {n : ℕ} {Λ P : Set (Pt n)} (hP : InW Λ P) : (0 : Pt n) ∈ interior P := by
  have h : (0 : Pt n) ∈ interior P ∩ Λ := by rw [hP.2.2]; rfl
  exact h.1

lemma inW_interior_nonempty {n : ℕ} {Λ P : Set (Pt n)} (hP : InW Λ P) : (interior P).Nonempty :=
  ⟨0, inW_zero_interior hP⟩

lemma intCount_one_of_inW {n : ℕ} {Λ P : Set (Pt n)} (hP : InW Λ P) : intCount Λ P 1 = 1 := by
  unfold intCount
  rw [Nat.cast_one, one_smul, hP.2.2]
  exact Set.ncard_singleton 0

lemma g0_of_inW {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) {P : Set (Pt n)} (hP : InW (lat B) P) :
    g (lat B) P 0 = 1 :=
  g0_eq_one_proof n B P (inW_interior_nonempty hP)

/-- `L(-k)` from reciprocity, for `P ∈ W^n_Λ`. -/
lemma recip_of_inW {n : ℕ} (hE2 : EhrhartReciprocity) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0)
    {P : Set (Pt n)} (hP : InW (lat B) P) (k : ℕ) (hk : 1 ≤ k) :
    (ehrhartPoly (lat B) P).eval (-(k : ℝ)) = (-1) ^ n * (intCount (lat B) P k : ℝ) :=
  hE2 n B hB P hP.1 (inW_interior_nonempty hP) k hk

/-! ### Dimension four -/

/-- `L(-1) = 1` for `P ∈ W^4_Λ`. -/
lemma recip_m1_dim4_proof (hE2 : EhrhartReciprocity) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0)
    (P : Set (Pt 4)) (hP : InW (lat B) P) : (ehrhartPoly (lat B) P).eval (-1) = 1 := by
  have h := recip_of_inW hE2 B hB hP 1 le_rfl
  rw [intCount_one_of_inW hP] at h
  norm_num at h ⊢
  exact h

/-- The two equations `L(1) = G` and `L(-1) = 1` in the coefficients, `n = 4`. -/
lemma dim4_equations (hE2 : EhrhartReciprocity) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0)
    (P : Set (Pt 4)) (hP : InW (lat B) P) :
    (G (lat B) P : ℝ) = 1 + g (lat B) P 1 + g (lat B) P 2 + g (lat B) P 3 + g (lat B) P 4 ∧
      (1 : ℝ) = 1 - g (lat B) P 1 + g (lat B) P 2 - g (lat B) P 3 + g (lat B) P 4 := by
  have h1 := ehrhartPoly_eval_node (lat B) P (k := 1) (by norm_num)
  have hm1 := recip_m1_dim4_proof hE2 B hB P hP
  rw [ehrhartPoly_eval_eq_sum] at h1 hm1
  rw [latCount_one] at h1
  have h0 := g0_of_inW B hP
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_one] at h1 hm1
  constructor <;> nlinarith [h1, hm1, h0]

lemma lem_4_1_proof (hE2 : EhrhartReciprocity) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0)
    (P : Set (Pt 4)) (hP : InW (lat B) P) :
    g (lat B) P 1 + g (lat B) P 3 = ((G (lat B) P : ℝ) - 1) / 2 ∧
      g (lat B) P 2 + g (lat B) P 4 = ((G (lat B) P : ℝ) - 1) / 2 := by
  obtain ⟨h1, h2⟩ := dim4_equations hE2 B hB P hP
  constructor <;> linarith

lemma prop_4_2_g4_of (hE1 : EhrhartLeading) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0)
    (P : Set (Pt 4)) (hP : InW (lat B) P) (hvol : (volume P).toReal / |B.det| ≤ 16) :
    g (lat B) P 4 = (volume P).toReal / |B.det| ∧ g (lat B) P 4 ≤ 16 := by
  have h := hE1 4 B hB P hP.1 (inW_interior_nonempty hP)
  exact ⟨h, h ▸ hvol⟩

/-- From (E3)'s facet data: `σ ≤ 4 g_4`, i.e. `Σ relvol ≤ 4 vol/det`. -/
lemma sigma_le_of_data (B : Matrix (Fin 4) (Fin 4) ℝ) (P : Set (Pt 4)) (m : ℕ) (relvol : Fin m → ℝ)
    (b : Fin m → ℤ) (hd : IsFacetData B P m relvol b) :
    ∑ j, relvol j ≤ 4 * ((volume P).toReal / |B.det|) := by
  obtain ⟨hrel, hb, _, hvol⟩ := hd
  have key : ∑ j, relvol j ≤ ∑ j, (b j : ℝ) * relvol j := by
    apply Finset.sum_le_sum
    intro j _
    have : (1 : ℝ) ≤ (b j : ℝ) := by exact_mod_cast hb j
    nlinarith [hrel j]
  rw [hvol]
  norm_num
  linarith

lemma prop_4_2_g3_of (hE1 : EhrhartLeading) (hE3 : FacetFormula) (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P) (hvol : (volume P).toReal / |B.det| ≤ 16) :
    g (lat B) P 3 ≤ 2 * g (lat B) P 4 ∧ 2 * g (lat B) P 4 ≤ 32 := by
  obtain ⟨m, relvol, b, hd⟩ := hE3 4 (by norm_num) B hB P hP
  obtain ⟨hg4, hg4le⟩ := prop_4_2_g4_of hE1 B hB P hP hvol
  have hs := sigma_le_of_data B P m relvol b hd
  have hg3 : g (lat B) P 3 = (1 / 2) * ∑ j, relvol j := hd.2.2.1
  constructor <;> nlinarith

lemma prop_4_2_iff_proof (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P) :
    (∃ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b) ∧
      ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b →
        (g (lat B) P 1 ≤ 8 ↔ (G (lat B) P : ℝ) ≤ ∑ j, relvol j + 17) := by
  refine ⟨hE3 4 (by norm_num) B hB P hP, fun m relvol b hd => ?_⟩
  obtain ⟨h13, _⟩ := lem_4_1_proof hE2 B hB P hP
  have hg3 : g (lat B) P 3 = (1 / 2) * ∑ j, relvol j := hd.2.2.1
  constructor <;> intro h <;> linarith

lemma prop_4_2_g2_of (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P)
    (hvol : (volume P).toReal / |B.det| ≤ 16) (h1 : g (lat B) P 1 ≤ 8) :
    g (lat B) P 2 ≤ g (lat B) P 4 + 8 ∧ g (lat B) P 4 + 8 ≤ 24 := by
  obtain ⟨h13, h24⟩ := lem_4_1_proof hE2 B hB P hP
  obtain ⟨h3, h4⟩ := prop_4_2_g3_of hE1 hE3 B hB P hP hvol
  constructor <;> linarith

lemma star_iff_proof (hE3 : FacetFormula) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4))
    (hP : InW (lat B) P) :
    (∃ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b) ∧
      ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b →
        ((G (lat B) P : ℝ) ≤ ∑ j, relvol j + 17 ↔ ∑ j, 6 * relvol j ≥ 6 * (G (lat B) P : ℝ) - 102) := by
  refine ⟨hE3 4 (by norm_num) B hB P hP, fun m relvol b _ => ?_⟩
  rw [← Finset.mul_sum]
  constructor <;> intro h <;> linarith

lemma lem_4_3_arith_proof (f : Fin 4 → ℕ) (hW : (f 1 : ℤ) ≥ 4 * (f 0 : ℤ) - 10)
    (hDS1 : (f 0 : ℤ) - f 1 + f 2 - f 3 = 0) (hDS2 : 2 * f 2 = 4 * f 3) :
    (f 3 : ℤ) = f 1 - f 0 ∧ (f 3 : ℤ) ≥ 3 * (f 0 : ℤ) - 10 ∧
      ∀ Gc : ℤ, Gc ≤ 29 → 3 * Gc - 13 > 6 * Gc - 102 := by
  have h2 : (2 : ℤ) * f 2 = 4 * f 3 := by exact_mod_cast hDS2
  refine ⟨by linarith, by linarith, fun Gc hG => by linarith⟩

/-- `12 g_3 ≥ 3G - 13` from the triangulation facts. -/
lemma g3_lower_of_tri (hTRI : BoundaryTriangulation) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0)
    (P : Set (Pt 4)) (hP : InW (lat B) P) : 12 * g (lat B) P 3 ≥ 3 * (G (lat B) P : ℝ) - 13 := by
  obtain ⟨f, hf0, hf3, hW, hDS1, hDS2⟩ := hTRI B hB P hP
  obtain ⟨_, h3, _⟩ := lem_4_3_arith_proof f hW hDS1 hDS2
  have h3' : (f 3 : ℝ) ≥ 3 * (f 0 : ℝ) - 10 := by exact_mod_cast h3
  have hf0' : (f 0 : ℝ) = (G (lat B) P : ℝ) - 1 := by exact_mod_cast hf0
  linarith

lemma lem_4_3_proof (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) (hTRI : BoundaryTriangulation)
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P)
    (hG : G (lat B) P ≤ 29) :
    ((∃ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b) ∧
      ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b →
        ∑ j, 6 * relvol j > 6 * (G (lat B) P : ℝ) - 102) ∧ g (lat B) P 1 < 8 := by
  have hlow := g3_lower_of_tri hTRI B hB P hP
  have hG' : (G (lat B) P : ℝ) ≤ 29 := by exact_mod_cast hG
  obtain ⟨h13, _⟩ := lem_4_1_proof hE2 B hB P hP
  refine ⟨⟨hE3 4 (by norm_num) B hB P hP, fun m relvol b hd => ?_⟩, by linarith⟩
  have hg3 : g (lat B) P 3 = (1 / 2) * ∑ j, relvol j := hd.2.2.1
  rw [← Finset.mul_sum]
  linarith

lemma rem_4_4_only_proof (Gc : ℤ) : 3 * Gc - 13 > 6 * Gc - 102 ↔ Gc ≤ 29 := by
  constructor <;> intro h <;> omega

/-! ### Dimension five: Proposition 3.1 -/

lemma prop_3_1_proof (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (P : Set (Pt 5))
    (hP : InW (lat 1) P) :
    g (lat 1) P 1 = (4 * ((G (lat 1) P : ℝ) + 1) + 24 * (volume P).toReal -
      (1 / 2) * ((latCount (lat 1) P 2 : ℝ) + (intCount (lat 1) P 2 : ℝ))) / 6 := by
  have hB : (1 : Matrix (Fin 5) (Fin 5) ℝ).det ≠ 0 := by simp
  have h1 := ehrhartPoly_eval_node (lat 1) P (k := 1) (by norm_num)
  have h2 := ehrhartPoly_eval_node (lat 1) P (k := 2) (by norm_num)
  have hm1 := recip_of_inW hE2 1 hB hP 1 le_rfl
  have hm2 := recip_of_inW hE2 1 hB hP 2 (by norm_num)
  rw [intCount_one_of_inW hP] at hm1
  have h5 := hE1 5 1 hB P hP.1 (inW_interior_nonempty hP)
  simp only [Matrix.det_one, abs_one, div_one] at h5
  rw [ehrhartPoly_eval_eq_sum] at h1 h2 hm1 hm2
  rw [latCount_one] at h1
  have h0 := g0_of_inW 1 hP
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1 h2 hm1 hm2
  push_cast at h1 h2 hm1 hm2
  rw [← h5]
  linarith

end Wills
