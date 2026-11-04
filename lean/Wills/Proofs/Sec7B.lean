/-
Wills/Proofs/Sec7B.lean — Section 7 rows G_unimod_inv, T_iso, D4star_dual of "Wills' (1981) conjecture is fully
resolved".
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

namespace Wills.S7B

/-! ### Unimodular maps preserve `G` -/

lemma toReal_mulVec_ofInt {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    (toReal U).mulVec (ofInt z) = ofInt (U.mulVec z) := by
  funext i
  simp [toReal, ofInt, Matrix.mulVec, dotProduct]

lemma toReal_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) : toReal (A * B) = toReal A * toReal B := by
  ext i j
  simp [toReal, Matrix.mul_apply]

lemma toReal_one {n : ℕ} : toReal (1 : Matrix (Fin n) (Fin n) ℤ) = 1 := by
  ext i j
  simp [toReal, Matrix.one_apply]

lemma isUnit_det_of_GLZ {n : ℕ} {U : Matrix (Fin n) (Fin n) ℤ} (hU : IsGLZ U) : IsUnit U.det := by
  rcases hU with h | h
  · rw [h]; exact isUnit_one
  · rw [h]; exact isUnit_one.neg

lemma mulVec_injective_of_GLZ {n : ℕ} {U : Matrix (Fin n) (Fin n) ℤ} (hU : IsGLZ U) :
    Function.Injective (fun x : Pt n => (toReal U).mulVec x) := by
  intro x y hxy
  have hinv : toReal U⁻¹ * toReal U = 1 := by
    rw [← toReal_mul, Matrix.nonsing_inv_mul _ (isUnit_det_of_GLZ hU), toReal_one]
  have hx : (toReal U⁻¹).mulVec ((toReal U).mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hy : (toReal U⁻¹).mulVec ((toReal U).mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  simp only at hxy
  rw [← hx, ← hy, hxy]

lemma image_Zn_of_GLZ {n : ℕ} {U : Matrix (Fin n) (Fin n) ℤ} (hU : IsGLZ U) :
    (fun x : Pt n => (toReal U).mulVec x) '' Zn n = Zn n := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨U.mulVec z, (toReal_mulVec_ofInt U z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨ofInt (U⁻¹.mulVec z), ⟨_, rfl⟩, ?_⟩
    simp only
    rw [toReal_mulVec_ofInt, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_of_GLZ hU),
      Matrix.one_mulVec]

/-- Proof of Theorem 7.1, l.403: unimodular maps preserve `G`. -/
theorem G_unimod_inv (P P' : Set (Pt 4)) (h : UnimodEquiv P P') : G (Zn 4) P' = G (Zn 4) P := by
  obtain ⟨U, hU, rfl⟩ := h
  unfold G
  rw [← image_Zn_of_GLZ hU, ← Set.image_inter (mulVec_injective_of_GLZ hU),
    Set.ncard_image_of_injective _ (mulVec_injective_of_GLZ hU), image_Zn_of_GLZ hU]

/-! ### The dual of `ℤ⁴ ∪ (ℤ⁴ + ½(1,1,1,1))` -/

lemma single_mem_latD4star (i : Fin 4) : (Pi.single i (1 : ℝ) : Pt 4) ∈ latD4star := by
  refine Or.inl ⟨Pi.single i 1, ?_⟩
  funext j
  simp only [ofInt, Pi.single_apply]
  split_ifs <;> simp

lemma half_mem_latD4star : (fun _ => (1 / 2 : ℝ) : Pt 4) ∈ latD4star :=
  Or.inr ⟨0, Sec2.zero_mem_Zn 4, by simp⟩

/-- l.389: the dual lattice of `ℤ⁴ ∪ (ℤ⁴ + ½(1,1,1,1))` is `{y ∈ ℤ⁴ : y_1 + ⋯ + y_4 even}`. -/
theorem D4star_dual : dualLat latD4star = gammaI Finset.univ := by
  ext w
  constructor
  · intro hw
    have hcoord : ∀ i, ∃ z : ℤ, w i = z := by
      intro i
      obtain ⟨z, hz⟩ := hw _ (single_mem_latD4star i)
      exact ⟨z, by simpa [dotProduct_single] using hz⟩
    choose z hz using hcoord
    have hwz : w = ofInt z := funext fun i => hz i
    obtain ⟨c, hc⟩ := hw _ half_mem_latD4star
    rw [hwz] at hc
    simp only [dotProduct, ofInt, Fin.sum_univ_four] at hc
    have hc' : ((z 0 + z 1 + z 2 + z 3 : ℤ) : ℝ) = ((c + c : ℤ) : ℝ) := by
      push_cast; linarith
    have hc'' : z 0 + z 1 + z 2 + z 3 = c + c := by exact_mod_cast hc'
    refine ⟨z, hwz, c, ?_⟩
    rw [Fin.sum_univ_four]
    exact hc''
  · rintro ⟨z, rfl, c, hc⟩ x hx
    rw [Fin.sum_univ_four] at hc
    have hc' : ((z 0 : ℝ) + z 1 + z 2 + z 3) = (c : ℝ) + c := by exact_mod_cast hc
    rcases hx with ⟨y, rfl⟩ | ⟨v, ⟨y, rfl⟩, rfl⟩
    · refine ⟨z 0 * y 0 + z 1 * y 1 + z 2 * y 2 + z 3 * y 3, ?_⟩
      simp only [dotProduct, ofInt, Fin.sum_univ_four]
      push_cast; ring
    · refine ⟨z 0 * y 0 + z 1 * y 1 + z 2 * y 2 + z 3 * y 3 + c, ?_⟩
      simp only [dotProduct, ofInt, Fin.sum_univ_four, Pi.add_apply]
      push_cast
      linear_combination (1 / 2 : ℝ) * hc'

/-! ### The 24-cell: `T` in the basis `e_1, e_2, e_3, ½(1,1,1,1)` -/

/-- The matrix with columns `e_1, e_2, e_3, ½(1,1,1,1)`. -/
noncomputable def Mh : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![1, 0, 0, 1 / 2], ![0, 1, 0, 1 / 2], ![0, 0, 1, 1 / 2], ![0, 0, 0, 1 / 2]]

lemma Mh_mulVec (x : Pt 4) : Mh.mulVec x = ![x 0 + x 3 / 2, x 1 + x 3 / 2, x 2 + x 3 / 2, x 3 / 2] := by
  funext i
  fin_cases i <;> simp [Mh, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

lemma lat_Mh : latD4star = lat Mh := by
  ext x
  constructor
  · rintro (⟨y, rfl⟩ | ⟨v, ⟨y, rfl⟩, rfl⟩)
    · refine ⟨![y 0 - y 3, y 1 - y 3, y 2 - y 3, 2 * y 3], ?_⟩
      dsimp only
      rw [Mh_mulVec]
      funext i
      fin_cases i <;> simp [ofInt]
    · refine ⟨![y 0 - y 3, y 1 - y 3, y 2 - y 3, 2 * y 3 + 1], ?_⟩
      dsimp only
      rw [Mh_mulVec]
      funext i
      fin_cases i <;> simp [ofInt] <;> ring
  · rintro ⟨z, rfl⟩
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' (z 3)
    · refine Or.inl ⟨![z 0 + m, z 1 + m, z 2 + m, m], ?_⟩
      dsimp only
      rw [Mh_mulVec]
      funext i
      fin_cases i <;> simp [ofInt, hm]
    · refine Or.inr ⟨ofInt ![z 0 + m, z 1 + m, z 2 + m, m], ⟨_, rfl⟩, ?_⟩
      dsimp only
      rw [Mh_mulVec]
      funext i
      fin_cases i <;> simp [ofInt, hm] <;> ring

lemma Mh_det : Mh.det ≠ 0 := by
  simp [Mh, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

lemma Mh_fVec (a : Fin 4) : Mh.mulVec (ofInt (fVec a)) = Pi.single a 1 := by
  rw [Mh_mulVec]
  funext i
  fin_cases a <;> fin_cases i <;> simp [ofInt, fVec]

lemma ofInt_lin (s t : ℤ) (u v : Fin 4 → ℤ) :
    ofInt (s • u + t • v) = (s : ℝ) • ofInt u + (t : ℝ) • ofInt v := by
  funext i
  simp [ofInt]

lemma sign_int {s : ℝ} (hs : s = 1 ∨ s = -1) : ∃ s' : ℤ, (s' = 1 ∨ s' = -1) ∧ (s' : ℝ) = s := by
  rcases hs with rfl | rfl
  · exact ⟨1, Or.inl rfl, by simp⟩
  · exact ⟨-1, Or.inr rfl, by simp⟩

lemma image_tPts : (fun x => Mh.mulVec x) '' tPts =
    {x | ∃ a b : Fin 4, a < b ∧ ∃ s t : ℝ, (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
      x = s • Pi.single a 1 + t • Pi.single b 1} := by
  have key : ∀ (a b : Fin 4) (s t : ℤ),
      Mh.mulVec (ofInt (s • fVec a + t • fVec b)) = (s : ℝ) • Pi.single a 1 + (t : ℝ) • Pi.single b 1 := by
    intro a b s t
    rw [ofInt_lin, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Mh_fVec, Mh_fVec]
  ext x
  constructor
  · rintro ⟨y, ⟨a, b, hab, s, t, hs, ht, rfl⟩, rfl⟩
    refine ⟨a, b, hab, s, t, ?_, ?_, key a b s t⟩
    · rcases hs with rfl | rfl <;> simp
    · rcases ht with rfl | rfl <;> simp
  · rintro ⟨a, b, hab, s, t, hs, ht, rfl⟩
    obtain ⟨s', hs', rfl⟩ := sign_int hs
    obtain ⟨t', ht', rfl⟩ := sign_int ht
    exact ⟨ofInt (s' • fVec a + t' • fVec b), ⟨a, b, hab, s', t', hs', ht', rfl⟩, key a b s' t'⟩

/-- l.378: `T` is the 24-cell `conv{±e_a ± e_b}` written in the basis `e_1, e_2, e_3, ½(1,1,1,1)` of the lattice
`ℤ⁴ ∪ (ℤ⁴ + ½(1,1,1,1))`: these four vectors are a basis of that lattice, and `(T, ℤ⁴) ≅ (24-cell, that lattice)`. -/
theorem T_iso :
    latD4star = lat (Matrix.of ![![1, 0, 0, 1 / 2], ![0, 1, 0, 1 / 2], ![0, 0, 1, 1 / 2], ![0, 0, 0, 1 / 2]]) ∧
      IsoPair T (Zn 4) cell24 latD4star := by
  refine ⟨lat_Mh, ?_⟩
  set φ : Pt 4 ≃ₗ[ℝ] Pt 4 := (Sec2.linEquiv Mh Mh_det).toLinearEquiv with hφdef
  have hφ : ∀ x, φ x = Mh.mulVec x := fun x => Sec2.linEquiv_apply Mh Mh_det x
  have hfun : (⇑φ) = fun x => Mh.mulVec x := funext hφ
  refine ⟨φ, ?_, ?_⟩
  · unfold T cell24
    have himg := LinearMap.image_convexHull (φ : Pt 4 →ₗ[ℝ] Pt 4) tPts
    rw [LinearEquiv.coe_coe] at himg
    rw [himg, hfun, image_tPts]
  · rw [lat_Mh, hfun]
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨ofInt z, ⟨z, rfl⟩, rfl⟩

end Wills.S7B
