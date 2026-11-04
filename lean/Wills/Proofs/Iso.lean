/-
Wills/Proofs/Iso.lean — Section 2 rows (l.158): isomorphic pairs have the same counts and Ehrhart coefficients, carry
W to W, and a linear isomorphism of ℝⁿ preserving ℤⁿ is given by a matrix in GL_n(ℤ).
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
import Wills.Proofs.Sec5

open MeasureTheory Pointwise

namespace Wills.S2D

/-! ### A linear isomorphism of `ℝⁿ` as a homeomorphism -/

/-- A linear isomorphism of `ℝⁿ` carries interiors to interiors. -/
lemma interior_image_linEquiv {n : ℕ} (φ : Pt n ≃ₗ[ℝ] Pt n) (S : Set (Pt n)) :
    interior (φ '' S) = φ '' interior S :=
  (φ.toContinuousLinearEquiv.toHomeomorph.image_interior S).symm

/-- A linear isomorphism commutes with negation of sets. -/
lemma image_neg_linEquiv {n : ℕ} (φ : Pt n ≃ₗ[ℝ] Pt n) (S : Set (Pt n)) :
    φ '' (-S) = -(φ '' S) := by
  ext y
  simp only [Set.mem_neg, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨-x, hx, by rw [map_neg]⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨-x, by rw [neg_neg]; exact hx, by rw [map_neg, hxy, neg_neg]⟩

/-! ### The rows -/

/-- l.158: isomorphic pairs have the same lattice-point counts, `φ(kP) ∩ Λ' = φ(kP ∩ Λ)`, so
`L_{P',Λ'} = L_{P,Λ}`; also for the interiors. -/
theorem iso_count (n : ℕ) (P Λ P' Λ' : Set (Pt n)) (h : IsoPair P Λ P' Λ') (k : ℕ) :
    latCount Λ' P' k = latCount Λ P k ∧ intCount Λ' P' k = intCount Λ P k := by
  refine ⟨Sec5.latCount_iso h k, ?_⟩
  obtain ⟨φ, hP, hΛ⟩ := h
  have hsmul : (k : ℝ) • P' = φ '' ((k : ℝ) • P) := by rw [← hP, image_smul_set]
  unfold intCount
  rw [hsmul, interior_image_linEquiv, ← hΛ, ← Set.image_inter φ.injective,
    Set.ncard_image_of_injective _ φ.injective]

/-- l.158: isomorphic pairs have the same Ehrhart coefficients. -/
theorem iso_g (n : ℕ) (P Λ P' Λ' : Set (Pt n)) (h : IsoPair P Λ P' Λ') (i : ℕ) : g Λ' P' i = g Λ P i := by
  have hpoly : ehrhartPoly Λ' P' = ehrhartPoly Λ P := by
    unfold ehrhartPoly
    congr 1
    funext k
    rw [Sec5.latCount_iso h k]
  unfold g
  rw [hpoly]

/-- Isomorphic pairs carry `W^n_Λ` to `W^n_{Λ'}`. -/
theorem inW_iso {n : ℕ} {P Λ P' Λ' : Set (Pt n)} (h : IsoPair P Λ P' Λ') (hP : InW Λ P) : InW Λ' P' := by
  classical
  obtain ⟨φ, hφP, hφΛ⟩ := h
  obtain ⟨⟨V, hV, hPV⟩, hsymm, hint⟩ := hP
  subst hφP hφΛ
  refine ⟨⟨V.image φ, ?_, ?_⟩, ?_, ?_⟩
  · rw [Finset.coe_image]; exact Set.image_mono hV
  · rw [Finset.coe_image, hPV]; exact φ.toLinearMap.image_convexHull _
  · rw [← image_neg_linEquiv, hsymm]
  · rw [interior_image_linEquiv, ← Set.image_inter φ.injective, hint, Set.image_singleton, map_zero]

/-! ### Integer matrices of maps preserving `ℤⁿ` -/

lemma single_mem_Zn {n : ℕ} (j : Fin n) : (Pi.single j 1 : Pt n) ∈ Zn n :=
  ⟨Pi.single j 1, by funext i; simp [ofInt, Pi.single_apply]⟩

/-- A linear map of `ℝⁿ` carrying `ℤⁿ` into `ℤⁿ` is `x ↦ Ux` for an integer matrix `U`. -/
lemma exists_int_matrix {n : ℕ} (ψ : Pt n →ₗ[ℝ] Pt n) (h : ∀ x ∈ Zn n, ψ x ∈ Zn n) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, ∀ x, ψ x = (toReal U).mulVec x := by
  have hc : ∀ j : Fin n, ∃ z : Fin n → ℤ, ofInt z = ψ (Pi.single j 1) := fun j =>
    h _ (single_mem_Zn j)
  choose c hc using hc
  refine ⟨Matrix.of fun i j => c j i, fun x => ?_⟩
  have hM : LinearMap.toMatrix' ψ = toReal (Matrix.of fun i j => c j i) := by
    ext i j
    rw [LinearMap.toMatrix'_apply, ← hc j]
    simp [toReal, ofInt]
  calc ψ x = Matrix.toLin' (LinearMap.toMatrix' ψ) x := by rw [Matrix.toLin'_toMatrix']
    _ = (toReal (Matrix.of fun i j => c j i)).mulVec x := by rw [Matrix.toLin'_apply, hM]

/-- l.158: a linear isomorphism of `ℝⁿ` that carries `ℤⁿ` onto `ℤⁿ` is given by a matrix in `GL_n(ℤ)`. -/
theorem iso_Zn_GL (n : ℕ) (φ : Pt n ≃ₗ[ℝ] Pt n) (h : φ '' Zn n = Zn n) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, IsGLZ U ∧ ∀ x, φ x = (toReal U).mulVec x := by
  have h1 : ∀ x ∈ Zn n, φ x ∈ Zn n := fun x hx => h ▸ Set.mem_image_of_mem φ hx
  have h2 : ∀ x ∈ Zn n, φ.symm x ∈ Zn n := by
    intro x hx
    rw [← h] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  obtain ⟨U, hU⟩ := exists_int_matrix φ.toLinearMap h1
  obtain ⟨W, hW⟩ := exists_int_matrix φ.symm.toLinearMap h2
  refine ⟨U, ?_, hU⟩
  have hmat : toReal W * toReal U = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_one,
      LinearMap.id_apply, ← hU x, ← hW]
    simp
  have hdetR : (W.det : ℝ) * (U.det : ℝ) = 1 := by
    rw [← Sec5.det_toReal, ← Sec5.det_toReal, ← Matrix.det_mul, hmat, Matrix.det_one]
  have hdet : U.det * W.det = 1 := by
    rw [mul_comm]; exact_mod_cast hdetR
  exact Int.eq_one_or_neg_one_of_mul_eq_one hdet

end Wills.S2D
