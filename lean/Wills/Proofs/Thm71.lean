/-
Wills/Proofs/Thm71.lean — Theorem 7.1 (l.383-385, proof l.403) in a conditional form: the Case III transfer (row
case_III_transfer, for every P) enters as the hypothesis `S12.CaseIIITransfer`.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import Wills.Defs.Basic
import Wills.Defs.Cases
import Wills.Defs.Examples
import Wills.Facts.Basic
import Wills.Checks.Computations
import Wills.Proofs.Interp
import Wills.Proofs.Algebra
import Wills.Proofs.Sec2
import Wills.Proofs.Thm13
import Wills.Proofs.Sec5
import Wills.Proofs.Rows1
import Wills.Proofs.Rows7
import Wills.Proofs.Iso
import Wills.Proofs.Thm12

open MeasureTheory Pointwise

namespace Wills.S71

/-! ### Isomorphic pairs and unimodular equivalence -/

lemma iso_symm {P Λ P' Λ' : Set (Pt 4)} (h : IsoPair P Λ P' Λ') : IsoPair P' Λ' P Λ := by
  obtain ⟨φ, hP, hΛ⟩ := h
  refine ⟨φ.symm, ?_, ?_⟩
  · rw [← hP]; exact φ.symm_image_image P
  · rw [← hΛ]; exact φ.symm_image_image Λ

lemma iso_trans {P Λ P' Λ' P'' Λ'' : Set (Pt 4)} (h1 : IsoPair P Λ P' Λ') (h2 : IsoPair P' Λ' P'' Λ'') :
    IsoPair P Λ P'' Λ'' := by
  obtain ⟨φ, hP, hΛ⟩ := h1
  obtain ⟨ψ, hP', hΛ'⟩ := h2
  refine ⟨φ.trans ψ, ?_, ?_⟩
  · show (fun x => ψ (φ x)) '' P = P''
    rw [← Set.image_image, hP, hP']
  · show (fun x => ψ (φ x)) '' Λ = Λ''
    rw [← Set.image_image, hΛ, hΛ']

/-- A unimodular equivalence gives an isomorphic pair over `ℤ⁴`. -/
lemma iso_of_unimod {P Q : Set (Pt 4)} (h : UnimodEquiv P Q) : IsoPair P (Zn 4) Q (Zn 4) := by
  obtain ⟨U, hU, hPQ⟩ := h
  have hA := Sec5.toReal_det_ne_zero (S12.det_ne_zero_of_GLZ hU)
  refine ⟨(Sec2.linEquiv (toReal U) hA).toLinearEquiv, ?_, ?_⟩
  · show (Sec2.linEquiv (toReal U) hA) '' P = _
    rw [Sec5.linEquiv_coe]
    exact hPQ
  · show (Sec2.linEquiv (toReal U) hA) '' Zn 4 = _
    rw [Sec5.linEquiv_coe]
    exact S12.image_Zn_of_GLZ hU

/-- An isomorphic pair over `ℤ⁴` is a unimodular equivalence (`S2D.iso_Zn_GL`). -/
lemma unimod_of_iso {P Q : Set (Pt 4)} (h : IsoPair P (Zn 4) Q (Zn 4)) : UnimodEquiv P Q := by
  obtain ⟨φ, hP, hZ⟩ := h
  obtain ⟨U, hU, hφ⟩ := S2D.iso_Zn_GL 4 φ hZ
  refine ⟨U, hU, ?_⟩
  have hfun : (fun x => (toReal U).mulVec x) = ⇑φ := funext fun x => (hφ x).symm
  rw [hfun, hP]

lemma unimod_symm {P Q : Set (Pt 4)} (h : UnimodEquiv P Q) : UnimodEquiv Q P :=
  unimod_of_iso (iso_symm (iso_of_unimod h))

/-! ### Signed permutations as linear isomorphisms -/

lemma sign_mul_self (b : Bool) : ((if b then -1 else 1) : ℝ) * (if b then -1 else 1) = 1 := by
  cases b <;> norm_num

/-- The signed permutation `x ↦ (ε_i x_{π i})_i` as a linear isomorphism of `ℝ⁴`; its inverse is
`y ↦ (ε_{π⁻¹ k} y_{π⁻¹ k})_k`. -/
def spEquiv (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : Pt 4 ≃ₗ[ℝ] Pt 4 where
  toFun := signedPerm σ
  invFun := fun y k => (if σ.2 (σ.1.symm k) then -1 else 1) * y (σ.1.symm k)
  map_add' := by
    intro x y
    funext i
    simp only [signedPerm, Pi.add_apply]
    ring
  map_smul' := by
    intro c x
    funext i
    simp only [signedPerm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv := by
    intro x
    funext k
    simp only [signedPerm, Equiv.apply_symm_apply]
    rw [← mul_assoc, sign_mul_self, one_mul]
  right_inv := by
    intro y
    funext i
    simp only [signedPerm, Equiv.symm_apply_apply]
    rw [← mul_assoc, sign_mul_self, one_mul]

lemma spEquiv_coe (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : ⇑(spEquiv σ) = signedPerm σ := rfl

lemma iso_signedPerm {j : Fin 39} {S S' : Set (Pt 4)} (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool))
    (hpres : Preserves (frameRep j) σ) (hS' : S' = signedPerm σ '' S) :
    IsoPair (convexHull ℝ S) (frameRep j) (convexHull ℝ S') (frameRep j) := by
  refine ⟨spEquiv σ, ?_, ?_⟩
  · rw [S12.image_convexHull_linEquiv, spEquiv_coe, hS']
  · rw [spEquiv_coe]
    exact hpres

/-! ### The cube is the convex hull of `{-1,0,1}⁴` -/

lemma corners_subset_cubePts : {x : Pt 4 | ∀ i, x i = 1 ∨ x i = -1} ⊆ cubePts 4 := by
  intro x hx
  refine Sec5.cube_inter_Zn_subset 4 ⟨Sec2.corners_subset_cube 4 hx, ⟨fun i => if x i = 1 then 1 else -1, ?_⟩⟩
  funext i
  rcases hx i with h | h
  · simp [ofInt, h]
  · simp [ofInt, h]
    norm_num

lemma cube_eq_conv_cubePts : cube 4 = convexHull ℝ (cubePts 4) := by
  apply le_antisymm
  · rw [Sec2.cube_eq_convexHull_corners]
    exact convexHull_mono corners_subset_cubePts
  · exact convexHull_min (fun x hx => (Sec2.cubePts_subset 4 hx).1) (Sec2.cube_convex 4)

/-! ### The linear coefficients of `C_4`, `T`, `X` -/

lemma g1_cube : g (Zn 4) (cube 4) 1 = 8 := by
  rw [Sec2.cube_g1]; norm_num

lemma g1_T (hE2 : EhrhartReciprocity) : g (Zn 4) T 1 = 8 := by
  unfold g
  rw [Rows7.polyT_eq hE2, polyT, polyOf_coeff]
  rfl

lemma g1_X (hE2 : EhrhartReciprocity) : g (Zn 4) X 1 = 8 := by
  unfold g
  rw [Rows7.polyX_eq hE2, polyX, polyOf_coeff]
  rfl

/-! ### `M = {0}` gives `r = 0` -/

lemma rP_zero {P : Set (Pt 4)} (h : MP P = {0}) : rP P = 0 := by
  unfold rP
  rw [h]
  simp

/-! ### Case I: `g_1 = 8` forces `P ≅ C_4` -/

lemma caseI_eq (hC1 : Comp1) (P : Set (Pt 4)) (hP : InW (Zn 4) P) (hG : 31 ≤ G (Zn 4) P) (hI : CaseI P)
    (hg : g (Zn 4) P 1 = 8) : UnimodEquiv (cube 4) P := by
  obtain ⟨U, hU, hrows⟩ := hI
  obtain ⟨-, hconv, hcub, hsymm, hsat, hUE⟩ := Sec5.case_I P hP U hU hrows
  have hiso := iso_of_unimod hUE
  have hGQ : G (Zn 4) ((fun x => (toReal U).mulVec x) '' P) = G (Zn 4) P := by
    have h1 := Sec5.latCount_iso hiso 1
    rw [latCount_one, latCount_one] at h1
    exact h1
  have hin : Comp1Input (((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4) := by
    refine ⟨hcub, hsymm, hsat, ?_⟩
    show 31 ≤ G (Zn 4) ((fun x => (toReal U).mulVec x) '' P)
    rw [hGQ]
    exact hG
  have hgQ : g (Zn 4) (convexHull ℝ (((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4)) 1 = 8 := by
    rw [← hconv, S12.g_iso hiso]
    exact hg
  have hS := (hC1 _ hin).2 hgQ
  have hQ : (fun x => (toReal U).mulVec x) '' P = cube 4 := by
    rw [hconv, hS]
    exact cube_eq_conv_cubePts.symm
  have hPC : UnimodEquiv P (cube 4) := by
    rw [← hQ]
    exact hUE
  exact unimod_symm hPC

/-! ### Case II: Computation 3 gives `g_1 ≤ 6` -/

/-- A copy of `S12.g1_caseII` that keeps the bound `6` of Computation 3. -/
lemma g1_caseII6 (hC2 : Comp2) (hC3 : Comp3) (P : Set (Pt 4)) (hP : InW (Zn 4) P) (hG : 31 ≤ G (Zn 4) P)
    (h4 : rP P = 4) (hno : ¬ CaseI P) : g (Zn 4) P 1 ≤ 6 := by
  obtain ⟨U, hrows, hdet⟩ := S12.exists_U P h4
  obtain ⟨-, I, hI2, hUI⟩ := Sec5.case_II_index2 hC2 P hP hG U hrows hdet hno
  obtain ⟨hiso, -, -, -, hconv, hsat, hsymm, hsub, -⟩ := Sec5.case_II_transfer P hP U hrows hdet
  have hspan : Spans (((fun x => (toReal U).mulVec x) '' P) ∩ subLat U) := by
    refine Sec5.spans_of_image (Sec5.toReal_det_ne_zero hdet) (Sec5.span_latPts P hP) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, by rw [Sec5.subLat_eq_image]; exact ⟨x, hx.2, rfl⟩⟩
  exact S12.g1_of_gammaI hC3 P _ _ I hiso hUI hI2 hG hconv hsat hsymm hsub hspan

/-! ### Case III: Computation 5 identifies `P` with `T` or `X` -/

/-- `S` is saturated in the frame lattice, so `#S = G(conv S, Λ) = G(P)` when the counts agree. -/
lemma ncard_of_transfer {P : Set (Pt 4)} {j : Fin 39} {S : Set (Pt 4)} (hS : Comp5Input j S)
    (hcnt : ∀ k, latCount (frameRep j) (convexHull ℝ S) k = latCount (Zn 4) P k) : S.ncard = G (Zn 4) P := by
  have hsat : convexHull ℝ S ∩ frameRep j = S := hS.1.2.2.2.2.1
  have h1 := hcnt 1
  rw [latCount_one, latCount_one] at h1
  rw [← h1]
  unfold G
  rw [hsat]

/-- If `P` (through the Case III transfer) gives `S` with `g_1 = 8` and `#S = G(R)`, where `R` is itself in Case III
with `g_1(R) = 8`, then Computation 5 (uniqueness up to signed permutations) gives `R ≅ P`. -/
lemma caseIII_eq (hC5 : Comp5) (hIII : S12.CaseIIITransfer) (R : Set (Pt 4)) (hR : InW (Zn 4) R)
    (hR31 : 31 ≤ G (Zn 4) R) (hrR : rP R ≤ 3) (hgR : g (Zn 4) R 1 = 8) (P : Set (Pt 4)) {j : Fin 39}
    {S : Set (Pt 4)} (hS : Comp5Input j S) (hiso : IsoPair P (Zn 4) (convexHull ℝ S) (frameRep j))
    (hgS : g (frameRep j) (convexHull ℝ S) 1 = 8) (hn : S.ncard = G (Zn 4) R) : UnimodEquiv R P := by
  obtain ⟨j', S', hS', hiso', hcnt'⟩ := hIII R hR hR31 hrR
  have hgS' : g (frameRep j') (convexHull ℝ S') 1 = 8 := by
    rw [S12.g_iso hiso']
    exact hgR
  have hn' := ncard_of_transfer hS' hcnt'
  obtain ⟨rfl, σ, hpres, hS'eq⟩ := hC5.2.2.1 j j' S S' hS hS' hgS hgS' (hn.trans hn'.symm)
  have h1 : IsoPair P (Zn 4) R (Zn 4) :=
    iso_trans (iso_trans hiso (iso_signedPerm σ hpres hS'eq)) (iso_symm hiso')
  exact unimod_of_iso (iso_symm h1)

lemma T_caseIII : 31 ≤ G (Zn 4) T ∧ rP T ≤ 3 := by
  refine ⟨by rw [Rows7.T_G]; norm_num, ?_⟩
  rw [rP_zero Rows7.M_T]
  norm_num

lemma X_caseIII : 31 ≤ G (Zn 4) X ∧ rP X ≤ 3 := by
  refine ⟨by rw [Rows7.X_G]; norm_num, ?_⟩
  rw [rP_zero Rows7.M_X]
  norm_num

/-! ### The two directions -/

lemma forward (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) (hTRI : BoundaryTriangulation) (hC1 : Comp1)
    (hC2 : Comp2) (hC3 : Comp3) (hC5 : Comp5) (hIII : S12.CaseIIITransfer) (P : Set (Pt 4)) (hP : InW (Zn 4) P)
    (hg : g (Zn 4) P 1 = 8) : UnimodEquiv (cube 4) P ∨ UnimodEquiv T P ∨ UnimodEquiv X P := by
  by_cases hG : G (Zn 4) P ≤ 29
  · have h := (Rows1.lem_4_3 hE2 hE3 hTRI 1 (Rows1.det_one_ne 4) P (S12.inW_lat1 hP)
      (by rw [lat_one']; exact hG)).2
    rw [lat_one'] at h
    linarith
  have hG31 := S12.G_ge_31 P hP hG
  rcases Sec5.thm_1_2_case_split P hP with hI | ⟨h4, hno⟩ | hr
  · exact Or.inl (caseI_eq hC1 P hP hG31 hI hg)
  · have h6 := g1_caseII6 hC2 hC3 P hP hG31 h4 hno
    linarith
  · obtain ⟨j, S, hS, hiso, -⟩ := hIII P hP hG31 hr
    have hgS : g (frameRep j) (convexHull ℝ S) 1 = 8 := by
      rw [S12.g_iso hiso]
      exact hg
    rcases hC5.2.1 j S hS hgS with h49 | h33
    · exact Or.inr (Or.inl (caseIII_eq hC5 hIII T Rows7.T_mem T_caseIII.1 T_caseIII.2 (g1_T hE2) P hS hiso hgS
        (by rw [h49, Rows7.T_G])))
    · exact Or.inr (Or.inr (caseIII_eq hC5 hIII X Rows7.X_mem X_caseIII.1 X_caseIII.2 (g1_X hE2) P hS hiso hgS
        (by rw [h33, Rows7.X_G])))

lemma backward (hE2 : EhrhartReciprocity) (P : Set (Pt 4))
    (h : UnimodEquiv (cube 4) P ∨ UnimodEquiv T P ∨ UnimodEquiv X P) : g (Zn 4) P 1 = 8 := by
  rcases h with h | h | h
  · rw [S12.g_iso (iso_of_unimod h)]
    exact g1_cube
  · rw [S12.g_iso (iso_of_unimod h)]
    exact g1_T hE2
  · rw [S12.g_iso (iso_of_unimod h)]
    exact g1_X hE2

/-! ### The row -/

/-- Theorem 7.1, l.383-385, proof l.403, conditional on the Case III transfer: for `P ∈ W⁴`, `g_1(P) = 8` if and
only if `P` is unimodularly equivalent to `C_4`, `T` or `X`; and these three are pairwise inequivalent
(`G = 81, 49, 33`). The hypothesis `hE1` is not used (renamed `_hE1`). -/
theorem thm_7_1_of (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (hTRI : BoundaryTriangulation) (hC1 : Comp1) (hC2 : Comp2) (hC3 : Comp3) (hC5 : Comp5)
    (hIII : S12.CaseIIITransfer) :
    (∀ P : Set (Pt 4), InW (Zn 4) P →
      (g (Zn 4) P 1 = 8 ↔ UnimodEquiv (cube 4) P ∨ UnimodEquiv T P ∨ UnimodEquiv X P)) ∧
      ¬ UnimodEquiv (cube 4) T ∧ ¬ UnimodEquiv (cube 4) X ∧ ¬ UnimodEquiv T X := by
  refine ⟨fun P hP => ⟨forward hE2 hE3 hTRI hC1 hC2 hC3 hC5 hIII P hP, backward hE2 P⟩, ?_, ?_, ?_⟩
  · intro h
    have hG := Rows7.G_unimod_inv _ _ h
    rw [Rows7.T_G, Rows7.cube4_G_vol.1] at hG
    norm_num at hG
  · intro h
    have hG := Rows7.G_unimod_inv _ _ h
    rw [Rows7.X_G, Rows7.cube4_G_vol.1] at hG
    norm_num at hG
  · intro h
    have hG := Rows7.G_unimod_inv _ _ h
    rw [Rows7.X_G, Rows7.T_G] at hG
    norm_num at hG

end Wills.S71
