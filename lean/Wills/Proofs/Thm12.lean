/-
Wills/Proofs/Thm12.lean — Theorem 1.2, Conjecture 1.1 for n = 4 and Corollary 1.4 (l.372-374, l.94, l.105-111), in a
conditional form: the Case III transfer (row case_III_transfer, for every P) enters as the hypothesis
`CaseIIITransfer`.
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
import Wills.Proofs.Dim3

open MeasureTheory Pointwise

namespace Wills.S12

/-- The Case III transfer: the conclusion of the row `case_III_transfer` of Statements.lean, for every `P`. -/
def CaseIIITransfer : Prop :=
  ∀ P : Set (Pt 4), InW (Zn 4) P → 31 ≤ G (Zn 4) P → rP P ≤ 3 →
    ∃ j S, Comp5Input j S ∧ IsoPair P (Zn 4) (convexHull ℝ S) (frameRep j) ∧
      ∀ k, latCount (frameRep j) (convexHull ℝ S) k = latCount (Zn 4) P k

/-! ### Isomorphic pairs and linear isomorphisms -/

/-- Isomorphic pairs have the same Ehrhart coefficients (their counts agree, so their interpolants agree). -/
lemma g_iso {n : ℕ} {P Λ P' Λ' : Set (Pt n)} (h : IsoPair P Λ P' Λ') (i : ℕ) : g Λ' P' i = g Λ P i := by
  have hpoly : ehrhartPoly Λ' P' = ehrhartPoly Λ P := by
    unfold ehrhartPoly
    congr 1
    funext k
    rw [Sec5.latCount_iso h k]
  unfold g
  rw [hpoly]

lemma image_neg_linEquiv {n : ℕ} (φ : Pt n ≃ₗ[ℝ] Pt n) (S : Set (Pt n)) :
    φ '' (-S) = -(φ '' S) := by
  ext y
  simp only [Set.mem_neg, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨-x, hx, by rw [map_neg]⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨-x, by rw [neg_neg]; exact hx, by rw [map_neg, hxy, neg_neg]⟩

lemma image_convexHull_linEquiv {n : ℕ} (φ : Pt n ≃ₗ[ℝ] Pt n) (S : Set (Pt n)) :
    φ '' convexHull ℝ S = convexHull ℝ (φ '' S) :=
  φ.toLinearMap.image_convexHull S

lemma spans_image_linEquiv (φ : Pt 4 ≃ₗ[ℝ] Pt 4) {S : Set (Pt 4)} (h : Spans S) : Spans (φ '' S) := by
  unfold Spans at h ⊢
  rw [eq_top_iff]
  intro x _
  have hx : φ.symm x ∈ Submodule.span ℝ S := by rw [h]; exact Submodule.mem_top
  have := Submodule.apply_mem_span_image_of_mem_span φ.toLinearMap hx
  simpa using this

lemma inW_lat1 {P : Set (Pt 4)} (hP : InW (Zn 4) P) : InW (lat (1 : Matrix (Fin 4) (Fin 4) ℝ)) P := by
  rw [lat_one']; exact hP

/-! ### Few lattice points: `G ≤ 29` (Lemma 4.3), and `G` odd -/

lemma g1_small (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) (hTRI : BoundaryTriangulation)
    (P : Set (Pt 4)) (hP : InW (Zn 4) P) (hG : G (Zn 4) P ≤ 29) : g (Zn 4) P 1 ≤ 8 := by
  have h := (Rows1.lem_4_3 hE2 hE3 hTRI 1 (Rows1.det_one_ne 4) P (inW_lat1 hP) (by rw [lat_one']; exact hG)).2
  rw [lat_one'] at h
  exact h.le

lemma G_ge_31 (P : Set (Pt 4)) (hP : InW (Zn 4) P) (hG : ¬ G (Zn 4) P ≤ 29) : 31 ≤ G (Zn 4) P := by
  have hodd := Sec2.G_odd 4 1 (Rows1.det_one_ne 4) P (inW_lat1 hP)
  rw [lat_one'] at hodd
  obtain ⟨k, hk⟩ := hodd
  omega

/-! ### Case I -/

lemma det_ne_zero_of_GLZ {U : Matrix (Fin 4) (Fin 4) ℤ} (hU : IsGLZ U) : U.det ≠ 0 := by
  rcases hU with h | h <;> rw [h] <;> norm_num

lemma isUnit_det_of_GLZ {n : ℕ} {U : Matrix (Fin n) (Fin n) ℤ} (hU : IsGLZ U) : IsUnit U.det := by
  rcases hU with h | h
  · rw [h]; exact isUnit_one
  · rw [h]; exact isUnit_one.neg

/-- `x ↦ Ux` carries `ℤⁿ` onto `ℤⁿ` for `U ∈ GL_n(ℤ)`. -/
lemma image_Zn_of_GLZ {n : ℕ} {U : Matrix (Fin n) (Fin n) ℤ} (hU : IsGLZ U) :
    (fun x : Pt n => (toReal U).mulVec x) '' Zn n = Zn n := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨U.mulVec z, (Sec5.toReal_mulVec_ofInt U z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨ofInt (U⁻¹.mulVec z), ⟨_, rfl⟩, ?_⟩
    simp only
    rw [Sec5.toReal_mulVec_ofInt, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_of_GLZ hU),
      Matrix.one_mulVec]

lemma g1_caseI (hC1 : Comp1) (P : Set (Pt 4)) (hP : InW (Zn 4) P) (hG : 31 ≤ G (Zn 4) P) (hI : CaseI P) :
    g (Zn 4) P 1 ≤ 8 := by
  obtain ⟨U, hU, hrows⟩ := hI
  obtain ⟨-, hconv, hcub, hsymm, hsat, -⟩ := Sec5.case_I P hP U hU hrows
  have hA := Sec5.toReal_det_ne_zero (det_ne_zero_of_GLZ hU)
  have hiso : IsoPair P (Zn 4) ((fun x => (toReal U).mulVec x) '' P) (Zn 4) := by
    refine ⟨(Sec2.linEquiv (toReal U) hA).toLinearEquiv, ?_, ?_⟩
    · show (Sec2.linEquiv (toReal U) hA) '' P = _
      rw [Sec5.linEquiv_coe]
    · show (Sec2.linEquiv (toReal U) hA) '' Zn 4 = _
      rw [Sec5.linEquiv_coe]
      exact image_Zn_of_GLZ hU
  have hGQ : G (Zn 4) ((fun x => (toReal U).mulVec x) '' P) = G (Zn 4) P := by
    have h1 := Sec5.latCount_iso hiso 1
    rw [latCount_one, latCount_one] at h1
    exact h1
  have hin : Comp1Input (((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4) := by
    refine ⟨hcub, hsymm, hsat, ?_⟩
    show 31 ≤ G (Zn 4) ((fun x => (toReal U).mulVec x) '' P)
    rw [hGQ]; exact hG
  have h1 := (hC1 _ hin).1
  rw [← hconv, g_iso hiso] at h1
  exact h1

/-! ### Case II -/

/-- `r(P) = 4`: the rows of an integer matrix `U` with `det U ≠ 0` lie in `M(P)`. -/
lemma exists_U (P : Set (Pt 4)) (h4 : rP P = 4) :
    ∃ U : Matrix (Fin 4) (Fin 4) ℤ, (∀ i, ofInt (U i) ∈ MP P) ∧ U.det ≠ 0 := by
  have htop : Submodule.span ℝ (MP P) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact h4
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℝ (MP P)
  rw [htop] at hspan
  let B : Module.Basis b ℝ (Pt 4) := Module.Basis.mk hli (by rw [Subtype.range_coe]; exact hspan.symm.le)
  have : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = 4 := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : Fin 4 ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hZ : ∀ i, ∃ z : Fin 4 → ℤ, ofInt z = (e i : Pt 4) := fun i => (hb (e i).2).1
  choose z hz using hZ
  refine ⟨Matrix.of fun i j => z i j, fun i => ?_, ?_⟩
  · show ofInt (z i) ∈ MP P
    rw [hz i]
    exact hb (e i).2
  · have hli' : LinearIndependent ℝ (fun i => (e i : Pt 4)) := hli.comp e e.injective
    have hrow : (toReal (Matrix.of fun i j => z i j)).row = fun i => (e i : Pt 4) := by
      funext i
      rw [← hz i]
      rfl
    rw [← hrow] at hli'
    have hU := Matrix.linearIndependent_row_iff_isUnit.1 hli'
    have hdet := ((Matrix.isUnit_iff_isUnit_det _).1 hU).ne_zero
    rw [Sec5.det_toReal] at hdet
    exact_mod_cast hdet

/-- A permutation `π` of the coordinates with `a ∈ J ↔ π a ∈ I`, when `|I| = |J|`. -/
lemma exists_perm_iff (I J : Finset (Fin 4)) (h : J.card = I.card) :
    ∃ π : Equiv.Perm (Fin 4), ∀ a, a ∈ J ↔ π a ∈ I := by
  have hc : Fintype.card {x // x ∈ J} = Fintype.card {x // x ∈ I} := by
    simp only [Fintype.card_coe, h]
  let e : {x // x ∈ J} ≃ {x // x ∈ I} := Fintype.equivOfCardEq hc
  refine ⟨e.extendSubtype, fun a => ⟨fun ha => e.extendSubtype_mem a ha, fun ha => ?_⟩⟩
  by_contra hna
  exact e.extendSubtype_not_mem a hna ha

/-- The coordinate permutation `x ↦ x ∘ π` carries `Γ_I` onto `Γ_J` when `a ∈ J ↔ π a ∈ I`. -/
lemma perm_gammaI (π : Equiv.Perm (Fin 4)) (I J : Finset (Fin 4)) (hπ : ∀ a, a ∈ J ↔ π a ∈ I) :
    (LinearEquiv.funCongrLeft ℝ ℝ π) '' gammaI I = gammaI J := by
  have hsum : ∀ z : Fin 4 → ℤ, ∑ i ∈ J, z (π i) = ∑ i ∈ I, z i := fun z =>
    Finset.sum_equiv π hπ (fun _ _ => rfl)
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl, hz⟩, rfl⟩
    refine ⟨z ∘ π, rfl, ?_⟩
    show Even (∑ i ∈ J, z (π i))
    rw [hsum z]
    exact hz
  · rintro ⟨w, rfl, hw⟩
    refine ⟨ofInt (w ∘ π.symm), ⟨w ∘ π.symm, rfl, ?_⟩, ?_⟩
    · have h1 := hsum (w ∘ π.symm)
      simp only [Function.comp_apply, Equiv.symm_apply_apply] at h1
      show Even (∑ i ∈ I, w (π.symm i))
      rw [← h1]
      exact hw
    · funext i
      simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, ofInt]

lemma perm_cubePts (π : Equiv.Perm (Fin 4)) :
    (LinearEquiv.funCongrLeft ℝ ℝ π) '' cubePts 4 ⊆ cubePts 4 := by
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  exact ⟨z ∘ π, fun i => hz (π i), rfl⟩

lemma card_filter_lt (m : ℕ) (hm : m ≤ 4) : (Finset.univ.filter (fun i : Fin 4 => i.val < m)).card = m := by
  interval_cases m <;> decide

/-- Case II after the transfer: `(P, ℤ⁴) ≅ (Q, Γ_I)`, `|I| ≥ 2`, `Q = conv S`, `S = Q ∩ Γ_I` saturated, symmetric,
spanning, in `{-1,0,1}⁴`; then `g_1(P) ≤ 6` by Computation 3 (after a permutation `Γ_I → Γ_m`). -/
lemma g1_of_gammaI (hC3 : Comp3) (P Q Γ : Set (Pt 4)) (I : Finset (Fin 4)) (hiso : IsoPair P (Zn 4) Q Γ)
    (hΓ : Γ = gammaI I) (hI2 : 2 ≤ I.card) (hG : 31 ≤ G (Zn 4) P) (hconv : Q = convexHull ℝ (Q ∩ Γ))
    (hsat : Saturated Γ (Q ∩ Γ)) (hsymm : -(Q ∩ Γ) = Q ∩ Γ) (hsub : Q ∩ Γ ⊆ Γ ∩ cubePts 4)
    (hspan : Spans (Q ∩ Γ)) : g (Zn 4) P 1 ≤ 6 := by
  have hI4 : I.card ≤ 4 := by simpa using Finset.card_le_univ I
  obtain ⟨π, hπ⟩ := exists_perm_iff I (Finset.univ.filter (fun i : Fin 4 => i.val < I.card))
    (card_filter_lt I.card hI4)
  have hψΓ : (LinearEquiv.funCongrLeft ℝ ℝ π) '' Γ = gammaM I.card := by
    rw [hΓ]; exact perm_gammaI π I _ hπ
  have hn : (Q ∩ Γ).ncard = G (Zn 4) P := by
    have h1 := Sec5.latCount_iso hiso 1
    rw [latCount_one, latCount_one] at h1
    exact h1
  have hsat' : convexHull ℝ (Q ∩ Γ) ∩ Γ = Q ∩ Γ := hsat
  have hin : Comp3Input I.card ((LinearEquiv.funCongrLeft ℝ ℝ π) '' (Q ∩ Γ)) := by
    refine ⟨?_, ?_, ?_, spans_image_linEquiv _ hspan, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hx' := hsub hx
      refine ⟨?_, perm_cubePts π ⟨x, hx'.2, rfl⟩⟩
      rw [← hψΓ]
      exact ⟨x, hx'.1, rfl⟩
    · rw [← image_neg_linEquiv, hsymm]
    · show convexHull ℝ _ ∩ _ = _
      rw [← hψΓ, ← image_convexHull_linEquiv, ← Set.image_inter (LinearEquiv.funCongrLeft ℝ ℝ π).injective,
        hsat']
    · rw [Set.ncard_image_of_injective _ (LinearEquiv.funCongrLeft ℝ ℝ π).injective, hn]
      exact hG
  have hm : I.card ∈ ({2, 3, 4} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have h6 := hC3 I.card hm _ hin
  have hiso2 : IsoPair Q Γ ((LinearEquiv.funCongrLeft ℝ ℝ π) '' Q) (gammaM I.card) :=
    ⟨LinearEquiv.funCongrLeft ℝ ℝ π, rfl, hψΓ⟩
  rw [← image_convexHull_linEquiv, ← hconv, g_iso hiso2, g_iso hiso] at h6
  exact h6

lemma g1_caseII (hC2 : Comp2) (hC3 : Comp3) (P : Set (Pt 4)) (hP : InW (Zn 4) P) (hG : 31 ≤ G (Zn 4) P)
    (h4 : rP P = 4) (hno : ¬ CaseI P) : g (Zn 4) P 1 ≤ 8 := by
  obtain ⟨U, hrows, hdet⟩ := exists_U P h4
  obtain ⟨-, I, hI2, hUI⟩ := Sec5.case_II_index2 hC2 P hP hG U hrows hdet hno
  obtain ⟨hiso, -, -, -, hconv, hsat, hsymm, hsub, -⟩ := Sec5.case_II_transfer P hP U hrows hdet
  have hspan : Spans (((fun x => (toReal U).mulVec x) '' P) ∩ subLat U) := by
    refine Sec5.spans_of_image (Sec5.toReal_det_ne_zero hdet) (Sec5.span_latPts P hP) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, by rw [Sec5.subLat_eq_image]; exact ⟨x, hx.2, rfl⟩⟩
  have h6 := g1_of_gammaI hC3 P _ _ I hiso hUI hI2 hG hconv hsat hsymm hsub hspan
  linarith

/-! ### `g_1 ≤ 8` -/

lemma g1_le_8 (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) (hTRI : BoundaryTriangulation) (hC1 : Comp1)
    (hC2 : Comp2) (hC3 : Comp3) (hC5 : Comp5) (hIII : CaseIIITransfer) (P : Set (Pt 4)) (hP : InW (Zn 4) P) :
    g (Zn 4) P 1 ≤ 8 := by
  by_cases hG : G (Zn 4) P ≤ 29
  · exact g1_small hE2 hE3 hTRI P hP hG
  have hG31 := G_ge_31 P hP hG
  rcases Sec5.thm_1_2_case_split P hP with hI | ⟨h4, hno⟩ | hr
  · exact g1_caseI hC1 P hP hG31 hI
  · exact g1_caseII hC2 hC3 P hP hG31 h4 hno
  · obtain ⟨j, S, hS, hiso, -⟩ := hIII P hP hG31 hr
    have h1 := hC5.1 j S hS
    rw [g_iso hiso] at h1
    exact h1

/-! ### The rows -/

/-- Theorem 1.2, l.93-95, proof l.372-374, conditional on the Case III transfer: every `P ∈ W⁴` has
`g_1(P) ≤ 8` and `g_2(P) ≤ 24`. -/
theorem thm_1_2_of (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (hTRI : BoundaryTriangulation) (hC1 : Comp1) (hC2 : Comp2) (hC3 : Comp3) (hC5 : Comp5) (hIII : CaseIIITransfer)
    (P : Set (Pt 4)) (hP : InW (Zn 4) P) : g (Zn 4) P 1 ≤ 8 ∧ g (Zn 4) P 2 ≤ 24 := by
  have h1 := g1_le_8 hE2 hE3 hTRI hC1 hC2 hC3 hC5 hIII P hP
  have h2 := Rows1.prop_4_2_g2 hE1 hE2 hE3 1 (Rows1.det_one_ne 4) P (inW_lat1 hP) (by rw [lat_one']; exact h1)
  rw [lat_one'] at h2
  exact ⟨h1, h2.1.trans h2.2⟩

/-- Theorem 1.2, l.94, conditional on the Case III transfer: Conjecture 1.1 holds for `n = 4`. -/
theorem conj_n4_of (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (hTRI : BoundaryTriangulation) (hC1 : Comp1) (hC2 : Comp2) (hC3 : Comp3) (hC5 : Comp5) (hIII : CaseIIITransfer) :
    WillsConj 4 := by
  intro P hP i hi
  have h12 := thm_1_2_of hE1 hE2 hE3 hTRI hC1 hC2 hC3 hC5 hIII P hP
  interval_cases i
  · exact ((Sec2.conj_i0 4 P hP).trans (Sec2.cube_g 4 0)).le
  · rw [show Nat.choose 4 1 = 4 by decide]
    have : (2 : ℝ) ^ 1 * ((4 : ℕ) : ℝ) = 8 := by norm_num
    linarith [h12.1]
  · rw [show Nat.choose 4 2 = 6 by decide]
    have : (2 : ℝ) ^ 2 * ((6 : ℕ) : ℝ) = 24 := by norm_num
    linarith [h12.2]
  · have h3 := Rows1.prop_4_2_g3 hE1 hE3 1 (Rows1.det_one_ne 4) P (inW_lat1 hP)
    rw [lat_one'] at h3
    rw [show Nat.choose 4 3 = 4 by decide]
    have : (2 : ℝ) ^ 3 * ((4 : ℕ) : ℝ) = 32 := by norm_num
    linarith [h3.1, h3.2]
  · exact Rows1.conj_in hE1 4 P hP

/-- Corollary 1.4, l.105-111, conditional on the Case III transfer: Wills' conjecture holds in `ℝⁿ` (`n ≥ 1`) if and
only if `n ≤ 4`. -/
theorem cor_1_4_of (hEHR : EhrhartThm) (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (hTRI : BoundaryTriangulation) (hVolW : VolW) (hC1 : Comp1) (hC2 : Comp2) (hC3 : Comp3)
    (hC5 : Comp5) (hIII : CaseIIITransfer) (n : ℕ) (hn : 1 ≤ n) : WillsConj n ↔ n ≤ 4 := by
  constructor
  · intro h
    by_contra hlt
    rcases Nat.lt_or_ge n 6 with h6 | h6
    · have hn5 : n = 5 := by omega
      subst hn5
      have h1 := h W Rows1.thm_1_3_mem 1 (by norm_num)
      rw [(Rows1.thm_1_3_g1 hE1 hE2 hVolW).1, Nat.choose_one_right] at h1
      norm_num at h1
    · obtain ⟨m, rfl⟩ : ∃ m, n = 5 + m := ⟨n - 5, by omega⟩
      have hm : 1 ≤ m := by omega
      obtain ⟨hmem, hg1, -, -, -⟩ := Rows1.thm_1_3_prod hEHR hE1 hE2 hVolW m hm
      have h1 := h (prod W (cube m)) hmem 1 (by omega)
      rw [hg1, Nat.choose_one_right] at h1
      have h2 : (2 : ℝ) ^ 1 * ((5 + m : ℕ) : ℝ) = 10 + 2 * m := by push_cast; ring
      linarith
  · intro hle
    interval_cases n
    · exact Rows1.conj_le_two hE1 hE3 1 le_rfl (by norm_num)
    · exact Rows1.conj_le_two hE1 hE3 2 (by norm_num) le_rfl
    · exact Dim3.wills_dim3_proof hE1 hE2 hE3
    · exact conj_n4_of hE1 hE2 hE3 hTRI hC1 hC2 hC3 hC5 hIII

end Wills.S12
