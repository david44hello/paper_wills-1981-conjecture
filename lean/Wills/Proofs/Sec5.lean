/-
Wills/Proofs/Sec5.lean — proofs for Section 5 of "Wills' (1981) conjecture is fully resolved": the set M(P) of integer
functionals, the three cases, Cases I and II, the frame of Case III and Lemma 5.1.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Defs.Basic
import Wills.Defs.Cases
import Wills.Facts.Basic
import Wills.Checks.Computations
import Wills.Proofs.Sec2

open MeasureTheory Pointwise

namespace Wills.Sec5

/-! ### Integer points and integer matrices -/

lemma ofInt_neg {n : ℕ} (z : Fin n → ℤ) : ofInt (-z) = -ofInt z := by
  funext i; simp [ofInt]

lemma neg_Zn (n : ℕ) : -Zn n = Zn n := by
  ext x
  rw [Set.mem_neg]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨-z, by rw [ofInt_neg, hz, neg_neg]⟩
  · rintro ⟨z, rfl⟩
    exact ⟨-z, ofInt_neg z⟩

lemma toReal_mulVec_ofInt {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    (toReal U).mulVec (ofInt z) = ofInt (U.mulVec z) := by
  funext i
  simp [toReal, ofInt, Matrix.mulVec, dotProduct]

lemma det_toReal {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ) : (toReal U).det = (U.det : ℝ) := by
  have := RingHom.map_det (Int.castRingHom ℝ) U
  simpa [toReal] using this.symm

lemma toReal_det_ne_zero {n : ℕ} {U : Matrix (Fin n) (Fin n) ℤ} (h : U.det ≠ 0) : (toReal U).det ≠ 0 := by
  rw [det_toReal]; exact_mod_cast h

lemma toReal_mulVec_Zn {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ) {x : Pt n} (hx : x ∈ Zn n) :
    (toReal U).mulVec x ∈ Zn n := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨U.mulVec z, (toReal_mulVec_ofInt U z).symm⟩

lemma subLat_eq_image (B : Matrix (Fin 4) (Fin 4) ℤ) :
    subLat B = (fun x => (toReal B).mulVec x) '' Zn 4 := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨ofInt z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

lemma subLat_subset_Zn (B : Matrix (Fin 4) (Fin 4) ℤ) : subLat B ⊆ Zn 4 := by
  rw [subLat_eq_image]
  rintro _ ⟨x, hx, rfl⟩
  exact toReal_mulVec_Zn B hx

lemma dot_Zn {n : ℕ} {u x : Pt n} (hu : u ∈ Zn n) (hx : x ∈ Zn n) : ∃ m : ℤ, u ⬝ᵥ x = m := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hx
  exact ⟨a ⬝ᵥ b, by simp [ofInt, dotProduct]⟩

/-- The real matrix with columns `w i ∈ ℤ⁴` is an integer matrix. -/
lemma colMat_int (w : Fin 4 → Pt 4) (hw : ∀ i, w i ∈ Zn 4) :
    ∃ Z : Matrix (Fin 4) (Fin 4) ℤ, colMat w = toReal Z := by
  choose z hz using hw
  refine ⟨Matrix.of fun i j => z j i, ?_⟩
  ext i j
  simp [colMat, toReal, ← hz, ofInt]

lemma cube_inter_Zn_subset (n : ℕ) : cube n ∩ Zn n ⊆ cubePts n := by
  rintro x ⟨hx, z, rfl⟩
  refine ⟨z, fun i => ?_, rfl⟩
  have h : |(z i : ℝ)| ≤ 1 := hx i
  have h' : |z i| ≤ 1 := by exact_mod_cast h
  exact abs_le.1 h'

lemma cubePts_finite (n : ℕ) : (cubePts n).Finite :=
  (Sec2.cube_inter_Zn_finite n).subset (Sec2.cubePts_subset n)

/-! ### Linear images -/

lemma image_convexHull_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Set (Pt n)) :
    (fun x => A.mulVec x) '' convexHull ℝ S = convexHull ℝ ((fun x => A.mulVec x) '' S) :=
  (Matrix.mulVecLin A).image_convexHull S

lemma image_neg_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Set (Pt n)) :
    (fun x => A.mulVec x) '' (-S) = -((fun x => A.mulVec x) '' S) := by
  ext y
  rw [Set.mem_neg]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨-x, hx, by simp [Matrix.mulVec_neg]⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨-x, by rw [Set.mem_neg, neg_neg]; exact hx, ?_⟩
    simp only at hxy
    simp only [Matrix.mulVec_neg]
    rw [hxy, neg_neg]

lemma linEquiv_coe {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    ⇑(Sec2.linEquiv A hA) = fun x => A.mulVec x :=
  funext (Sec2.linEquiv_apply A hA)

lemma mulVec_injective {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    Function.Injective (fun x : Pt n => A.mulVec x) := by
  rw [← linEquiv_coe A hA]
  exact (Sec2.linEquiv A hA).injective

lemma interior_image_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (S : Set (Pt n)) :
    interior ((fun x => A.mulVec x) '' S) = (fun x => A.mulVec x) '' interior S := by
  rw [← linEquiv_coe A hA]
  exact ((Sec2.linEquiv A hA).toHomeomorph.image_interior S).symm

lemma neg_inter_eq {n : ℕ} {Q Γ : Set (Pt n)} (hQ : -Q = Q) (hΓ : -Γ = Γ) : -(Q ∩ Γ) = Q ∩ Γ := by
  ext x
  have h1 : (-x ∈ Q ↔ x ∈ Q) := by rw [← Set.mem_neg, hQ]
  have h2 : (-x ∈ Γ ↔ x ∈ Γ) := by rw [← Set.mem_neg, hΓ]
  simp only [Set.mem_neg, Set.mem_inter_iff, h1, h2]

/-- `P = conv (P ∩ Λ)` for a polytope with vertices in `Λ`. -/
lemma conv_latPts {n : ℕ} {Λ P : Set (Pt n)} (hP : IsLatticePolytope Λ P) : P = convexHull ℝ (P ∩ Λ) := by
  obtain ⟨V, hV, rfl⟩ := hP
  apply Set.Subset.antisymm
  · exact convexHull_mono (fun x hx => ⟨subset_convexHull ℝ _ hx, hV hx⟩)
  · exact convexHull_min Set.inter_subset_left (convex_convexHull ℝ _)

lemma zero_mem_latPts {n : ℕ} {Λ P : Set (Pt n)} (hP : InW Λ P) : (0 : Pt n) ∈ P ∩ Λ := by
  have : (0 : Pt n) ∈ interior P ∩ Λ := by rw [hP.2.2]; rfl
  exact ⟨interior_subset this.1, this.2⟩

/-- The image of a polytope with vertices in `Λ` under `x ↦ Ax` is the convex hull of its points in any `Γ ⊇ AΛ`. -/
lemma image_conv_eq {n : ℕ} {Λ P : Set (Pt n)} (hP : IsLatticePolytope Λ P) (A : Matrix (Fin n) (Fin n) ℝ)
    (Γ : Set (Pt n)) (hΓ : (fun x => A.mulVec x) '' Λ ⊆ Γ) :
    (fun x => A.mulVec x) '' P = convexHull ℝ ((fun x => A.mulVec x) '' P ∩ Γ) := by
  have hPc : P = convexHull ℝ (P ∩ Λ) := conv_latPts hP
  have h1 : (fun x => A.mulVec x) '' P = convexHull ℝ ((fun x => A.mulVec x) '' (P ∩ Λ)) := by
    rw [← image_convexHull_mulVec, ← hPc]
  apply Set.Subset.antisymm
  · refine h1.subset.trans (convexHull_mono ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, hΓ ⟨x, hx.2, rfl⟩⟩
  · apply convexHull_min Set.inter_subset_left
    have hconvP : Convex ℝ P := by rw [hPc]; exact convex_convexHull ℝ _
    exact hconvP.linear_image (Matrix.mulVecLin A)

/-- `x ↦ Ax` (`det A ≠ 0`) carries `W^n_Λ` to `W^n_{AΛ}`. -/
lemma inW_image {n : ℕ} {Λ P : Set (Pt n)} (hP : InW Λ P) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    InW ((fun x => A.mulVec x) '' Λ) ((fun x => A.mulVec x) '' P) := by
  classical
  obtain ⟨⟨V, hV, hPV⟩, hsymm, hint⟩ := hP
  refine ⟨⟨V.image (fun x => A.mulVec x), ?_, ?_⟩, ?_, ?_⟩
  · rw [Finset.coe_image]; exact Set.image_mono hV
  · rw [Finset.coe_image, ← image_convexHull_mulVec, hPV]
  · rw [← image_neg_mulVec, hsymm]
  · rw [interior_image_mulVec A hA, ← Set.image_inter (mulVec_injective A hA), hint, Set.image_singleton]
    simp

/-- Isomorphic pairs have the same lattice-point counts. -/
lemma latCount_iso {n : ℕ} {P Λ P' Λ' : Set (Pt n)} (h : IsoPair P Λ P' Λ') (k : ℕ) :
    latCount Λ' P' k = latCount Λ P k := by
  obtain ⟨φ, hP, hΛ⟩ := h
  have hsmul : (k : ℝ) • P' = φ '' ((k : ℝ) • P) := by rw [← hP, image_smul_set]
  unfold latCount
  rw [hsmul, ← hΛ, ← Set.image_inter φ.injective, Set.ncard_image_of_injective _ φ.injective]

/-- The images of the points of `P` span `ℝ⁴` when those points do. -/
lemma spans_of_image {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : A.det ≠ 0) {S T : Set (Pt 4)}
    (hS : Submodule.span ℝ S = ⊤) (hST : (fun x => A.mulVec x) '' S ⊆ T) : Spans T := by
  have hsurj : LinearMap.range (Matrix.mulVecLin A) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨(Sec2.linEquiv A hA).symm y, ?_⟩
    rw [Matrix.mulVecLin_apply, ← Sec2.linEquiv_apply A hA]
    exact (Sec2.linEquiv A hA).apply_symm_apply y
  unfold Spans
  rw [eq_top_iff]
  calc (⊤ : Submodule ℝ (Pt 4)) = Submodule.map (Matrix.mulVecLin A) (Submodule.span ℝ S) := by
        rw [hS, Submodule.map_top, hsurj]
    _ = Submodule.span ℝ ((fun x => A.mulVec x) '' S) := Submodule.map_span _ _
    _ ≤ Submodule.span ℝ T := Submodule.span_mono hST

/-! ### The lattice points of `P ∈ W⁴` -/

lemma latPts_finite (P : Set (Pt 4)) (hP : InW (Zn 4) P) : (P ∩ Zn 4).Finite :=
  Sec2.Zn_inter_finite (Sec2.latticePolytope_compact_convex hP.1).1.isBounded

/-- The lattice points of `P ∈ W⁴` span `ℝ⁴`. -/
lemma span_latPts (P : Set (Pt 4)) (hP : InW (Zn 4) P) : Submodule.span ℝ (P ∩ Zn 4) = ⊤ := by
  obtain ⟨-, haff⟩ := Sec2.inW_full_dim 4 (Zn 4) P hP
  have hPc := conv_latPts hP.1
  have h1 : affineSpan ℝ (P ∩ Zn 4) = ⊤ := by rw [← affineSpan_convexHull, ← hPc]; exact haff
  rw [eq_top_iff]
  intro x _
  have : x ∈ (affineSpan ℝ (P ∩ Zn 4) : Set (Pt 4)) := by rw [h1, AffineSubspace.top_coe]; trivial
  exact affineSpan_subset_span this

/-- `P ∈ W⁴` has four lattice points with nonzero determinant. -/
lemma exists_basis_pts (P : Set (Pt 4)) (hP : InW (Zn 4) P) :
    ∃ w : Fin 4 → Pt 4, (∀ i, w i ∈ P ∩ Zn 4) ∧ (colMat w).det ≠ 0 := by
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℝ (P ∩ Zn 4)
  rw [span_latPts P hP] at hspan
  let B : Module.Basis b ℝ (Pt 4) := Module.Basis.mk hli (by rw [Subtype.range_coe]; exact hspan.symm.le)
  have : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = 4 := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : Fin 4 ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (e i : Pt 4), fun i => hb (e i).2, ?_⟩
  have hli' : LinearIndependent ℝ (fun i => (e i : Pt 4)) := hli.comp e e.injective
  have hcol : (colMat fun i => (e i : Pt 4)).col = fun i => (e i : Pt 4) := by ext j i; rfl
  rw [← hcol] at hli'
  have hU := Matrix.linearIndependent_col_iff_isUnit.1 hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hU).ne_zero

/-! ### `M(P)` (l.275) -/

/-- l.275: `M(P)` is finite (`P` contains a ball around `0`). -/
theorem M_finite (P : Set (Pt 4)) (hP : InW (Zn 4) P) : (MP P).Finite := by
  obtain ⟨h0, -⟩ := Sec2.inW_full_dim 4 (Zn 4) P hP
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h0
  have hsub : MP P ⊆ Metric.closedBall 0 (2 / ε) ∩ Zn 4 := by
    intro u hu
    refine ⟨?_, hu.1⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    have hmem : Pi.single i (ε / 2) ∈ P := by
      apply interior_subset
      apply hball
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same, Pi.zero_apply, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
        linarith
      · rw [Pi.single_eq_of_ne hj, Pi.zero_apply, dist_self]
        exact hε
    have h1 := hu.2 _ hmem
    rw [dotProduct_single, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ε / 2)] at h1
    rw [Real.norm_eq_abs, le_div_iff₀ hε]
    linarith
  exact (Sec2.Zn_inter_finite Metric.isBounded_closedBall).subset hsub

/-- l.275: `M(P)` is symmetric. -/
theorem M_symm (P : Set (Pt 4)) (u : Pt 4) (hu : u ∈ MP P) : -u ∈ MP P := by
  refine ⟨?_, fun x hx => ?_⟩
  · have : -u ∈ -Zn 4 := by rw [Set.mem_neg, neg_neg]; exact hu.1
    rwa [neg_Zn] at this
  · rw [neg_dotProduct, abs_neg]
    exact hu.2 x hx

/-- l.275: `⟨u, x⟩ ∈ {-1, 0, 1}` for `u ∈ M(P)` and `x ∈ P ∩ ℤ⁴`. -/
theorem M_values (P : Set (Pt 4)) (u : Pt 4) (hu : u ∈ MP P) (x : Pt 4) (hx : x ∈ P ∩ Zn 4) :
    u ⬝ᵥ x = -1 ∨ u ⬝ᵥ x = 0 ∨ u ⬝ᵥ x = 1 := by
  obtain ⟨m, hm⟩ := dot_Zn hu.1 hx.2
  have h1 := hu.2 x hx.1
  rw [hm] at h1 ⊢
  have h2 : |m| ≤ 1 := by exact_mod_cast h1
  have h3 := abs_le.1 h2
  have : m = -1 ∨ m = 0 ∨ m = 1 := by omega
  rcases this with rfl | rfl | rfl <;> simp

lemma rP_le (P : Set (Pt 4)) : rP P ≤ 4 := by
  unfold rP
  calc Module.finrank ℝ (Submodule.span ℝ (MP P)) ≤ Module.finrank ℝ (Pt 4) := Submodule.finrank_le _
    _ = 4 := Module.finrank_fin_fun ℝ

/-- The case split (l.275, Figure 2 l.277-288, l.373): every `P ∈ W⁴` is in Case I, Case II (`r(P) = 4`, no basis)
or Case III (`r(P) ≤ 3`). -/
theorem thm_1_2_case_split (P : Set (Pt 4)) (hP : InW (Zn 4) P) :
    CaseI P ∨ (rP P = 4 ∧ ¬ CaseI P) ∨ rP P ≤ 3 := by
  by_cases h : CaseI P
  · exact Or.inl h
  · have := rP_le P
    by_cases h4 : rP P = 4
    · exact Or.inr (Or.inl ⟨h4, h⟩)
    · exact Or.inr (Or.inr (by omega))

/-! ### Cases I and II (l.291-304) -/

/-- If the rows of `U` lie in `M(P)`, then `UP ⊂ C_4`. -/
lemma image_subset_cube (P : Set (Pt 4)) (U : Matrix (Fin 4) (Fin 4) ℤ) (hrows : ∀ i, ofInt (U i) ∈ MP P) :
    (fun x => (toReal U).mulVec x) '' P ⊆ cube 4 := by
  rintro _ ⟨x, hx, rfl⟩ i
  exact (hrows i).2 x hx

/-- Case I, l.291 (and l.151 (a), Figure 2): if the rows of `U ∈ GL_4(ℤ)` lie in `M(P)`, then `UP ⊂ C_4`,
`UP = conv S` for `S = UP ∩ ℤ⁴ ⊂ {-1,0,1}⁴`, `S` is symmetric and saturated, and `P` is unimodularly equivalent to
`UP`. -/
theorem case_I (P : Set (Pt 4)) (hP : InW (Zn 4) P) (U : Matrix (Fin 4) (Fin 4) ℤ) (hU : IsGLZ U)
    (hrows : ∀ i, ofInt (U i) ∈ MP P) :
    ((fun x => (toReal U).mulVec x) '' P) ⊆ cube 4 ∧
      (fun x => (toReal U).mulVec x) '' P = convexHull ℝ (((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4) ∧
      ((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4 ⊆ cubePts 4 ∧
      -(((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4) = ((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4 ∧
      Saturated (Zn 4) (((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4) ∧
      UnimodEquiv P ((fun x => (toReal U).mulVec x) '' P) := by
  have hcube := image_subset_cube P U hrows
  have hZ : (fun x => (toReal U).mulVec x) '' Zn 4 ⊆ Zn 4 := by
    rintro _ ⟨x, hx, rfl⟩; exact toReal_mulVec_Zn U hx
  have hconv := image_conv_eq hP.1 (toReal U) (Zn 4) hZ
  have hsymm : -((fun x => (toReal U).mulVec x) '' P) = (fun x => (toReal U).mulVec x) '' P := by
    rw [← image_neg_mulVec, hP.2.1]
  refine ⟨hcube, hconv, ?_, neg_inter_eq hsymm (neg_Zn 4), ?_, ⟨U, hU, rfl⟩⟩
  · exact fun x hx => cube_inter_Zn_subset 4 ⟨hcube hx.1, hx.2⟩
  · show convexHull ℝ _ ∩ _ = _
    rw [← hconv]

/-- Case II, l.294: if the rows of `U` lie in `M(P)` and are linearly independent but `M(P)` contains no basis, then
`d = |det U| ≥ 2`. -/
theorem case_II_d_ge_2 (P : Set (Pt 4)) (hP : InW (Zn 4) P) (hno : ¬ CaseI P) (U : Matrix (Fin 4) (Fin 4) ℤ)
    (hrows : ∀ i, ofInt (U i) ∈ MP P) (hdet : U.det ≠ 0) : 2 ≤ |U.det| := by
  by_contra h
  push Not at h
  have h0 : 0 < |U.det| := abs_pos.2 hdet
  have h1 : |U.det| = 1 := by omega
  exact hno ⟨U, (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).1 h1, hrows⟩

/-- Case II, l.294-296: `x ↦ Ux` carries `ℤ⁴` onto `Γ = U ℤ⁴` and `P` into `C_4`; `(P, ℤ⁴) ≅ (UP, Γ)`,
`UP ∈ W^4_Γ`, `L_{UP,Γ} = L_P`, `UP = conv S` for the `Γ`-saturated symmetric `S = UP ∩ Γ ⊂ Γ ∩ {-1,0,1}⁴`, and
`G(P) ≤ #(Γ ∩ {-1,0,1}⁴)`. -/
theorem case_II_transfer (P : Set (Pt 4)) (hP : InW (Zn 4) P) (U : Matrix (Fin 4) (Fin 4) ℤ)
    (hrows : ∀ i, ofInt (U i) ∈ MP P) (hdet : U.det ≠ 0) :
    IsoPair P (Zn 4) ((fun x => (toReal U).mulVec x) '' P) (subLat U) ∧
      InW (subLat U) ((fun x => (toReal U).mulVec x) '' P) ∧
      ((fun x => (toReal U).mulVec x) '' P) ⊆ cube 4 ∧
      (∀ k, latCount (subLat U) ((fun x => (toReal U).mulVec x) '' P) k = latCount (Zn 4) P k) ∧
      (fun x => (toReal U).mulVec x) '' P =
        convexHull ℝ (((fun x => (toReal U).mulVec x) '' P) ∩ subLat U) ∧
      Saturated (subLat U) (((fun x => (toReal U).mulVec x) '' P) ∩ subLat U) ∧
      -(((fun x => (toReal U).mulVec x) '' P) ∩ subLat U) = ((fun x => (toReal U).mulVec x) '' P) ∩ subLat U ∧
      ((fun x => (toReal U).mulVec x) '' P) ∩ subLat U ⊆ subLat U ∩ cubePts 4 ∧
      G (Zn 4) P ≤ (subLat U ∩ cubePts 4).ncard := by
  have hA := toReal_det_ne_zero hdet
  have hiso : IsoPair P (Zn 4) ((fun x => (toReal U).mulVec x) '' P) (subLat U) := by
    refine ⟨(Sec2.linEquiv (toReal U) hA).toLinearEquiv, ?_, ?_⟩
    · show (Sec2.linEquiv (toReal U) hA) '' P = _
      rw [linEquiv_coe]
    · show (Sec2.linEquiv (toReal U) hA) '' Zn 4 = _
      rw [linEquiv_coe, subLat_eq_image]
  have hcube := image_subset_cube P U hrows
  have hconv := image_conv_eq hP.1 (toReal U) (subLat U) (by rw [subLat_eq_image])
  have hsymm : -((fun x => (toReal U).mulVec x) '' P) = (fun x => (toReal U).mulVec x) '' P := by
    rw [← image_neg_mulVec, hP.2.1]
  have hsymmΓ : -subLat U = subLat U := by rw [subLat_eq_image, ← image_neg_mulVec, neg_Zn]
  have hsub : ((fun x => (toReal U).mulVec x) '' P) ∩ subLat U ⊆ subLat U ∩ cubePts 4 :=
    fun x hx => ⟨hx.2, cube_inter_Zn_subset 4 ⟨hcube hx.1, subLat_subset_Zn U hx.2⟩⟩
  refine ⟨hiso, ?_, hcube, latCount_iso hiso, hconv, ?_, neg_inter_eq hsymm hsymmΓ, hsub, ?_⟩
  · rw [subLat_eq_image]; exact inW_image hP (toReal U) hA
  · show convexHull ℝ _ ∩ _ = _
    rw [← hconv]
  · have hfin : (subLat U ∩ cubePts 4).Finite := (cubePts_finite 4).subset Set.inter_subset_right
    calc G (Zn 4) P = ((fun x => (toReal U).mulVec x) '' (P ∩ Zn 4)).ncard :=
          (Set.ncard_image_of_injective _ (mulVec_injective _ hA)).symm
      _ = (((fun x => (toReal U).mulVec x) '' P) ∩ subLat U).ncard := by
          rw [Set.image_inter (mulVec_injective _ hA), subLat_eq_image]
      _ ≤ (subLat U ∩ cubePts 4).ncard := Set.ncard_le_ncard hsub hfin

/-! ### Hadamard's inequality for `{-1,0,1}` matrices of size 4 (l.298) -/

/-- The values `-1, 0, 1`. -/
def vals3 : List ℤ := [-1, 0, 1]

/-- Kernel check: every `3 × 3` determinant with entries in `{-1,0,1}` is at most `4` in absolute value
(the `3⁹` cases, in the expansion of `Matrix.det_fin_three`). -/
lemma det3_check : ∀ a ∈ vals3, ∀ b ∈ vals3, ∀ c ∈ vals3, ∀ d ∈ vals3, ∀ e ∈ vals3, ∀ f ∈ vals3,
    ∀ g ∈ vals3, ∀ h ∈ vals3, ∀ i ∈ vals3,
      |a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g| ≤ 4 := by
  decide +kernel

lemma mem_vals3 {a : ℤ} (h : |a| ≤ 1) : a ∈ vals3 := by
  have h' := abs_le.1 h
  have : a = -1 ∨ a = 0 ∨ a = 1 := by omega
  rcases this with rfl | rfl | rfl <;> simp [vals3]

lemma det3_le_4 (M : Matrix (Fin 3) (Fin 3) ℤ) (hM : ∀ i j, |M i j| ≤ 1) : |M.det| ≤ 4 := by
  rw [Matrix.det_fin_three]
  exact det3_check _ (mem_vals3 (hM 0 0)) _ (mem_vals3 (hM 0 1)) _ (mem_vals3 (hM 0 2))
    _ (mem_vals3 (hM 1 0)) _ (mem_vals3 (hM 1 1)) _ (mem_vals3 (hM 1 2))
    _ (mem_vals3 (hM 2 0)) _ (mem_vals3 (hM 2 1)) _ (mem_vals3 (hM 2 2))

/-- Hadamard's inequality for `{-1,0,1}` matrices of size 4 (used at l.298): `|det| ≤ 16`. Proof: expand along the
first row; every `3 × 3` minor is at most `4` (kernel check). -/
theorem det_cube_le_16 (M : Matrix (Fin 4) (Fin 4) ℤ) (hM : ∀ i j, |M i j| ≤ 1) : |M.det| ≤ 16 := by
  rw [Matrix.det_succ_row_zero]
  calc |∑ j : Fin 4, (-1) ^ (j : ℕ) * M 0 j * (M.submatrix Fin.succ j.succAbove).det|
      ≤ ∑ j : Fin 4, |(-1) ^ (j : ℕ) * M 0 j * (M.submatrix Fin.succ j.succAbove).det| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 4, (4 : ℤ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        have h1 := hM 0 j
        have h2 := det3_le_4 (M.submatrix Fin.succ j.succAbove) (fun a b => hM _ _)
        nlinarith [abs_nonneg (M 0 j), abs_nonneg (M.submatrix Fin.succ j.succAbove).det]
    _ = 16 := by simp

/-- Case II, l.298: `d ≤ 16`. The lattice points `w_j` of `P` with `det(w) ≠ 0` give `Z` with columns `w_j`;
`UZ` has entries `⟨u_i, w_j⟩ ∈ {-1,0,1}`, so `d ≤ d |det Z| = |det UZ| ≤ 16`. -/
theorem case_II_d_le_16 (P : Set (Pt 4)) (hP : InW (Zn 4) P) (U : Matrix (Fin 4) (Fin 4) ℤ)
    (hrows : ∀ i, ofInt (U i) ∈ MP P) (hdet : U.det ≠ 0) : |U.det| ≤ 16 := by
  obtain ⟨w, hw, hwdet⟩ := exists_basis_pts P hP
  obtain ⟨Z, hZ⟩ := colMat_int w (fun i => (hw i).2)
  have hZdet : Z.det ≠ 0 := by
    rw [hZ, det_toReal] at hwdet; exact_mod_cast hwdet
  have hent : ∀ i j, |(U * Z) i j| ≤ 1 := by
    intro i j
    have hwj : w j = fun k => (Z k j : ℝ) := by
      funext k
      have := congrFun (congrFun hZ k) j
      simpa [colMat, toReal] using this
    have h1 := (hrows i).2 (w j) (hw j).1
    have h2 : ofInt (U i) ⬝ᵥ w j = (((U * Z) i j : ℤ) : ℝ) := by
      rw [hwj, Matrix.mul_apply]; push_cast; simp [ofInt, dotProduct]
    rw [h2] at h1
    exact_mod_cast h1
  have h16 := det_cube_le_16 (U * Z) hent
  rw [Matrix.det_mul, abs_mul] at h16
  have h1 : 1 ≤ |Z.det| := Int.one_le_abs hZdet
  nlinarith [abs_nonneg U.det]

/-! ### The sublattices `Γ_I` (l.300-302) -/

lemma ofInt_mem_gammaI (I : Finset (Fin 4)) (z : Fin 4 → ℤ) :
    ofInt z ∈ gammaI I ↔ Even (∑ i ∈ I, z i) := by
  constructor
  · rintro ⟨z', hz', he⟩
    rwa [Sec2.ofInt_injective hz']
  · intro h
    exact ⟨z, rfl, h⟩

/-- Case II, l.300: a point of `{-1,0,1}⁴` lies in `Γ_I` exactly when an even number of its coordinates in `I` are
nonzero. -/
theorem gammaI_mem_iff (I : Finset (Fin 4)) (z : Fin 4 → ℤ) (hz : ∀ i, -1 ≤ z i ∧ z i ≤ 1) :
    ofInt z ∈ gammaI I ↔ Even (I.filter (fun i => z i ≠ 0)).card := by
  rw [ofInt_mem_gammaI, Finset.card_filter]
  have hdiff : Even (∑ i ∈ I, (z i - if z i ≠ 0 then 1 else 0)) := by
    apply Finset.even_sum
    intro i _
    rcases hz i with ⟨h1, h2⟩
    have : z i = -1 ∨ z i = 0 ∨ z i = 1 := by omega
    rcases this with h | h | h
    · rw [h]; exact ⟨-1, by norm_num⟩
    · rw [h]; exact ⟨0, by norm_num⟩
    · rw [h]; exact ⟨0, by norm_num⟩
  have hsplit : ∑ i ∈ I, z i = (∑ i ∈ I, (z i - if z i ≠ 0 then 1 else 0)) +
      ((∑ i ∈ I, if z i ≠ 0 then 1 else 0 : ℕ) : ℤ) := by
    rw [Nat.cast_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [hsplit, Int.even_add, Int.even_coe_nat]
  exact ⟨fun h => h.1 hdiff, fun h => ⟨fun _ => h, fun _ => hdiff⟩⟩

/-- The points of `Γ_I ∩ {-1,0,1}⁴`, as integer vectors. -/
def gamFin (I : Finset (Fin 4)) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-1 : ℤ) 1).filter (fun z => (∑ i ∈ I, z i) % 2 = 0)

/-- Kernel check: `2 #(Γ_I ∩ {-1,0,1}⁴) = 3^{4-m} (3^m + (-1)^m)`, `m = |I|`, for the 15 nonempty `I`. -/
lemma gamma_count_check : ∀ I : Finset (Fin 4), I.Nonempty →
    2 * ((gamFin I).card : ℤ) = 3 ^ (4 - I.card) * (3 ^ I.card + (-1) ^ I.card) := by
  decide +kernel

lemma gammaI_cubePts_eq (I : Finset (Fin 4)) : gammaI I ∩ cubePts 4 = ofInt '' ↑(gamFin I) := by
  ext x
  constructor
  · rintro ⟨hxg, z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    rw [Finset.mem_coe, gamFin, Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨fun i => Finset.mem_Icc.2 (hz i), Int.even_iff.1 ((ofInt_mem_gammaI I z).1 hxg)⟩
  · rintro ⟨z, hz, rfl⟩
    rw [Finset.mem_coe, gamFin, Finset.mem_filter, Fintype.mem_piFinset] at hz
    exact ⟨(ofInt_mem_gammaI I z).2 (Int.even_iff.2 hz.2), z, fun i => Finset.mem_Icc.1 (hz.1 i), rfl⟩

/-- Case II, l.302: `#(Γ_I ∩ {-1,0,1}⁴) = 3^{4-m} (3^m + (-1)^m)/2 = 27, 45, 39, 41` for `m = |I| = 1, 2, 3, 4`. -/
theorem gammaI_counts (I : Finset (Fin 4)) (hI : I.Nonempty) :
    2 * ((gammaI I ∩ cubePts 4).ncard : ℤ) = 3 ^ (4 - I.card) * (3 ^ I.card + (-1) ^ I.card) ∧
      (I.card = 1 → (gammaI I ∩ cubePts 4).ncard = 27) ∧ (I.card = 2 → (gammaI I ∩ cubePts 4).ncard = 45) ∧
      (I.card = 3 → (gammaI I ∩ cubePts 4).ncard = 39) ∧ (I.card = 4 → (gammaI I ∩ cubePts 4).ncard = 41) := by
  have hn : (gammaI I ∩ cubePts 4).ncard = (gamFin I).card := by
    rw [gammaI_cubePts_eq, Set.ncard_image_of_injective _ Sec2.ofInt_injective, Set.ncard_coe_finset]
  have hc := gamma_count_check I hI
  rw [hn]
  refine ⟨hc, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] at hc <;> norm_num at hc <;> omega

/-! ### The frame (l.307) -/

/-- Case III, l.307: `P ∈ W⁴` has a frame, and `D ≥ 1` since `P` spans `ℝ⁴`. -/
theorem frame_D_pos (P : Set (Pt 4)) (hP : InW (Zn 4) P) :
    (∃ v, IsFrame P v) ∧ ∀ v, IsFrame P v → 1 ≤ |(colMat v).det| := by
  have hfin := latPts_finite P hP
  have h0 : (0 : Pt 4) ∈ P ∩ Zn 4 := zero_mem_latPts hP
  constructor
  · classical
    have : Fintype ↥(P ∩ Zn 4) := hfin.fintype
    obtain ⟨w, -, hw⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 4 → ↥(P ∩ Zn 4)))
      (fun w => |(colMat (fun i => (w i : Pt 4))).det|) ⟨fun _ => ⟨0, h0⟩, Finset.mem_univ _⟩
    exact ⟨fun i => (w i : Pt 4), fun i => (w i).2, fun w' hw' => hw (fun i => ⟨w' i, hw' i⟩) (Finset.mem_univ _)⟩
  · intro v hv
    obtain ⟨w, hw, hwdet⟩ := exists_basis_pts P hP
    obtain ⟨Z, hZ⟩ := colMat_int w (fun i => (hw i).2)
    have hZdet : Z.det ≠ 0 := by
      rw [hZ, det_toReal] at hwdet; exact_mod_cast hwdet
    have h1 : 1 ≤ |(colMat w).det| := by
      rw [hZ, det_toReal]
      have h2 : (1 : ℤ) ≤ |Z.det| := Int.one_le_abs hZdet
      exact_mod_cast h2
    exact h1.trans (hv.2 w hw)

/-! ### The sublattices of index 2 (l.300, l.304) -/

/-- `B ℤ⁴` as an additive subgroup of `ℤ⁴`. -/
def rangeB (B : Matrix (Fin 4) (Fin 4) ℤ) : AddSubgroup (Fin 4 → ℤ) :=
  (LinearMap.range B.mulVecLin).toAddSubgroup

lemma mem_rangeB (B : Matrix (Fin 4) (Fin 4) ℤ) (y : Fin 4 → ℤ) : y ∈ rangeB B ↔ ∃ z, B.mulVec z = y := by
  rw [rangeB, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

lemma ofInt_mem_subLat (B : Matrix (Fin 4) (Fin 4) ℤ) (y : Fin 4 → ℤ) :
    ofInt y ∈ subLat B ↔ y ∈ rangeB B := by
  rw [mem_rangeB]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : ofInt (B.mulVec z) = ofInt y := by rw [← toReal_mulVec_ofInt]; exact hz
    exact ⟨z, Sec2.ofInt_injective hz'⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, toReal_mulVec_ofInt B z⟩

/-- The index of `B ℤ⁴` in `ℤ⁴` is `|det B|` (Mathlib: Smith normal form). -/
lemma rangeB_index (B : Matrix (Fin 4) (Fin 4) ℤ) (hB : B.det ≠ 0) : (rangeB B).index = B.det.natAbs := by
  have hinj : Function.Injective B.mulVecLin := by
    intro z z' h
    have h' : (toReal B).mulVec (ofInt z) = (toReal B).mulVec (ofInt z') := by
      rw [toReal_mulVec_ofInt, toReal_mulVec_ofInt]; exact congrArg ofInt h
    exact Sec2.ofInt_injective (mulVec_injective _ (toReal_det_ne_zero hB) h')
  have h := Submodule.natAbs_det_equiv (LinearMap.range B.mulVecLin) (LinearEquiv.ofInjective B.mulVecLin hinj)
  have hdet : LinearMap.det ((LinearMap.range B.mulVecLin).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((LinearEquiv.ofInjective B.mulVecLin hinj) :
        (Fin 4 → ℤ) →+ LinearMap.range B.mulVecLin)) = B.det := by
    have : (LinearMap.range B.mulVecLin).subtype ∘ₗ AddMonoidHom.toIntLinearMap
        ((LinearEquiv.ofInjective B.mulVecLin hinj) : (Fin 4 → ℤ) →+ LinearMap.range B.mulVecLin) =
        Matrix.toLin' B := by
      apply LinearMap.ext; intro x; rw [Matrix.toLin'_apply]; rfl
    rw [this, LinearMap.det_toLin']
  exact (show (rangeB B).index = Nat.card ((Fin 4 → ℤ) ⧸ LinearMap.range B.mulVecLin) from rfl).trans
    (h.symm.trans (congrArg Int.natAbs hdet))

/-- An additive subgroup of index 2 of `ℤ⁴` is `{x : Σ_{i ∈ I} x_i even}` for a nonempty `I`. -/
lemma index_two_parity (H : AddSubgroup (Fin 4 → ℤ)) (hH : H.index = 2) :
    ∃ I : Finset (Fin 4), I.Nonempty ∧ ∀ x, x ∈ H ↔ Even (∑ i ∈ I, x i) := by
  classical
  obtain ⟨a, ha⟩ := AddSubgroup.index_eq_two_iff.1 hH
  have hout : ∀ b, b ∉ H → b + a ∈ H := fun b hb => by
    rcases ha b with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hb
  have hin : ∀ b, b ∈ H → b + a ∉ H := fun b hb => by
    rcases ha b with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact absurd hb h2
    · exact h2
  have ha0 : a ∉ H := by have := hin 0 H.zero_mem; rwa [zero_add] at this
  have haa : a + a ∈ H := hout a ha0
  have hsum1 : ∀ x y, x ∈ H → y ∉ H → x + y ∉ H := fun x y hx hy hxy => hy (by
    have := H.sub_mem hxy hx; rwa [add_sub_cancel_left] at this)
  have hsum2 : ∀ x y, x ∉ H → y ∉ H → x + y ∈ H := fun x y hx hy => by
    have h2 := H.sub_mem (H.add_mem (hout x hx) (hout y hy)) haa
    have : x + a + (y + a) - (a + a) = x + y := by abel
    rwa [this] at h2
  let q : (Fin 4 → ℤ) →+ ZMod 2 := AddMonoidHom.mk' (fun x => if x ∈ H then 0 else 1) (by
    intro x y
    by_cases hx : x ∈ H <;> by_cases hy : y ∈ H
    · simp [hx, hy, H.add_mem hx hy]
    · simp [hx, hy, hsum1 x y hx hy]
    · have : x + y ∉ H := by rw [add_comm]; exact hsum1 y x hy hx
      simp [hx, hy, this]
    · simp [hx, hy, hsum2 x y hx hy]; decide)
  have hmem : ∀ x, x ∈ H ↔ q x = 0 := fun x => by
    by_cases hx : x ∈ H <;> simp [q, hx]
  have hq : ∀ x, q x = ((∑ i ∈ Finset.univ.filter (fun i => Pi.single i (1 : ℤ) ∉ H), x i : ℤ) : ZMod 2) := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [map_sum, Finset.sum_filter, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    by_cases he : Pi.single i (1 : ℤ) ∈ H <;> simp [q, he]
  refine ⟨Finset.univ.filter (fun i => Pi.single i (1 : ℤ) ∉ H), ?_, fun x => ?_⟩
  · by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply ha0
    rw [hmem, hq, hne, Finset.sum_empty, Int.cast_zero]
  · rw [hmem, hq, ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd, Nat.cast_ofNat]

/-- l.300, first half: a sublattice `B ℤ⁴` of index 2 is some `Γ_I`, `I` nonempty. -/
lemma subLat_eq_gammaI_of_index2 (B : Matrix (Fin 4) (Fin 4) ℤ) (hB : |B.det| = 2) :
    ∃ I : Finset (Fin 4), I.Nonempty ∧ subLat B = gammaI I := by
  have hB0 : B.det ≠ 0 := by intro h; rw [h] at hB; norm_num at hB
  have hidx : (rangeB B).index = 2 := by
    rw [rangeB_index B hB0]
    have h1 : ((B.det.natAbs : ℕ) : ℤ) = 2 := by rw [Int.natCast_natAbs, hB]
    exact_mod_cast h1
  obtain ⟨I, hI, hpar⟩ := index_two_parity (rangeB B) hidx
  refine ⟨I, hI, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := subLat_subset_Zn B hx
    exact (ofInt_mem_gammaI I y).2 ((hpar y).1 ((ofInt_mem_subLat B y).1 hx))
  · rintro ⟨y, rfl, hy⟩
    exact (ofInt_mem_subLat B y).2 ((hpar y).2 hy)

/-- The first element of `I` (`0` if `I` is empty). -/
def i0 (I : Finset (Fin 4)) : Fin 4 := if h : I.Nonempty then I.min' h else 0

/-- A basis of `Γ_I`, as the columns of an upper triangular matrix: `e_j + [j ∈ I] e_{i₀}` (`j ≠ i₀`) and `2 e_{i₀}`,
`i₀` the first element of `I`. -/
def matF (I : Finset (Fin 4)) (i j : Fin 4) : ℤ :=
  if i = i0 I then (if j = i0 I then 2 else if j ∈ I then 1 else 0) else (if i = j then 1 else 0)

/-- `matF I` as a matrix. -/
def matI (I : Finset (Fin 4)) : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of (matF I)

/-- Kernel check over the 15 nonempty `I`: `matI I` is upper triangular with diagonal product `2`, the sum of each
column over `I` is even, and the column `i ∉ I` is `e_i`. -/
lemma matI_check : ∀ I : Finset (Fin 4), I.Nonempty →
    (∀ i j : Fin 4, i ≤ j ∨ matF I i j = 0) ∧ (∏ i, matF I i i) = 2 ∧
      (∀ j, (∑ k ∈ I, matF I k j) % 2 = 0) ∧ (∀ i, i ∉ I → ∀ k, matF I k i = if k = i then 1 else 0) := by
  decide +kernel

lemma matI_det (I : Finset (Fin 4)) (hI : I.Nonempty) : (matI I).det = 2 := by
  obtain ⟨htri, hprod, -, -⟩ := matI_check I hI
  rw [Matrix.det_of_isUpperTriangular (M := matI I) (fun i j hij => (htri i j).resolve_left (not_le.2 hij))]
  exact hprod

lemma subLat_matI_subset (I : Finset (Fin 4)) (hI : I.Nonempty) : subLat (matI I) ⊆ gammaI I := by
  obtain ⟨-, -, hcol, -⟩ := matI_check I hI
  rintro _ ⟨z, rfl⟩
  refine ⟨(matI I).mulVec z, toReal_mulVec_ofInt _ _, ?_⟩
  have : ∑ k ∈ I, (matI I).mulVec z k = ∑ j, (∑ k ∈ I, matI I k j) * z j := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_comm
  rw [this]
  apply Finset.even_sum
  intro j _
  exact (Int.even_iff.2 (hcol j)).mul_right _

lemma ofInt_single_mem_gammaI (i : Fin 4) (K : Finset (Fin 4)) :
    ofInt (Pi.single i (1 : ℤ)) ∈ gammaI K ↔ i ∉ K := by
  rw [ofInt_mem_gammaI]
  by_cases h : i ∈ K <;> simp [Pi.single_apply, h]

/-- l.300, second half: every `Γ_I`, `I` nonempty, is a sublattice `B ℤ⁴` with `|det B| = 2`. -/
lemma gammaI_eq_subLat (I : Finset (Fin 4)) (hI : I.Nonempty) :
    |(matI I).det| = 2 ∧ subLat (matI I) = gammaI I := by
  have habs : |(matI I).det| = 2 := by rw [matI_det I hI]; norm_num
  refine ⟨habs, ?_⟩
  obtain ⟨J, -, hJ⟩ := subLat_eq_gammaI_of_index2 (matI I) habs
  obtain ⟨-, -, -, hunit⟩ := matI_check I hI
  have hJI : J = I := by
    ext i
    constructor
    · intro hiJ
      by_contra hiI
      have hmem : ofInt (Pi.single i (1 : ℤ)) ∈ subLat (matI I) := by
        refine ⟨Pi.single i 1, ?_⟩
        show (toReal (matI I)).mulVec (ofInt (Pi.single i 1)) = _
        rw [toReal_mulVec_ofInt]
        congr 1
        funext k
        rw [Matrix.mulVec_single_one]
        show matF I k i = _
        rw [hunit i hiI k, Pi.single_apply]
      rw [hJ, ofInt_single_mem_gammaI] at hmem
      exact hmem hiJ
    · intro hiI
      by_contra hiJ
      have h1 : ofInt (Pi.single i (1 : ℤ)) ∈ gammaI J := (ofInt_single_mem_gammaI i J).2 hiJ
      rw [← hJ] at h1
      exact (ofInt_single_mem_gammaI i I).1 (subLat_matI_subset I hI h1) hiI
  rw [hJ, hJI]

/-- Case II, l.300: the sublattices of `ℤ⁴` of index 2 are exactly the `Γ_I`, `I` nonempty. -/
theorem index2_eq_gammaI :
    (∀ B : Matrix (Fin 4) (Fin 4) ℤ, |B.det| = 2 → ∃ I : Finset (Fin 4), I.Nonempty ∧ subLat B = gammaI I) ∧
      ∀ I : Finset (Fin 4), I.Nonempty → ∃ B : Matrix (Fin 4) (Fin 4) ℤ, |B.det| = 2 ∧ subLat B = gammaI I :=
  ⟨subLat_eq_gammaI_of_index2, fun I hI => ⟨matI I, gammaI_eq_subLat I hI⟩⟩

/-- Case II, l.304 (and l.151 (b), Figure 2): since `27 < 31`, in Case II `d = 2` and `Γ = Γ_I` with
`|I| ∈ {2, 3, 4}` (using Computation 2). -/
theorem case_II_index2 (hC2 : Comp2) (P : Set (Pt 4)) (hP : InW (Zn 4) P) (hG : 31 ≤ G (Zn 4) P)
    (U : Matrix (Fin 4) (Fin 4) ℤ) (hrows : ∀ i, ofInt (U i) ∈ MP P) (hdet : U.det ≠ 0) (hno : ¬ CaseI P) :
    |U.det| = 2 ∧ ∃ I : Finset (Fin 4), 2 ≤ I.card ∧ subLat U = gammaI I := by
  have hd2 := case_II_d_ge_2 P hP hno U hrows hdet
  have hd16 := case_II_d_le_16 P hP U hrows hdet
  obtain ⟨-, -, -, -, -, -, -, hsub, hGle⟩ := case_II_transfer P hP U hrows hdet
  have hspan : Spans (subLat U ∩ cubePts 4) := by
    refine spans_of_image (toReal_det_ne_zero hdet) (span_latPts P hP) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hsub ⟨⟨x, hx.1, rfl⟩, by rw [subLat_eq_image]; exact ⟨x, hx.2, rfl⟩⟩
  have hle := hC2.1 U hd2 hd16 hspan
  have hdet2 : |U.det| = 2 := by
    by_contra h
    simp only [h, ite_false] at hle
    omega
  refine ⟨hdet2, ?_⟩
  obtain ⟨I, hI, hUI⟩ := index2_eq_gammaI.1 U hdet2
  refine ⟨I, ?_, hUI⟩
  by_contra hcard
  have h1 : I.card = 1 := by have := Finset.card_pos.2 hI; omega
  have h27 := (gammaI_counts I hI).2.1 h1
  rw [← hUI] at h27
  omega

/-! ### Inverse matrices and the lattice `A⁻¹ ℤ⁴` -/

lemma abs_add' (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  simpa [Real.norm_eq_abs] using norm_add_le a b

lemma inv_mulVec_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (x : Pt n) :
    A⁻¹.mulVec (A.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.2 hA), Matrix.one_mulVec]

lemma mulVec_inv_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (x : Pt n) :
    A.mulVec (A⁻¹.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 hA), Matrix.one_mulVec]

lemma det_inv_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) : (A⁻¹).det ≠ 0 := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero hA

lemma lat_eq_image {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : lat A = (fun x => A.mulVec x) '' Zn n := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨ofInt z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

/-- `x ∈ A⁻¹ ℤⁿ` iff `Ax ∈ ℤⁿ`. -/
lemma mem_lat_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (x : Pt n) :
    x ∈ lat A⁻¹ ↔ A.mulVec x ∈ Zn n := by
  constructor
  · rintro ⟨z, rfl⟩
    show A.mulVec (A⁻¹.mulVec (ofInt z)) ∈ Zn n
    rw [mulVec_inv_mulVec A hA]
    exact ⟨z, rfl⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    show A⁻¹.mulVec (ofInt z) = x
    rw [hz, inv_mulVec_mulVec A hA]

lemma ofInt_single (i : Fin 4) : ofInt (Pi.single i (1 : ℤ)) = unitVec i := by
  funext j
  by_cases h : j = i
  · subst h; simp [ofInt, unitVec]
  · simp [ofInt, unitVec, h]

lemma ofInt_add {n : ℕ} (a b : Fin n → ℤ) : ofInt (a + b) = ofInt a + ofInt b := by
  funext i; simp [ofInt]

lemma ofInt_sub {n : ℕ} (a b : Fin n → ℤ) : ofInt (a - b) = ofInt a - ofInt b := by
  funext i; simp [ofInt]

/-- The number of points of `W⁻¹ ℤ⁴` in `[0,1)⁴` is `|det W|` (`W` an integer matrix): `x ↦ Wx` is a bijection
onto `ℤ⁴ / W ℤ⁴`, whose order is `|det W|`. -/
lemma indexOver_eq (W : Matrix (Fin 4) (Fin 4) ℤ) (hW : W.det ≠ 0) :
    indexOver (lat (toReal W)⁻¹) = W.det.natAbs := by
  have hA : (toReal W).det ≠ 0 := toReal_det_ne_zero hW
  let T : Set (Pt 4) := lat (toReal W)⁻¹ ∩ {x : Pt 4 | ∀ i, 0 ≤ x i ∧ x i < 1}
  let fl : Pt 4 → (Fin 4 → ℤ) := fun y i => ⌊y i⌋
  have hfl : ∀ y ∈ Zn 4, ofInt (fl y) = y := by
    rintro _ ⟨z, rfl⟩
    funext i
    simp [fl, ofInt]
  have hfl' : ∀ w : Fin 4 → ℤ, fl (ofInt w) = w := fun w => by funext i; simp [fl, ofInt]
  let f : T → (Fin 4 → ℤ) ⧸ rangeB W := fun x => QuotientAddGroup.mk (fl ((toReal W).mulVec x))
  have hinj : Function.Injective f := by
    rintro ⟨x, hxl, hxb⟩ ⟨x', hxl', hxb'⟩ hxx
    obtain ⟨a, ha⟩ := (mem_lat_inv _ hA x).1 hxl
    obtain ⟨a', ha'⟩ := (mem_lat_inv _ hA x').1 hxl'
    rw [QuotientAddGroup.eq, mem_rangeB] at hxx
    obtain ⟨m, hm⟩ := hxx
    have hm' : W.mulVec m = -a + a' := by
      have e1 : fl ((toReal W).mulVec x) = a := by rw [← ha, hfl']
      have e2 : fl ((toReal W).mulVec x') = a' := by rw [← ha', hfl']
      rw [← e1, ← e2]
      exact hm
    have h1 : (toReal W).mulVec (ofInt m) = (toReal W).mulVec (x' - x) := by
      rw [toReal_mulVec_ofInt, hm', ofInt_add, ofInt_neg, ha, ha', Matrix.mulVec_sub]
      abel
    have h2 : x' - x = ofInt m := (mulVec_injective _ hA h1).symm
    have h3 : x' - x = 0 := Sec2.Zn_abs_lt_one ⟨m, h2.symm⟩ (fun i => by
      have := hxb i; have := hxb' i
      show |x' i - x i| < 1
      rw [abs_lt]; constructor <;> linarith)
    exact Subtype.ext (sub_eq_zero.1 h3).symm
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    let x0 : Pt 4 := (toReal W)⁻¹.mulVec (ofInt z)
    let k : Fin 4 → ℤ := fun i => ⌊x0 i⌋
    have hWx : (toReal W).mulVec (x0 - ofInt k) = ofInt (z - W.mulVec k) := by
      rw [Matrix.mulVec_sub, mulVec_inv_mulVec _ hA, toReal_mulVec_ofInt, ofInt_sub]
    refine ⟨⟨x0 - ofInt k, (mem_lat_inv _ hA _).2 (by rw [hWx]; exact ⟨_, rfl⟩), fun i => ?_⟩, ?_⟩
    · show 0 ≤ x0 i - (k i : ℝ) ∧ x0 i - (k i : ℝ) < 1
      exact ⟨Int.fract_nonneg (x0 i), Int.fract_lt_one (x0 i)⟩
    · show QuotientAddGroup.mk (fl ((toReal W).mulVec (x0 - ofInt k))) = QuotientAddGroup.mk z
      rw [hWx, hfl', QuotientAddGroup.eq, mem_rangeB]
      exact ⟨k, by abel⟩
  calc indexOver (lat (toReal W)⁻¹) = Nat.card T := (Nat.card_coe_set_eq T).symm
    _ = Nat.card ((Fin 4 → ℤ) ⧸ rangeB W) := Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩
    _ = W.det.natAbs := rangeB_index W hW

/-! ### The frame (l.307-316) -/

lemma frame_det_ne_zero (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    (colMat v).det ≠ 0 := by
  have h := (frame_D_pos P hP).2 v hv
  intro h0
  rw [h0, abs_zero] at h
  norm_num at h

lemma colMat_mulVec_unit (v : Fin 4 → Pt 4) (i : Fin 4) : (colMat v).mulVec (unitVec i) = v i := by
  rw [unitVec, Matrix.mulVec_single_one]
  rfl

lemma neg_mem_latPts {P : Set (Pt 4)} (hP : InW (Zn 4) P) {x : Pt 4} (hx : x ∈ P ∩ Zn 4) : -x ∈ P ∩ Zn 4 := by
  have h : x ∈ -(P ∩ Zn 4) := by rw [neg_inter_eq hP.2.1 (neg_Zn 4)]; exact hx
  exact h

/-- Case III, l.307: `x ↦ V⁻¹x` carries `ℤ⁴` onto `Λ = V⁻¹ℤ⁴ ⊇ ℤ⁴`, of index `D` over `ℤ⁴`. -/
theorem frame_lattice (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    Zn 4 ⊆ frameLat v ∧ (fun x => ((colMat v)⁻¹).mulVec x) '' Zn 4 = frameLat v ∧
      (indexOver (frameLat v) : ℝ) = |(colMat v).det| := by
  have hV := frame_det_ne_zero P hP v hv
  obtain ⟨W, hW⟩ := colMat_int v (fun i => (hv.1 i).2)
  refine ⟨fun y hy => ?_, (lat_eq_image _).symm, ?_⟩
  · rw [frameLat, mem_lat_inv _ hV, hW]
    exact toReal_mulVec_Zn W hy
  · have hW0 : W.det ≠ 0 := by rw [hW, det_toReal] at hV; exact_mod_cast hV
    rw [frameLat, hW, indexOver_eq W hW0, det_toReal, Nat.cast_natAbs, Int.cast_abs]

lemma updateCol_colMat (v : Fin 4 → Pt 4) (i : Fin 4) (x : Pt 4) :
    (colMat v).updateCol i x = colMat (Function.update v i x) := by
  ext a b
  by_cases h : b = i
  · subst h; simp [colMat]
  · simp [colMat, h]

/-- Cramer's rule: `(A⁻¹x)_i = det(A with column i replaced by x) / det A`. -/
lemma inv_mulVec_apply (A : Matrix (Fin 4) (Fin 4) ℝ) (x : Pt 4) (i : Fin 4) :
    (A⁻¹.mulVec x) i = (A.updateCol i x).det / A.det := by
  rw [Matrix.inv_def, Matrix.smul_mulVec, ← Matrix.cramer_eq_adjugate_mulVec, Pi.smul_apply,
    Matrix.cramer_apply, smul_eq_mul, Ring.inverse_eq_inv, div_eq_inv_mul]

/-- Lemma 5.1 (i), l.312: `S ⊂ Λ ∩ C_4`, `S = -S`, and `S` contains the unit vectors `±e_i`. -/
theorem lem_5_1_i (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    frameSet P v ⊆ frameLat v ∩ cube 4 ∧ -(frameSet P v) = frameSet P v ∧
      ∀ i, unitVec i ∈ frameSet P v ∧ -unitVec i ∈ frameSet P v := by
  have hV := frame_det_ne_zero P hP v hv
  refine ⟨?_, ?_, fun i => ⟨⟨v i, hv.1 i, ?_⟩, ⟨-v i, neg_mem_latPts hP (hv.1 i), ?_⟩⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, fun i => ?_⟩
    · obtain ⟨z, rfl⟩ := hx.2
      exact ⟨z, rfl⟩
    · show |((colMat v)⁻¹.mulVec x) i| ≤ 1
      rw [inv_mulVec_apply, updateCol_colMat, abs_div, div_le_one (abs_pos.2 hV)]
      refine hv.2 _ (fun k => ?_)
      rw [Function.update_apply]
      split_ifs
      · exact hx
      · exact hv.1 k
  · rw [frameSet, ← image_neg_mulVec, neg_inter_eq hP.2.1 (neg_Zn 4)]
  · show (colMat v)⁻¹.mulVec (v i) = unitVec i
    rw [← colMat_mulVec_unit v i, inv_mulVec_mulVec _ hV]
  · show (colMat v)⁻¹.mulVec (-v i) = -unitVec i
    rw [Matrix.mulVec_neg, ← colMat_mulVec_unit v i, inv_mulVec_mulVec _ hV]

lemma colMat_mulVec (A : Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → Pt 4) :
    colMat (fun i => A.mulVec (x i)) = A * colMat x := by
  ext a b
  simp [colMat, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- Lemma 5.1 (ii), l.313: `|det(s_1, …, s_4)| ≤ 1` for all `s_i ∈ S`. -/
theorem lem_5_1_ii (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v)
    (s : Fin 4 → Pt 4) (hs : ∀ i, s i ∈ frameSet P v) : |(colMat s).det| ≤ 1 := by
  have hV := frame_det_ne_zero P hP v hv
  simp only [frameSet, Set.mem_image] at hs
  choose x hx hxs using hs
  have hs' : s = fun i => (colMat v)⁻¹.mulVec (x i) := funext fun i => (hxs i).symm
  rw [hs', colMat_mulVec, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_mul, abs_inv,
    inv_mul_le_iff₀ (abs_pos.2 hV), mul_one]
  exact hv.2 x hx

/-- Lemma 5.1 (iii), l.314: `conv S ∩ Λ = S` and `int(conv S) ∩ Λ = {0}`. -/
theorem lem_5_1_iii (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    Saturated (frameLat v) (frameSet P v) ∧ interior (convexHull ℝ (frameSet P v)) ∩ frameLat v = {0} := by
  have hV := frame_det_ne_zero P hP v hv
  have hVi := det_inv_ne_zero _ hV
  have hconv : convexHull ℝ (frameSet P v) = (fun x => (colMat v)⁻¹.mulVec x) '' P := by
    rw [frameSet, ← image_convexHull_mulVec, ← conv_latPts hP.1]
  have hlat : frameLat v = (fun x => (colMat v)⁻¹.mulVec x) '' Zn 4 := lat_eq_image _
  constructor
  · show convexHull ℝ _ ∩ _ = _
    rw [hconv, hlat, ← Set.image_inter (mulVec_injective _ hVi)]
    rfl
  · rw [hconv, interior_image_mulVec _ hVi, hlat, ← Set.image_inter (mulVec_injective _ hVi), hP.2.2,
      Set.image_singleton]
    simp

/-- A convex set containing `0` and `±e_i` contains the closed `ℓ¹` unit ball. -/
lemma l1_ball_subset (S : Set (Pt 4)) (hS : Convex ℝ S) (h0 : (0 : Pt 4) ∈ S)
    (he : ∀ i, unitVec i ∈ S ∧ -unitVec i ∈ S) (c : Pt 4) (hc : ∑ i, |c i| ≤ 1) : c ∈ S := by
  let z : Option (Fin 4) → Pt 4 := fun o => o.elim 0 (fun i => if 0 ≤ c i then unitVec i else -unitVec i)
  let w : Option (Fin 4) → ℝ := fun o => o.elim (1 - ∑ i, |c i|) (fun i => |c i|)
  have hmem := hS.sum_mem (t := Finset.univ) (w := w) (z := z)
    (fun o _ => by cases o with
      | none => show 0 ≤ 1 - ∑ i, |c i|; linarith
      | some i => exact abs_nonneg (c i))
    (by rw [Fintype.sum_option]; show 1 - ∑ i, |c i| + ∑ i, |c i| = 1; ring)
    (fun o _ => by cases o with
      | none => exact h0
      | some i =>
        show (if 0 ≤ c i then unitVec i else -unitVec i) ∈ S
        split_ifs
        · exact (he i).1
        · exact (he i).2)
  have hsum : ∑ o, w o • z o = c := by
    rw [Fintype.sum_option]
    show (1 - ∑ i, |c i|) • (0 : Pt 4) + ∑ i, |c i| • (if 0 ≤ c i then unitVec i else -unitVec i) = c
    rw [smul_zero, zero_add]
    conv_rhs => rw [pi_eq_sum_univ' c]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [abs_of_nonneg h, unitVec]
    · rw [abs_of_neg (not_le.1 h), neg_smul_neg, unitVec]
  rw [hsum] at hmem
  exact hmem

/-- Lemma 5.1 (iv), l.315: `Λ` contains no point `c ≠ 0` with `|c_1| + ⋯ + |c_4| < 1`. -/
theorem lem_5_1_iv (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    NoShortL1 (frameLat v) := by
  intro c hc hc0
  by_contra hlt
  push Not at hlt
  obtain ⟨-, -, he⟩ := lem_5_1_i P hP v hv
  have hS0 : (0 : Pt 4) ∈ frameSet P v := ⟨0, zero_mem_latPts hP, by simp⟩
  have hopen : IsOpen {c : Pt 4 | ∑ i, |c i| < 1} :=
    isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).abs) continuous_const
  have hsub : {c : Pt 4 | ∑ i, |c i| < 1} ⊆ convexHull ℝ (frameSet P v) := fun c' hc' =>
    l1_ball_subset _ (convex_convexHull ℝ _) (subset_convexHull ℝ _ hS0)
      (fun i => ⟨subset_convexHull ℝ _ (he i).1, subset_convexHull ℝ _ (he i).2⟩) c' (le_of_lt hc')
  have hint : c ∈ interior (convexHull ℝ (frameSet P v)) ∩ frameLat v :=
    ⟨interior_maximal hsub hopen hlt, hc⟩
  rw [(lem_5_1_iii P hP v hv).2] at hint
  exact hc0 hint

/-! ### Integer functionals in the frame coordinates (l.326) -/

lemma dot_transpose (V : Matrix (Fin 4) (Fin 4) ℝ) (u y : Pt 4) :
    (V.transpose.mulVec u) ⬝ᵥ y = u ⬝ᵥ V.mulVec y := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

lemma convex_slab (u : Pt 4) : Convex ℝ {x : Pt 4 | |u ⬝ᵥ x| ≤ 1} := by
  intro x hx y hy a b ha hb hab
  show |u ⬝ᵥ (a • x + b • y)| ≤ 1
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  calc |a * (u ⬝ᵥ x) + b * (u ⬝ᵥ y)| ≤ |a * (u ⬝ᵥ x)| + |b * (u ⬝ᵥ y)| := abs_add' _ _
    _ = a * |u ⬝ᵥ x| + b * |u ⬝ᵥ y| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by rw [mul_one, mul_one, hab]

lemma frame_M_iff (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) (u : Pt 4) :
    u ∈ MP P ↔ (colMat v).transpose.mulVec u ∈ MS (frameLat v) (frameSet P v) := by
  have hV := frame_det_ne_zero P hP v hv
  have key : ∀ u x, ((colMat v).transpose.mulVec u) ⬝ᵥ ((colMat v)⁻¹.mulVec x) = u ⬝ᵥ x := fun u x => by
    rw [dot_transpose, mulVec_inv_mulVec _ hV]
  constructor
  · rintro ⟨hu, hb⟩
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨z, rfl⟩ := hy
      obtain ⟨m, hm⟩ := dot_Zn hu ⟨z, rfl⟩
      exact ⟨m, (key u (ofInt z)).trans hm⟩
    · rintro _ ⟨x, hx, rfl⟩
      show |((colMat v).transpose.mulVec u) ⬝ᵥ ((colMat v)⁻¹.mulVec x)| ≤ 1
      rw [key]
      exact hb x hx.1
  · rintro ⟨hdual, hb⟩
    have hb' : ∀ x ∈ P ∩ Zn 4, |u ⬝ᵥ x| ≤ 1 := fun x hx => by
      have h := hb ((colMat v)⁻¹.mulVec x) ⟨x, hx, rfl⟩
      rwa [key] at h
    refine ⟨?_, fun x hx => ?_⟩
    · have hint : ∀ i, ∃ m : ℤ, u i = m := fun i => by
        obtain ⟨m, hm⟩ := hdual ((colMat v)⁻¹.mulVec (unitVec i))
          ⟨Pi.single i 1, by show (colMat v)⁻¹.mulVec (ofInt (Pi.single i 1)) = _; rw [ofInt_single]⟩
        refine ⟨m, ?_⟩
        rw [key, unitVec, dotProduct_single, mul_one] at hm
        exact hm
      choose m hm using hint
      exact ⟨m, funext fun i => (hm i).symm⟩
    · have hsub : convexHull ℝ (P ∩ Zn 4) ⊆ {x : Pt 4 | |u ⬝ᵥ x| ≤ 1} :=
        convexHull_min (fun y hy => hb' y hy) (convex_slab u)
      rw [← conv_latPts hP.1] at hsub
      exact hsub hx

/-- l.326: `u ∈ M(P)` iff `Vᵀu ∈ M(S)`, so `r(P) = r(S)`. -/
theorem frame_M_transfer (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    (∀ u, u ∈ MP P ↔ (Matrix.transpose (colMat v)).mulVec u ∈ MS (frameLat v) (frameSet P v)) ∧
      rP P = rS (frameLat v) (frameSet P v) := by
  have hV := frame_det_ne_zero P hP v hv
  have hVt : (Matrix.transpose (colMat v)).det ≠ 0 := by rw [Matrix.det_transpose]; exact hV
  have hiff := frame_M_iff P hP v hv
  refine ⟨hiff, ?_⟩
  have himage : MS (frameLat v) (frameSet P v) = (fun u => (colMat v).transpose.mulVec u) '' MP P := by
    ext w
    constructor
    · intro hw
      refine ⟨((colMat v).transpose)⁻¹.mulVec w, ?_, mulVec_inv_mulVec _ hVt w⟩
      rw [hiff, mulVec_inv_mulVec _ hVt]
      exact hw
    · rintro ⟨u, hu, rfl⟩
      exact (hiff u).1 hu
  have hspan : Submodule.span ℝ ((fun u => (colMat v).transpose.mulVec u) '' MP P) =
      Submodule.map (Matrix.mulVecLin (colMat v).transpose) (Submodule.span ℝ (MP P)) :=
    (Submodule.map_span (Matrix.mulVecLin (colMat v).transpose) (MP P)).symm
  have hinj : Function.Injective (Matrix.mulVecLin (colMat v).transpose) := mulVec_injective _ hVt
  unfold rP rS
  rw [himage, hspan]
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq

/-! ### Volumes: the cross-polytope (l.323) -/

lemma l1_ball_convex : Convex ℝ {c : Pt 4 | ∑ i, |c i| ≤ 1} := by
  intro x hx y hy a b ha hb hab
  show ∑ i, |(a • x + b • y) i| ≤ 1
  calc ∑ i, |(a • x + b • y) i| ≤ ∑ i, (a * |x i| + b * |y i|) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        calc |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add' _ _
          _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a * ∑ i, |x i| + b * ∑ i, |y i| := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by rw [mul_one, mul_one, hab]

lemma l1_unit_norm (i : Fin 4) : ∑ k, |unitVec i k| = 1 := by
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [unitVec, hk]) (by simp)]
  simp [unitVec]

/-- `conv{±e_i}` is the closed `ℓ¹` unit ball. -/
lemma l1_closed_eq :
    convexHull ℝ (Set.range unitVec ∪ Set.range (fun i => -unitVec i)) = {c : Pt 4 | ∑ i, |c i| ≤ 1} := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ l1_ball_convex
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact (l1_unit_norm i).le
    · show ∑ k, |(-unitVec i) k| ≤ 1
      simp only [Pi.neg_apply, abs_neg]
      exact (l1_unit_norm i).le
  · intro c hc
    have he : ∀ i, unitVec i ∈ convexHull ℝ (Set.range unitVec ∪ Set.range (fun i => -unitVec i)) ∧
        -unitVec i ∈ convexHull ℝ (Set.range unitVec ∪ Set.range (fun i => -unitVec i)) := fun i =>
      ⟨subset_convexHull ℝ _ (Or.inl ⟨i, rfl⟩), subset_convexHull ℝ _ (Or.inr ⟨i, rfl⟩)⟩
    have h0 : (0 : Pt 4) ∈ convexHull ℝ (Set.range unitVec ∪ Set.range (fun i => -unitVec i)) := by
      have := convex_convexHull ℝ _ (he 0).1 (he 0).2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa using this
    exact l1_ball_subset _ (convex_convexHull ℝ _) h0 he c hc

lemma l1_ball_volume : volume {c : Pt 4 | ∑ i, |c i| ≤ 1} = ENNReal.ofReal (2 ^ 4 / 24) := by
  have h := MeasureTheory.volume_sum_rpow_le (ι := Fin 4) (p := 1) le_rfl 1
  have hset : {x : Pt 4 | (∑ i, |x i| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) ≤ 1} = {c : Pt 4 | ∑ i, |c i| ≤ 1} := by
    ext x; simp [Real.rpow_one]
  rw [hset] at h
  rw [h]
  have hg2 : Real.Gamma (1 / 1 + 1) = 1 := by norm_num [Real.Gamma_two]
  have hg5 : Real.Gamma ((Fintype.card (Fin 4) : ℝ) / 1 + 1) = 24 := by
    have := Real.Gamma_nat_eq_factorial 4
    rw [Fintype.card_fin]
    norm_num [Nat.factorial] at this ⊢
  rw [hg2, hg5, ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin]
  norm_num

/-- Lemma 5.1 (v) proof, l.323: the cross-polytope `conv{±v_i}` has volume `(2⁴/4!) D`. -/
theorem crosspoly_vol (v : Fin 4 → Pt 4) :
    volume (convexHull ℝ (Set.range v ∪ Set.range (fun i => -v i))) =
      ENNReal.ofReal ((2 : ℝ) ^ 4 / 24 * |(colMat v).det|) := by
  have himg : Set.range v ∪ Set.range (fun i => -v i) =
      (fun x => (colMat v).mulVec x) '' (Set.range unitVec ∪ Set.range (fun i => -unitVec i)) := by
    ext y
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨unitVec i, Or.inl ⟨i, rfl⟩, colMat_mulVec_unit v i⟩
      · exact ⟨-unitVec i, Or.inr ⟨i, rfl⟩, by simp only [Matrix.mulVec_neg, colMat_mulVec_unit]⟩
    · rintro ⟨_, (⟨i, rfl⟩ | ⟨i, rfl⟩), rfl⟩
      · exact Or.inl ⟨i, (colMat_mulVec_unit v i).symm⟩
      · exact Or.inr ⟨i, by simp only [Matrix.mulVec_neg, colMat_mulVec_unit]⟩
  have h1 := MeasureTheory.Measure.addHaar_image_linearMap volume (Matrix.toLin' (colMat v))
    {c : Pt 4 | ∑ i, |c i| ≤ 1}
  rw [LinearMap.det_toLin'] at h1
  have h3 : (fun x => (colMat v).mulVec x) '' {c : Pt 4 | ∑ i, |c i| ≤ 1} =
      ⇑(Matrix.toLin' (colMat v)) '' {c : Pt 4 | ∑ i, |c i| ≤ 1} := by
    ext y; simp [Matrix.toLin'_apply]
  rw [himg, ← image_convexHull_mulVec, l1_closed_eq, h3, h1, l1_ball_volume, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

/-- Lemma 5.1 (v) proof, l.323: `D ≤ 24`; if `D = 24` then `P = conv{±v_i}` and `vol P = 16`. -/
theorem frame_D_le_24 (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    |(colMat v).det| ≤ 24 ∧ (|(colMat v).det| = 24 →
      P = convexHull ℝ (Set.range v ∪ Set.range (fun i => -v i)) ∧ volume P = 16) := by
  obtain ⟨hcpt, hconvP⟩ := Sec2.latticePolytope_compact_convex hP.1
  have hKP : convexHull ℝ (Set.range v ∪ Set.range (fun i => -v i)) ⊆ P :=
    convexHull_min (Set.union_subset (Set.range_subset_iff.2 fun i => (hv.1 i).1)
      (Set.range_subset_iff.2 fun i => (neg_mem_latPts hP (hv.1 i)).1)) hconvP
  have hvolP : volume P ≤ 16 := by
    have h := Sec2.minkowski_first 4 P hconvP hcpt (fun x hx => by rw [← hP.2.1]; simpa using hx)
      (by rw [hP.2.2])
    norm_num at h
    exact h
  have hvolK := crosspoly_vol v
  have hle : ENNReal.ofReal ((2 : ℝ) ^ 4 / 24 * |(colMat v).det|) ≤ 16 := by
    rw [← hvolK]; exact (measure_mono hKP).trans hvolP
  rw [ENNReal.ofReal_le_iff_le_toReal (by norm_num)] at hle
  norm_num at hle
  refine ⟨by linarith, fun hD => ?_⟩
  have hK16 : volume (convexHull ℝ (Set.range v ∪ Set.range (fun i => -v i))) = 16 := by
    rw [hvolK, hD]; norm_num
  have hPK : P ⊆ convexHull ℝ (Set.range v ∪ Set.range (fun i => -v i)) := by
    intro x hxP
    by_contra hxK
    set K := convexHull ℝ (Set.range v ∪ Set.range (fun i => -v i)) with hKdef
    have hKc : IsClosed K :=
      (((Set.finite_range v).union (Set.finite_range fun i => -v i)).isCompact_convexHull ℝ).isClosed
    have h0 : (0 : Pt 4) ∈ interior P := (Sec2.inW_full_dim 4 _ P hP).1
    have hcl : closure (interior P) = closure P :=
      hconvP.closure_interior_eq_closure_of_nonempty_interior ⟨0, h0⟩
    have hxcl : x ∈ closure (interior P) := by rw [hcl]; exact subset_closure hxP
    obtain ⟨z, hzK, hzP⟩ := mem_closure_iff.1 hxcl Kᶜ hKc.isOpen_compl hxK
    have hUopen : IsOpen (interior P ∩ Kᶜ) := isOpen_interior.inter hKc.isOpen_compl
    have hUpos : 0 < volume (interior P ∩ Kᶜ) := hUopen.measure_pos volume ⟨z, hzP, hzK⟩
    have hunion : volume K + volume (interior P ∩ Kᶜ) ≤ volume P := by
      rw [← measure_union (Set.disjoint_left.2 fun a ha hb => hb.2 ha) hUopen.measurableSet]
      exact measure_mono (Set.union_subset hKP (Set.inter_subset_left.trans interior_subset))
    rw [hK16] at hunion
    have h2 : (16 : ENNReal) + volume (interior P ∩ Kᶜ) ≤ 16 + 0 := by
      rw [add_zero]; exact hunion.trans hvolP
    have h3 := (ENNReal.add_le_add_iff_left (by norm_num)).1 h2
    exact absurd hUpos (not_lt.2 h3)
  have hPeq : P = convexHull ℝ (Set.range v ∪ Set.range (fun i => -v i)) := Set.Subset.antisymm hPK hKP
  refine ⟨hPeq, ?_⟩
  rw [hPeq, hK16]

/-! ### Signed permutations (l.326) -/

/-- The sign `±1` of coordinate `i` under `σ` (`true` = minus). -/
def sgn (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (i : Fin 4) : ℤ := if σ.2 i then -1 else 1

lemma sgn_mul_self (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (i : Fin 4) : sgn σ i * sgn σ i = 1 := by
  unfold sgn; split_ifs <;> norm_num

lemma signedPerm_apply' (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (x : Pt 4) (i : Fin 4) :
    signedPerm σ x i = (sgn σ i : ℝ) * x (σ.1 i) := by
  unfold signedPerm sgn; split_ifs <;> simp

/-- The integer matrix of a signed permutation. -/
def spMat (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => if j = σ.1 i then sgn σ i else 0

lemma signedPerm_eq (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (x : Pt 4) :
    signedPerm σ x = (toReal (spMat σ)).mulVec x := by
  funext i
  rw [signedPerm_apply']
  simp [spMat, toReal, Matrix.mulVec, dotProduct, ite_mul]

/-- The inverse signed permutation. -/
def spInv (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : Equiv.Perm (Fin 4) × (Fin 4 → Bool) :=
  (σ.1.symm, fun j => σ.2 (σ.1.symm j))

lemma signedPerm_inv_left (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (x : Pt 4) :
    signedPerm (spInv σ) (signedPerm σ x) = x := by
  funext j
  rw [signedPerm_apply', signedPerm_apply']
  have h : sgn (spInv σ) j = sgn σ (σ.1.symm j) := rfl
  have h2 : (spInv σ).1 j = σ.1.symm j := rfl
  rw [h, h2, Equiv.apply_symm_apply, ← mul_assoc, ← Int.cast_mul, sgn_mul_self, Int.cast_one, one_mul]

lemma signedPerm_inv_right (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (y : Pt 4) :
    signedPerm σ (signedPerm (spInv σ) y) = y := by
  funext i
  rw [signedPerm_apply', signedPerm_apply']
  have h : sgn (spInv σ) (σ.1 i) = sgn σ i := by
    show sgn σ (σ.1.symm (σ.1 i)) = sgn σ i
    rw [Equiv.symm_apply_apply]
  have h2 : (spInv σ).1 (σ.1 i) = i := Equiv.symm_apply_apply σ.1 i
  rw [h, h2, ← mul_assoc, ← Int.cast_mul, sgn_mul_self, Int.cast_one, one_mul]

lemma signedPerm_injective (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : Function.Injective (signedPerm σ) :=
  fun x y h => by rw [← signedPerm_inv_left σ x, h, signedPerm_inv_left]

lemma toReal_mul (A B : Matrix (Fin 4) (Fin 4) ℤ) : toReal (A * B) = toReal A * toReal B := by
  ext i j
  simp [toReal, Matrix.mul_apply]

lemma spMat_inv_mul (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) :
    toReal (spMat (spInv σ)) * toReal (spMat σ) = 1 := by
  ext i j
  have h := congrFun (signedPerm_inv_left σ (Pi.single j 1)) i
  rw [signedPerm_eq, signedPerm_eq, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
  have h' : (toReal (spMat (spInv σ)) * toReal (spMat σ)) i j = (Pi.single j (1 : ℝ) : Pt 4) i := h
  rw [h', Pi.single_apply, Matrix.one_apply]

lemma spMat_det (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : |(spMat σ).det| = 1 := by
  have h := congrArg Matrix.det (spMat_inv_mul σ)
  rw [Matrix.det_mul, Matrix.det_one, det_toReal, det_toReal] at h
  have h' : (spMat (spInv σ)).det * (spMat σ).det = 1 := by exact_mod_cast h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h' with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2] <;> norm_num

lemma l1_signedPerm (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (c : Pt 4) :
    ∑ i, |signedPerm σ c i| = ∑ i, |c i| := by
  have h : ∀ i, |signedPerm σ c i| = |c (σ.1 i)| := fun i => by
    rw [signedPerm_apply', abs_mul]; unfold sgn; split_ifs <;> simp
  simp_rw [h]
  exact Equiv.sum_comp σ.1 (fun i => |c i|)

lemma mem_image_signedPerm (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (Λ : Set (Pt 4)) (y : Pt 4) :
    y ∈ signedPerm σ '' Λ ↔ signedPerm (spInv σ) y ∈ Λ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [signedPerm_inv_left]
  · intro h
    exact ⟨_, h, signedPerm_inv_right σ y⟩

/-- l.326: the signed permutations act on the frame lattices. -/
theorem signedPerm_frameLat (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (Λ : Set (Pt 4))
    (hΛ : IsFrameLattice Λ) : IsFrameLattice (signedPerm σ '' Λ) := by
  obtain ⟨V, hV0, hV23, rfl, hshort⟩ := hΛ
  have hdet : |(V * spMat (spInv σ)).det| = |V.det| := by
    rw [Matrix.det_mul, abs_mul, spMat_det, mul_one]
  have hA : (toReal V).det ≠ 0 := toReal_det_ne_zero hV0
  have hV'0 : (V * spMat (spInv σ)).det ≠ 0 := by
    intro h; rw [h, abs_zero] at hdet; exact hV0 (abs_eq_zero.1 hdet.symm)
  have hA' : (toReal (V * spMat (spInv σ))).det ≠ 0 := toReal_det_ne_zero hV'0
  refine ⟨V * spMat (spInv σ), hV'0, by rw [hdet]; exact hV23, ?_, ?_⟩
  · ext y
    rw [mem_image_signedPerm, mem_lat_inv _ hA, mem_lat_inv _ hA', toReal_mul, ← Matrix.mulVec_mulVec,
      ← signedPerm_eq]
  · rintro _ ⟨c, hc, rfl⟩ hc0
    rw [l1_signedPerm]
    exact hshort c hc (fun h => hc0 (by rw [h]; funext i; simp [signedPerm]))

/-! ### Finiteness of the frame lattices (l.326) -/

lemma adj_toReal (V : Matrix (Fin 4) (Fin 4) ℤ) : (toReal V).adjugate = toReal V.adjugate := by
  have := RingHom.map_adjugate (Int.castRingHom ℝ) V
  simpa [toReal] using this.symm

/-- `x ∈ W⁻¹ ℤ⁴` has `(det W) x ∈ ℤ⁴`. -/
lemma det_smul_mem_Zn (V : Matrix (Fin 4) (Fin 4) ℤ) (hV : V.det ≠ 0) {x : Pt 4} (hx : x ∈ lat (toReal V)⁻¹) :
    (V.det : ℝ) • x ∈ Zn 4 := by
  obtain ⟨z, rfl⟩ := hx
  have hA : (toReal V).det ≠ 0 := toReal_det_ne_zero hV
  refine ⟨V.adjugate.mulVec z, ?_⟩
  show ofInt (V.adjugate.mulVec z) = (V.det : ℝ) • (toReal V)⁻¹.mulVec (ofInt z)
  rw [← toReal_mulVec_ofInt, ← adj_toReal, Matrix.inv_def, Matrix.smul_mulVec, smul_smul, Ring.inverse_eq_inv,
    ← det_toReal, mul_inv_cancel₀ hA, one_smul]

lemma Zn_add_mem {x y : Pt 4} (hx : x ∈ Zn 4) (hy : y ∈ Zn 4) : x + y ∈ Zn 4 := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, ofInt_add a b⟩

lemma Zn_sub_mem {x y : Pt 4} (hx : x ∈ Zn 4) (hy : y ∈ Zn 4) : x - y ∈ Zn 4 := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a - b, ofInt_sub a b⟩

/-- The half-open unit cube `[0,1)⁴`. -/
def unitBox : Set (Pt 4) := {x | ∀ i, 0 ≤ x i ∧ x i < 1}

/-- The lattice generated by `T` and `ℤ⁴`, as `{x : x - y ∈ ℤ⁴ for some y ∈ T}`. -/
def addZn (T : Set (Pt 4)) : Set (Pt 4) := {x | ∃ y ∈ T, x - y ∈ Zn 4}

/-- A lattice `W⁻¹ ℤ⁴ ⊇ ℤ⁴` is determined by its points in `[0,1)⁴`. -/
lemma lat_eq_addZn (V : Matrix (Fin 4) (Fin 4) ℤ) (hV : V.det ≠ 0) :
    lat (toReal V)⁻¹ = addZn (lat (toReal V)⁻¹ ∩ unitBox) := by
  have hA : (toReal V).det ≠ 0 := toReal_det_ne_zero hV
  ext x
  constructor
  · intro hx
    let k : Fin 4 → ℤ := fun i => ⌊x i⌋
    have hk : ofInt k ∈ lat (toReal V)⁻¹ := (mem_lat_inv _ hA _).2 (toReal_mulVec_Zn V ⟨k, rfl⟩)
    refine ⟨x - ofInt k, ⟨?_, fun i => ⟨Int.fract_nonneg (x i), Int.fract_lt_one (x i)⟩⟩, ?_⟩
    · rw [mem_lat_inv _ hA, Matrix.mulVec_sub]
      exact Zn_sub_mem ((mem_lat_inv _ hA _).1 hx) ((mem_lat_inv _ hA _).1 hk)
    · rw [sub_sub_cancel]; exact ⟨k, rfl⟩
  · rintro ⟨y, ⟨hy, -⟩, hxy⟩
    have hxy' : x - y ∈ lat (toReal V)⁻¹ := (mem_lat_inv _ hA _).2 (toReal_mulVec_Zn V hxy)
    rw [mem_lat_inv _ hA] at hy hxy' ⊢
    have := Zn_add_mem hxy' hy
    rwa [← Matrix.mulVec_add, sub_add_cancel] at this

lemma smulZn_cube_finite (D : ℕ) : (((1 / ((D : ℝ) + 1)) • Zn 4) ∩ cube 4).Finite := by
  have hD : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  refine ((Sec2.Zn_inter_finite (Metric.isBounded_closedBall (x := (0 : Pt 4)) (r := (D : ℝ) + 1))).image
    (fun y => (1 / ((D : ℝ) + 1)) • y)).subset ?_
  rintro x ⟨⟨y, hy, rfl⟩, hx⟩
  refine ⟨y, ⟨?_, hy⟩, rfl⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hD.le]
  intro i
  have h := hx i
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((D : ℝ) + 1))] at h
  rw [Real.norm_eq_abs]
  rw [one_div, inv_mul_le_iff₀ hD, mul_one] at h
  exact h

/-- l.326: a lattice of index `D` over `ℤ⁴` lies in `(1/D)ℤ⁴`, so the set of frame lattices is finite. -/
theorem frameLat_finite :
    (∀ V : Matrix (Fin 4) (Fin 4) ℤ, V.det ≠ 0 →
        lat (toReal V)⁻¹ ⊆ (1 / (|V.det| : ℝ)) • Zn 4) ∧ {Λ | IsFrameLattice Λ}.Finite := by
  have hsub : ∀ V : Matrix (Fin 4) (Fin 4) ℤ, V.det ≠ 0 → lat (toReal V)⁻¹ ⊆ (1 / (|V.det| : ℝ)) • Zn 4 := by
    intro V hV x hx
    have hd : (0 : ℝ) < |(V.det : ℝ)| := abs_pos.2 (by exact_mod_cast hV)
    have h1 : |(V.det : ℝ)| • x ∈ Zn 4 := by
      rcases abs_choice (V.det : ℝ) with h | h
      · rw [h]; exact det_smul_mem_Zn V hV hx
      · rw [h, neg_smul, ← neg_Zn, Set.mem_neg, neg_neg]
        exact det_smul_mem_Zn V hV hx
    have h2 : x = (1 / |(V.det : ℝ)|) • (|(V.det : ℝ)| • x) := by
      rw [smul_smul, one_div, inv_mul_cancel₀ hd.ne', one_smul]
    rw [h2]
    exact Set.smul_mem_smul_set h1
  refine ⟨hsub, ?_⟩
  let F : Set (Pt 4) := ⋃ D : Fin 23, (((1 / ((D : ℕ) + 1 : ℝ)) • Zn 4) ∩ cube 4)
  have hF : F.Finite := Set.finite_iUnion fun D => by
    have := smulZn_cube_finite (D : ℕ)
    simpa using this
  refine ((hF.finite_subsets).image addZn).subset ?_
  rintro Λ ⟨V, hV0, hV23, rfl, -⟩
  refine ⟨lat (toReal V)⁻¹ ∩ unitBox, ?_, (lat_eq_addZn V hV0).symm⟩
  rintro x ⟨hx, hxb⟩
  have h1 : (1 : ℤ) ≤ |V.det| := Int.one_le_abs hV0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (|V.det| : ℤ) = n + 1 := ⟨(|V.det| - 1).toNat, by omega⟩
  have hn23 : n < 23 := by omega
  refine Set.mem_iUnion.2 ⟨⟨n, hn23⟩, ?_, fun i => ?_⟩
  · have := hsub V hV0 hx
    have hcast : |(V.det : ℝ)| = ((n : ℕ) + 1 : ℝ) := by rw [← Int.cast_abs, hn]; push_cast; ring
    rw [hcast] at this
    exact this
  · have := hxb i
    rw [abs_le]; constructor <;> linarith [this.1, this.2]

/-! ### The tiling step of Lemma 5.1 (v) (l.323) -/

lemma interior_vadd' (z : Pt 4) (K : Set (Pt 4)) : interior (z +ᵥ K) = z +ᵥ interior K :=
  ((Homeomorph.addLeft z).image_interior K).symm

/-- The translates of `½ int P` by distinct lattice points are disjoint (an overlap would put a nonzero lattice
point in `int P`). -/
lemma half_disjoint (P : Set (Pt 4)) (hP : InW (Zn 4) P) {z z' : Pt 4} (hz : z ∈ Zn 4) (hz' : z' ∈ Zn 4)
    (hzz : z ≠ z') : Disjoint (interior (z +ᵥ (1 / 2 : ℝ) • P)) (interior (z' +ᵥ (1 / 2 : ℝ) • P)) := by
  obtain ⟨-, hconvP⟩ := Sec2.latticePolytope_compact_convex hP.1
  have hsymm : ∀ x ∈ P, -x ∈ P := fun x hx => by rw [← hP.2.1]; simpa using hx
  rw [Set.disjoint_left]
  intro y hy hy'
  rw [interior_vadd', interior_smul₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hy hy'
  obtain ⟨_, ⟨p, hp, rfl⟩, rfl⟩ := hy
  obtain ⟨_, ⟨p', hp', rfl⟩, hyy⟩ := hy'
  -- z - z' = ½ p' - ½ p ∈ int P
  have hdiff : z - z' = (1 / 2 : ℝ) • p' + (1 / 2 : ℝ) • (-p) := by
    have hyy' : z' + (1 / 2 : ℝ) • p' = z + (1 / 2 : ℝ) • p := hyy
    have h3 : z = z' + (1 / 2 : ℝ) • p' - (1 / 2 : ℝ) • p := eq_sub_of_add_eq hyy'.symm
    rw [h3, smul_neg]
    abel
  have hmem : z - z' ∈ interior P := by
    rw [hdiff]
    exact hconvP.interior hp' (Sec2.neg_mem_interior hsymm hp) (by norm_num) (by norm_num) (by norm_num)
  have h0 : z - z' ∈ interior P ∩ Zn 4 := ⟨hmem, Zn_sub_mem hz hz'⟩
  rw [hP.2.2] at h0
  exact hzz (sub_eq_zero.1 h0)

/-- Lemma 5.1 (v) proof, l.323: if `P ∈ W⁴` has volume 16, the translates `½P + z`, `z ∈ ℤ⁴`, tile `ℝ⁴` (disjoint
interiors and total density 1). -/
theorem half_translates_tile (P : Set (Pt 4)) (hP : InW (Zn 4) P) (hvol : volume P = 16) :
    TilesByZ4 ((1 / 2 : ℝ) • P) := by
  obtain ⟨hcpt, hconvP⟩ := Sec2.latticePolytope_compact_convex hP.1
  set K := (1 / 2 : ℝ) • P with hKdef
  refine ⟨?_, fun z hz z' hz' hzz => half_disjoint P hP hz hz' hzz⟩
  have hKc : IsCompact K := hcpt.smul (1 / 2 : ℝ)
  have hKconv : Convex ℝ K := hconvP.smul (1 / 2 : ℝ)
  have hvolK : volume K = 1 := by
    rw [hKdef, MeasureTheory.Measure.addHaar_smul, hvol, Module.finrank_fin_fun,
      show (16 : ENNReal) = ENNReal.ofReal 16 by norm_num, ← ENNReal.ofReal_mul (by positivity)]
    norm_num
  have hvolI : volume (interior K) = 1 := by
    apply le_antisymm
    · rw [← hvolK]; exact measure_mono interior_subset
    · rw [← hvolK]; exact Sec2.volume_le_interior hKconv
  -- suppose a point `y` is not covered
  rw [Set.eq_univ_iff_forall]
  intro y
  by_contra hy
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall 0
  have hR0 : 0 ≤ R := by
    have h0K : (0 : Pt 4) ∈ K := ⟨0, (zero_mem_latPts hP).1, by simp⟩
    have := hR h0K
    rw [mem_closedBall_zero_iff, norm_zero] at this
    exact this
  -- the finitely many translates that come near `y`
  set Z' := Metric.closedBall y (R + 1) ∩ Zn 4 with hZ'
  have hZ'fin : Z'.Finite := Sec2.Zn_inter_finite Metric.isBounded_closedBall
  have hU'closed : IsClosed (⋃ z ∈ Z', z +ᵥ K) :=
    hZ'fin.isClosed_biUnion fun z _ => (hKc.vadd z).isClosed
  have hyU' : y ∉ ⋃ z ∈ Z', z +ᵥ K := fun h => hy (by
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 h
    exact Set.mem_iUnion₂.2 ⟨z, hz.2, hyz⟩)
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.1 hU'closed.isOpen_compl y hyU'
  set ε := min ε₁ (1 / 2) with hεdef
  have hε : 0 < ε := lt_min hε₁ (by norm_num)
  -- the ball `B(y, ε)` meets no translate `z + K`
  have hmiss : ∀ z ∈ Zn 4, ∀ w ∈ Metric.ball y ε, w ∉ z +ᵥ K := by
    intro z hz w hw hwz
    by_cases hnear : z ∈ Metric.closedBall y (R + 1)
    · have : w ∈ Metric.ball y ε₁ := Metric.ball_subset_ball (min_le_left _ _) hw
      exact hball₁ this (Set.mem_iUnion₂.2 ⟨z, ⟨hnear, hz⟩, hwz⟩)
    · obtain ⟨k, hk, rfl⟩ := hwz
      have hk' : ‖k‖ ≤ R := mem_closedBall_zero_iff.1 (hR hk)
      have hwy : dist (z +ᵥ k) y < 1 := lt_of_lt_of_le (Metric.mem_ball.1 hw) ((min_le_right _ _).trans (by norm_num))
      apply hnear
      rw [Metric.mem_closedBall]
      have h1 : dist z y ≤ dist (z +ᵥ k) y + ‖k‖ := by
        rw [vadd_eq_add, dist_eq_norm, dist_eq_norm]
        calc ‖z - y‖ = ‖(z + k - y) - k‖ := by congr 1; abel
          _ ≤ ‖z + k - y‖ + ‖k‖ := norm_sub_le _ _
      linarith
  -- the set `int K ∪ B(y, ε)` has volume `> 1`
  set b := Pi.basisFun ℝ (Fin 4)
  have h_fund : IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)).toAddSubgroup
      (ZSpan.fundamentalDomain b) volume := ZSpan.isAddFundamentalDomain b volume
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range b))
    infer_instance
  have hF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi_pi]; simp
  have h0Zn : (0 : Pt 4) ∈ Zn 4 := Sec2.zero_mem_Zn 4
  have hdisj : Disjoint (interior K) (Metric.ball y ε) := by
    rw [Set.disjoint_left]
    intro w hwK hwB
    exact hmiss 0 h0Zn w hwB (by rw [zero_vadd]; exact interior_subset hwK)
  have hvolT : volume (ZSpan.fundamentalDomain b) < volume (interior K ∪ Metric.ball y ε) := by
    rw [measure_union hdisj Metric.isOpen_ball.measurableSet, hvolI, hF]
    exact ENNReal.lt_add_right ENNReal.one_ne_top (Metric.measure_ball_pos volume y hε).ne'
  obtain ⟨x, hx, x', hx', ⟨g, hg⟩, hg0, hgx⟩ :=
    h_fund.exists_ne_zero_vadd_eq (isOpen_interior.union Metric.isOpen_ball).nullMeasurableSet hvolT
  -- `g` is a nonzero lattice point with `g + x = x'`
  rw [Submodule.mem_toAddSubgroup] at hg
  have hrep := (b.mem_span_iff_repr_mem ℤ g).mp hg
  choose zg hzg using hrep
  have hgZ : g ∈ Zn 4 := ⟨zg, by funext i; simpa [ofInt, b] using hzg i⟩
  have hg0' : g ≠ 0 := fun h => hg0 (Subtype.ext h)
  have hgx' : g + x = x' := hgx
  rcases hx with hxK | hxB <;> rcases hx' with hx'K | hx'B
  · -- both in `int K`: two translates of `int K` overlap
    have h1 : x' ∈ interior (g +ᵥ K) := by
      rw [interior_vadd', ← hgx']; exact ⟨x, hxK, rfl⟩
    have h2 : x' ∈ interior ((0 : Pt 4) +ᵥ K) := by rw [zero_vadd]; exact hx'K
    exact Set.disjoint_left.1 (half_disjoint P hP hgZ h0Zn hg0') h1 h2
  · -- `x' ∈ B(y, ε)` lies in `g + K`
    exact hmiss g hgZ x' hx'B (by rw [← hgx']; exact ⟨x, interior_subset hxK, rfl⟩)
  · -- `x ∈ B(y, ε)` lies in `-g + K`
    have hng : -g ∈ Zn 4 := by rw [← neg_Zn]; rw [Set.mem_neg, neg_neg]; exact hgZ
    refine hmiss (-g) hng x hxB ⟨x', interior_subset hx'K, ?_⟩
    show -g + x' = x
    rw [← hgx']
    abel
  · -- both in `B(y, ε)`: `g = x' - x` is a nonzero lattice point of norm `< 1`
    have hnorm : ‖g‖ < 1 := by
      have h1 : dist x' x < 2 * ε := by
        calc dist x' x ≤ dist x' y + dist x y := dist_triangle_right _ _ _
          _ < ε + ε := add_lt_add (Metric.mem_ball.1 hx'B) (Metric.mem_ball.1 hxB)
          _ = 2 * ε := by ring
      have h2 : g = x' - x := by rw [← hgx']; abel
      rw [h2, ← dist_eq_norm]
      linarith [min_le_right ε₁ (1 / 2 : ℝ)]
    exact hg0' (Sec2.Zn_abs_lt_one hgZ (fun i => by
      have := norm_le_pi_norm g i
      rw [Real.norm_eq_abs] at this
      linarith))

/-! ### Lemma 5.1 (v) and the transfer in Case III (l.316, l.326) -/

lemma linIndep_of_det (w : Fin 4 → Pt 4) (h : (colMat w).det ≠ 0) : LinearIndependent ℝ w := by
  have := Matrix.linearIndependent_cols_of_det_ne_zero h
  have hcol : (colMat w).col = w := by ext j i; rfl
  rwa [hcol] at this

lemma colMat_smul (c : ℝ) (v : Fin 4 → Pt 4) : colMat (fun i => c • v i) = c • colMat v := by
  ext a b; simp [colMat]

/-- Lemma 5.1 (v), l.316: `D ≤ 23`. -/
theorem lem_5_1_v (hTILE : CrossPolytopeNoTiling) (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4)
    (hv : IsFrame P v) : |(colMat v).det| ≤ 23 := by
  obtain ⟨h24, heq⟩ := frame_D_le_24 P hP v hv
  obtain ⟨W, hW⟩ := colMat_int v (fun i => (hv.1 i).2)
  have hD : |(colMat v).det| = ((|W.det| : ℤ) : ℝ) := by rw [hW, det_toReal, Int.cast_abs]
  rw [hD] at h24 ⊢
  have h24' : |W.det| ≤ 24 := by exact_mod_cast h24
  by_contra hgt
  have hW24 : |W.det| = 24 := by
    have : ¬ |W.det| ≤ 23 := fun h => hgt (by exact_mod_cast h)
    omega
  have hD24 : |(colMat v).det| = 24 := by rw [hD, hW24]; norm_num
  obtain ⟨hPeq, hvol⟩ := heq hD24
  have htile := half_translates_tile P hP hvol
  have hV : (colMat v).det ≠ 0 := frame_det_ne_zero P hP v hv
  have hli : LinearIndependent ℝ (fun i => (1 / 2 : ℝ) • v i) := by
    apply linIndep_of_det
    rw [colMat_smul, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hV
  apply hTILE _ hli
  have hset : Set.range (fun i => (1 / 2 : ℝ) • v i) ∪ Set.range (fun i => -((1 / 2 : ℝ) • v i)) =
      (1 / 2 : ℝ) • (Set.range v ∪ Set.range (fun i => -v i)) := by
    rw [Set.smul_set_union, Set.smul_set_range, Set.smul_set_range]
    simp only [smul_neg]
  rw [hset, convexHull_smul, ← hPeq]
  exact htile

/-- The signed-permuted frame: columns `V σ(e_j)`. -/
def spFrame (v : Fin 4 → Pt 4) (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : Fin 4 → Pt 4 :=
  fun j => (colMat v).mulVec (signedPerm σ (unitVec j))

lemma colMat_spFrame (v : Fin 4 → Pt 4) (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) :
    colMat (spFrame v σ) = colMat v * toReal (spMat σ) := by
  ext a b
  have h : spFrame v σ b = (colMat v * toReal (spMat σ)).mulVec (unitVec b) := by
    rw [spFrame, signedPerm_eq, Matrix.mulVec_mulVec]
  show spFrame v σ b a = _
  rw [h, unitVec, Matrix.mulVec_single_one]
  rfl

lemma signedPerm_unitVec (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (j : Fin 4) :
    signedPerm σ (unitVec j) = (sgn σ (σ.1.symm j) : ℝ) • unitVec (σ.1.symm j) := by
  funext i
  rw [signedPerm_apply', Pi.smul_apply, smul_eq_mul]
  by_cases h : σ.1 i = j
  · have hi : i = σ.1.symm j := by rw [← h, Equiv.symm_apply_apply]
    subst hi
    simp [unitVec]
  · have hi : i ≠ σ.1.symm j := fun hi => h (by rw [hi, Equiv.apply_symm_apply])
    simp [unitVec, h, hi]

lemma spFrame_mem (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v)
    (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (j : Fin 4) : spFrame v σ j ∈ P ∩ Zn 4 := by
  rw [spFrame, signedPerm_unitVec, Matrix.mulVec_smul, colMat_mulVec_unit]
  unfold sgn
  split_ifs
  · simpa using neg_mem_latPts hP (hv.1 (σ.1.symm j))
  · simpa using hv.1 (σ.1.symm j)

lemma spFrame_isFrame (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v)
    (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : IsFrame P (spFrame v σ) := by
  have hdet : |(colMat (spFrame v σ)).det| = |(colMat v).det| := by
    rw [colMat_spFrame, Matrix.det_mul, abs_mul, det_toReal, ← Int.cast_abs, spMat_det, Int.cast_one, mul_one]
  refine ⟨spFrame_mem P hP v hv σ, fun w hw => ?_⟩
  rw [hdet]
  exact hv.2 w hw

lemma frameLat_spFrame (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v)
    (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (Λ : Set (Pt 4)) (hΛ : frameLat v = signedPerm σ '' Λ) :
    frameLat (spFrame v σ) = Λ := by
  have hV := frame_det_ne_zero P hP v hv
  have hV' := frame_det_ne_zero P hP _ (spFrame_isFrame P hP v hv σ)
  ext x
  rw [frameLat, mem_lat_inv _ hV', colMat_spFrame, ← Matrix.mulVec_mulVec, ← signedPerm_eq, ← mem_lat_inv _ hV]
  rw [← frameLat, hΛ]
  exact (signedPerm_injective σ).mem_set_image

/-- l.326 (and l.151 (c), Figure 2): in Case III, `(P, ℤ⁴) ≅ (conv S, Λ)` for one of the 39 representatives `Λ`
and a set `S ∈ A(Λ)` with `#S ≥ 31` and `r(S) ≤ 3`; in particular `L_{conv S, Λ} = L_P` (using Computation 4). -/
theorem case_III_transfer (hTILE : CrossPolytopeNoTiling) (hC4 : Comp4) (P : Set (Pt 4)) (hP : InW (Zn 4) P)
    (hG : 31 ≤ G (Zn 4) P) (hr : rP P ≤ 3) :
    ∃ j S, Comp5Input j S ∧ IsoPair P (Zn 4) (convexHull ℝ S) (frameRep j) ∧
      ∀ k, latCount (frameRep j) (convexHull ℝ S) k = latCount (Zn 4) P k := by
  obtain ⟨⟨v, hv⟩, -⟩ := frame_D_pos P hP
  have hV := frame_det_ne_zero P hP v hv
  obtain ⟨W, hW⟩ := colMat_int v (fun i => (hv.1 i).2)
  have hW0 : W.det ≠ 0 := by rw [hW, det_toReal] at hV; exact_mod_cast hV
  have hFL : IsFrameLattice (frameLat v) := by
    refine ⟨W, hW0, ?_, by rw [frameLat, hW], lem_5_1_iv P hP v hv⟩
    have h := lem_5_1_v hTILE P hP v hv
    rw [hW, det_toReal, ← Int.cast_abs] at h
    exact_mod_cast h
  obtain ⟨j, σ, hσ⟩ := hC4.2.2 (frameLat v) hFL
  set v' := spFrame v σ with hv'def
  have hv' : IsFrame P v' := spFrame_isFrame P hP v hv σ
  have hlat : frameLat v' = frameRep j := frameLat_spFrame P hP v hv σ (frameRep j) hσ
  have hV' := frame_det_ne_zero P hP v' hv'
  have hVi := det_inv_ne_zero _ hV'
  obtain ⟨hi1, hi2, hi3⟩ := lem_5_1_i P hP v' hv'
  obtain ⟨hiii1, hiii2⟩ := lem_5_1_iii P hP v' hv'
  have hconv : convexHull ℝ (frameSet P v') = (fun x => (colMat v')⁻¹.mulVec x) '' P := by
    rw [frameSet, ← image_convexHull_mulVec, ← conv_latPts hP.1]
  refine ⟨j, frameSet P v', ⟨⟨?_, hi2, fun i => (hi3 i).1, lem_5_1_ii P hP v' hv', ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · rw [← hlat]; exact hi1
  · rw [← hlat]; exact hiii1
  · rw [← hlat]; exact hiii2
  · rw [frameSet, Set.ncard_image_of_injective _ (mulVec_injective _ hVi)]
    exact hG
  · rw [← hlat, ← (frame_M_transfer P hP v' hv').2]
    exact hr
  · refine ⟨(Sec2.linEquiv _ hVi).toLinearEquiv, ?_, ?_⟩
    · show (Sec2.linEquiv _ hVi) '' P = _
      rw [linEquiv_coe, hconv]
    · show (Sec2.linEquiv _ hVi) '' Zn 4 = _
      rw [linEquiv_coe, ← hlat, frameLat, lat_eq_image]
  · intro k
    apply latCount_iso
    refine ⟨(Sec2.linEquiv _ hVi).toLinearEquiv, ?_, ?_⟩
    · show (Sec2.linEquiv _ hVi) '' P = _
      rw [linEquiv_coe, hconv]
    · show (Sec2.linEquiv _ hVi) '' Zn 4 = _
      rw [linEquiv_coe, ← hlat, frameLat, lat_eq_image]

end Wills.Sec5
