/-
Wills/Proofs/WFacets.lean — the facets of `W` (Table 2 caption, l.196): each of the 92 facet inequalities `⟨u, x⟩ ≤ b`
of Wills/Certs/WData.lean holds on `W` and is attained at five affinely independent vertices of `W`, and no two of
them cut out the same face.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.CountW
import Wills.Certs.WFacetData

open MeasureTheory Pointwise

namespace Wills.WFacets

open Wills.Count Wills.WData

/-! ### The data, as functions of the facet index -/

/-- The `j`-th facet inequality `(u, b)`: `⟨u, x⟩ ≤ b`. -/
def fct (j : ℕ) : List ℤ × ℤ := facets.getD j ([], 0)

/-- Index (into the 50 vertices) of the `r`-th chosen vertex of facet `j`. -/
def vidx (j : ℕ) (r : Fin 5) : ℕ := (facetVerts.getD j []).getD r.val 0

/-- The integer matrix whose rows are the five chosen vertices of facet `j`. -/
def vertMat (j : ℕ) : Matrix (Fin 5) (Fin 5) ℤ := Matrix.of fun r c => (wVertsL.getD (vidx j r) []).getD c.val 0

/-- The certificate matrix `Q` of facet `j`. -/
def adjMat (j : ℕ) : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun r c => ((facetAdj.getD j ([], 0)).1.getD r.val []).getD c.val 0

/-- The certificate number `d` of facet `j`. -/
def adjDet (j : ℕ) : ℤ := (facetAdj.getD j ([], 0)).2

/-! ### The kernel checks -/

/-- Five chosen vertices, each on the facet's hyperplane, and `M Q = d I` with `d ≠ 0`. -/
def facetOk (j : ℕ) : Bool :=
  (facetVerts.getD j []).length == 5 &&
    (facetVerts.getD j []).all (fun i => decide (i < 50) && dotL (fct j).1 (wVertsL.getD i []) == (fct j).2) &&
    decide (adjDet j ≠ 0) && decide (vertMat j * adjMat j = adjDet j • (1 : Matrix (Fin 5) (Fin 5) ℤ))

/-- For `j ≠ k`, a chosen vertex of facet `j` lies strictly inside the half-space of facet `k`. -/
def apartOk (j k : ℕ) : Bool :=
  j == k || (facetVerts.getD j []).any fun i => decide (dotL (fct k).1 (wVertsL.getD i []) < (fct k).2)

/-- All checks for the 92 facets. -/
def allOk : Bool :=
  facets.length == 92 && (List.range 92).all fun j => facetOk j && (List.range 92).all (apartOk j)

set_option maxRecDepth 100000 in
lemma allOk_true : allOk = true := by decide +kernel

lemma facetOk_true {j : ℕ} (hj : j < 92) : facetOk j = true := by
  have h := allOk_true
  simp only [allOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact (h.2 j hj).1

lemma apartOk_true {j k : ℕ} (hj : j < 92) (hk : k < 92) : apartOk j k = true := by
  have h := allOk_true
  simp only [allOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact (h.2 j hj).2 k hk

/-! ### Soundness -/

lemma rdot_eq_dotProduct (u : List ℤ) (x : Pt 5) : rdot u x = toPt u ⬝ᵥ x := by
  simp [rdot, toPt, dotProduct]

lemma wVertsL_length : wVertsL.length = 50 := by decide

lemma fct_mem {j : ℕ} (hj : j < 92) : fct j ∈ facets := by
  have hlen : facets.length = 92 := by
    have h := allOk_true
    simp only [allOk, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  rw [fct, List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

/-- The `r`-th chosen vertex of facet `j`, a point of `ℝ⁵`. -/
def vpt (j : ℕ) (r : Fin 5) : Pt 5 := toPt (wVertsL.getD (vidx j r) [])

lemma facetVerts_length {j : ℕ} (hj : j < 92) : (facetVerts.getD j []).length = 5 := by
  have h := facetOk_true hj
  simp only [facetOk, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1

lemma vidx_mem {j : ℕ} (hj : j < 92) (r : Fin 5) : vidx j r ∈ facetVerts.getD j [] := by
  have hr : r.val < (facetVerts.getD j []).length := by rw [facetVerts_length hj]; exact r.isLt
  rw [vidx, List.getD_eq_getElem (facetVerts.getD j []) 0 hr]
  exact List.getElem_mem _

/-- Every chosen index of facet `j` is `vidx j r` for some `r`. -/
lemma exists_vidx {j : ℕ} (hj : j < 92) {i : ℕ} (hi : i ∈ facetVerts.getD j []) : ∃ r : Fin 5, vidx j r = i := by
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hi
  have h5 := facetVerts_length hj
  exact ⟨⟨n, by omega⟩, List.getD_eq_getElem (facetVerts.getD j []) 0 hn⟩

lemma vert_facts {j : ℕ} (hj : j < 92) (r : Fin 5) :
    vidx j r < 50 ∧ dotL (fct j).1 (wVertsL.getD (vidx j r) []) = (fct j).2 := by
  have h := facetOk_true hj
  simp only [facetOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1.2 _ (vidx_mem hj r)

lemma vert_mem {i : ℕ} (hi : i < 50) : wVertsL.getD i [] ∈ wVertsL := by
  rw [List.getD_eq_getElem _ _ (by rw [wVertsL_length]; exact hi)]
  exact List.getElem_mem _

lemma vpt_mem {j : ℕ} (hj : j < 92) (r : Fin 5) : vpt j r ∈ wPts :=
  toPt_mem_wPts (vert_mem (vert_facts hj r).1)

lemma vpt_on {j : ℕ} (hj : j < 92) (r : Fin 5) : toPt (fct j).1 ⬝ᵥ vpt j r = (fct j).2 := by
  rw [← rdot_eq_dotProduct, vpt, ← dotL_cast _ _ (facet_length (fct_mem hj))
    (mem_wVertsL_length (vert_mem (vert_facts hj r).1)), (vert_facts hj r).2]

lemma vertMat_det_ne_zero {j : ℕ} (hj : j < 92) : (vertMat j).det ≠ 0 := by
  have h := facetOk_true hj
  simp only [facetOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨_, hd⟩, hmul⟩ := h
  intro h0
  have := congrArg Matrix.det hmul
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
  exact hd (pow_eq_zero_iff (by norm_num) |>.1 this.symm)

lemma vpt_affineIndependent {j : ℕ} (hj : j < 92) : AffineIndependent ℝ (vpt j) := by
  have hmap : (Matrix.of fun r => vpt j r) = (vertMat j).map (fun x => (x : ℝ)) := by
    ext r c
    simp [vpt, vertMat, toPt]
  have hdet : (Matrix.of fun r => vpt j r).det ≠ 0 := by
    rw [hmap, ← Int.cast_det]
    exact Int.cast_ne_zero.2 (vertMat_det_ne_zero hj)
  exact (Matrix.linearIndependent_rows_of_det_ne_zero hdet).affineIndependent

/-- For `j ≠ k`, a chosen vertex of facet `j` lies strictly inside the half-space of facet `k`. -/
lemma apart_point {j k : ℕ} (hj : j < 92) (hk : k < 92) (hne : j ≠ k) :
    ∃ r : Fin 5, toPt (fct k).1 ⬝ᵥ vpt j r < ((fct k).2 : ℝ) := by
  have h := apartOk_true hj hk
  simp only [apartOk, Bool.or_eq_true, beq_iff_eq, hne, false_or, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨i, hi, hlt⟩ := h
  obtain ⟨r, hr⟩ := exists_vidx hj hi
  refine ⟨r, ?_⟩
  rw [vpt, ← rdot_eq_dotProduct, ← dotL_cast _ _ (facet_length (fct_mem hk))
    (mem_wVertsL_length (vert_mem (vert_facts hj r).1)), hr]
  exact_mod_cast hlt

/-! ### The row -/

/-- Table 2 caption, l.196: `W` has (at least) 92 facets — 92 hyperplanes `{⟨u_j, x⟩ = b_j}`, each with `W` on one
side and not inside it, and containing 5 affinely independent vertices of `W`, no two cutting out the same face. -/
theorem W_facets : ∃ (u : Fin 92 → Pt 5) (b : Fin 92 → ℝ),
    (∀ j, ∀ x ∈ W, u j ⬝ᵥ x ≤ b j) ∧ (∀ j, ∃ x ∈ W, u j ⬝ᵥ x < b j) ∧
    (∀ j, ∃ p : Fin 5 → Pt 5, (∀ i, p i ∈ wPts ∧ u j ⬝ᵥ p i = b j) ∧ AffineIndependent ℝ p) ∧
    Function.Injective (fun j => {x ∈ W | u j ⬝ᵥ x = b j}) := by
  refine ⟨fun j => toPt (fct j.val).1, fun j => ((fct j.val).2 : ℝ), ?_, ?_, ?_, ?_⟩
  · intro j x hx
    rw [← rdot_eq_dotProduct]
    exact facet_le_on_W facetsValid_true (fct_mem j.isLt) hx
  · intro j
    have hk : (j.val + 1) % 92 < 92 := Nat.mod_lt _ (by norm_num)
    have hne : (j.val + 1) % 92 ≠ j.val := by have := j.isLt; omega
    obtain ⟨r, hr⟩ := apart_point hk j.isLt hne
    exact ⟨vpt _ r, subset_convexHull ℝ _ (vpt_mem hk r), hr⟩
  · intro j
    exact ⟨vpt j.val, fun r => ⟨vpt_mem j.isLt r, vpt_on j.isLt r⟩, vpt_affineIndependent j.isLt⟩
  · intro j k hjk
    simp only at hjk
    by_contra hne
    obtain ⟨r, hlt⟩ := apart_point j.isLt k.isLt (fun h => hne (Fin.ext h))
    have hmem : vpt j.val r ∈ {x | x ∈ W ∧ toPt (fct j.val).1 ⬝ᵥ x = ((fct j.val).2 : ℝ)} :=
      ⟨subset_convexHull ℝ _ (vpt_mem j.isLt r), vpt_on j.isLt r⟩
    rw [hjk] at hmem
    exact absurd hmem.2 (ne_of_lt hlt)

end Wills.WFacets
