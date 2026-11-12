/-
Wills/Proofs/Sandwich.lean — Computation 5, l.369: the start of the sandwich search.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Sec5

open MeasureTheory Pointwise

namespace Wills.Sandwich

open Wills.Sec5 (l1_closed_eq mem_lat_inv toReal_det_ne_zero toReal_mulVec_Zn ofInt_single ofInt_neg)

/-- The points `±e_1, …, ±e_4`. -/
abbrev crossPts : Set (Pt 4) := Set.range unitVec ∪ Set.range (fun i => -unitVec i)

/-- `|det M| ≤ ∏_j Σ_i |M_ij|` (each column's `ℓ¹` norm; Hadamard's inequality in its `ℓ¹` form). -/
lemma abs_det_le_prod_l1 (M : Matrix (Fin 4) (Fin 4) ℝ) : |M.det| ≤ ∏ j, ∑ i, |M i j| := by
  rw [Matrix.det_apply, Finset.prod_univ_sum, Fintype.piFinset_univ]
  calc |∑ σ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ • ∏ i, M (σ i) i|
      ≤ ∑ σ : Equiv.Perm (Fin 4), |Equiv.Perm.sign σ • ∏ i, M (σ i) i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin 4), ∏ i, |M (σ i) i| := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, Finset.abs_prod]
    _ = ∑ f ∈ Finset.univ.map ⟨fun σ : Equiv.Perm (Fin 4) => (⇑σ : Fin 4 → Fin 4), DFunLike.coe_injective⟩,
          ∏ i, |M (f i) i| := by rw [Finset.sum_map]; rfl
    _ ≤ ∑ f : Fin 4 → Fin 4, ∏ i, |M (f i) i| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun f _ _ => Finset.prod_nonneg fun i _ => abs_nonneg _)

lemma l1_open_isOpen : IsOpen {c : Pt 4 | ∑ i, |c i| < 1} :=
  isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).abs) continuous_const

/-- The interior of the closed `ℓ¹` ball lies in the open one. -/
lemma interior_l1_subset : interior {c : Pt 4 | ∑ i, |c i| ≤ 1} ⊆ {c : Pt 4 | ∑ i, |c i| < 1} := by
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  let s : Pt 4 := fun i => if 0 ≤ x i then 1 else -1
  have hterm : ∀ i, |(x + (ε / 2) • s) i| = |x i| + ε / 2 := by
    intro i
    by_cases h : 0 ≤ x i
    · simp only [s, h, if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg h]
    · have h' : x i < 0 := lt_of_not_ge h
      simp only [s, h, if_false, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_neg, mul_one]
      rw [abs_of_neg (by linarith), abs_of_neg h']
      ring
  have hmem : x + (ε / 2) • s ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, Pi.add_apply, add_sub_cancel_left, Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (half_pos hε)]
    have hs : |s i| = 1 := by by_cases h : 0 ≤ x i <;> simp [s, h]
    rw [hs, mul_one]
    linarith
  have hle : ∑ i, |(x + (ε / 2) • s) i| ≤ 1 := hball hmem
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hle
  show ∑ i, |x i| < 1
  push_cast at hle
  linarith

lemma zero_mem_interior_l1 : (0 : Pt 4) ∈ interior {c : Pt 4 | ∑ i, |c i| ≤ 1} := by
  have hsub : {c : Pt 4 | ∑ i, |c i| < 1} ⊆ {c : Pt 4 | ∑ i, |c i| ≤ 1} := fun c hc =>
    show ∑ i, |c i| ≤ 1 from le_of_lt hc
  exact interior_maximal hsub l1_open_isOpen (by simp)

lemma frame_unit_mem {Λ : Set (Pt 4)} (hΛ : IsFrameLattice Λ) (i : Fin 4) : unitVec i ∈ Λ := by
  obtain ⟨V, hV, -, rfl, -⟩ := hΛ
  exact (mem_lat_inv (toReal V) (toReal_det_ne_zero hV) _).2
    (toReal_mulVec_Zn V ⟨Pi.single i 1, ofInt_single i⟩)

lemma frame_neg_mem {Λ : Set (Pt 4)} (hΛ : IsFrameLattice Λ) {x : Pt 4} (hx : x ∈ Λ) : -x ∈ Λ := by
  obtain ⟨V, -, -, rfl, -⟩ := hΛ
  obtain ⟨z, rfl⟩ := hx
  refine ⟨-z, ?_⟩
  show (toReal V)⁻¹.mulVec (ofInt (-z)) = -((toReal V)⁻¹.mulVec (ofInt z))
  rw [ofInt_neg, Matrix.mulVec_neg]

lemma frame_zero_mem {Λ : Set (Pt 4)} (hΛ : IsFrameLattice Λ) : (0 : Pt 4) ∈ Λ := by
  obtain ⟨V, -, -, rfl, -⟩ := hΛ
  exact zero_mem_lat _

lemma l1_le_of_mem {Λ : Set (Pt 4)} {x : Pt 4} (hx : x ∈ convexHull ℝ crossPts ∩ Λ) : ∑ i, |x i| ≤ 1 := by
  have h := hx.1
  rw [l1_closed_eq] at h
  exact h

/-- The start of the sandwich search (Computation 5, l.369). -/
theorem sandwich_start_proof (Λ : Set (Pt 4)) (hΛ : IsFrameLattice Λ) :
    InA Λ (convexHull ℝ crossPts ∩ Λ) ∧ convexHull ℝ crossPts ∩ Λ ⊆ Λ ∩ cube 4 ∧
      ∀ S : Set (Pt 4), InA Λ S → convexHull ℝ crossPts ∩ Λ ⊆ S ∧ S ⊆ Λ ∩ cube 4 := by
  set Sm := convexHull ℝ crossPts ∩ Λ with hSm
  have hcross : crossPts ⊆ Sm := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨subset_convexHull ℝ _ (Or.inl ⟨i, rfl⟩), frame_unit_mem hΛ i⟩
    · exact ⟨subset_convexHull ℝ _ (Or.inr ⟨i, rfl⟩), frame_neg_mem hΛ (frame_unit_mem hΛ i)⟩
  have hcube : Sm ⊆ Λ ∩ cube 4 := fun x hx =>
    ⟨hx.2, fun i => le_trans (Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i))
      (l1_le_of_mem hx)⟩
  have hconv : convexHull ℝ Sm = convexHull ℝ crossPts :=
    Set.Subset.antisymm (convexHull_min Set.inter_subset_left (convex_convexHull ℝ _)) (convexHull_mono hcross)
  refine ⟨⟨hcube, ?_, fun i => hcross (Or.inl ⟨i, rfl⟩), ?_, ?_, ?_⟩, hcube, fun S hS => ⟨?_, hS.1⟩⟩
  · -- `-S⁻ = S⁻`
    ext x
    simp only [Set.mem_neg, hSm, Set.mem_inter_iff, l1_closed_eq, Set.mem_setOf_eq, Pi.neg_apply, abs_neg]
    exact ⟨fun h => ⟨h.1, by simpa using frame_neg_mem hΛ h.2⟩, fun h => ⟨h.1, frame_neg_mem hΛ h.2⟩⟩
  · -- (ii): every column has `ℓ¹` norm at most `1`
    intro s hs
    refine le_trans (abs_det_le_prod_l1 _) (Finset.prod_le_one₀ (fun j _ => Finset.sum_nonneg fun i _ =>
      abs_nonneg _) fun j _ => ?_)
    simpa [colMat] using l1_le_of_mem (hs j)
  · -- (iii), saturated
    show convexHull ℝ Sm ∩ Λ = Sm
    rw [hconv]
  · -- (iii), the only interior lattice point is `0`
    rw [hconv, l1_closed_eq]
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.singleton_subset_iff.2 ⟨zero_mem_interior_l1, frame_zero_mem hΛ⟩)
    by_contra hne
    obtain ⟨V, -, -, -, hshort⟩ := hΛ
    have h1 := hshort x hx.2 hne
    have h2 : ∑ i, |x i| < 1 := interior_l1_subset hx.1
    linarith
  · -- `S⁻ ⊆ S` for every `S ∈ A(Λ)`, by (i) and (iii)
    obtain ⟨-, hsymm, hunit, -, hsat, -⟩ := hS
    have hsub : crossPts ⊆ S := by
      rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact hunit i
      · rw [← hsymm]; simpa using hunit i
    intro x hx
    rw [← hsat]
    exact ⟨convexHull_mono hsub hx.1, hx.2⟩

end Wills.Sandwich
