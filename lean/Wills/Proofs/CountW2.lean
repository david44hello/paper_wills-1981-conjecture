/-
Wills/Proofs/CountW2.lean — `#(2W ∩ ℤ⁵) = 1815` (Theorem 1.3, l.218): every lattice point of `2W` is the sum of two
lattice points of `W` (kernel-checked list of pairs), and every other point of the box `{-2,…,2}⁵` violates a facet
inequality.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.CountW

open MeasureTheory Pointwise

namespace Wills.Count

set_option maxRecDepth 100000 in
lemma cert2All_true : cert2All = true := by decide +kernel

lemma cert2_length : WData.cert2.length = 1815 := by decide +kernel

lemma cert2Ok_sound {z : List ℤ} {ij : ℕ × ℕ} (h : cert2Ok z ij = true) : toPt z ∈ (2 : ℝ) • W := by
  simp only [cert2Ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hi, hj⟩, hz⟩ := h
  have hmi : (insideL 1).getD ij.1 [] ∈ insideL 1 := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hmj : (insideL 1).getD ij.2 [] ∈ insideL 1 := by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  rw [hz, toPt_add _ _ (insideL_length5 hmi) (insideL_length5 hmj),
    show (2 : ℝ) = 1 + 1 by norm_num, W_convex.add_smul zero_le_one zero_le_one, one_smul]
  exact Set.add_mem_add (insideL1_in_W _ hmi) (insideL1_in_W _ hmj)

lemma insideL2_facts : (insideL 2).length = 1815 ∧ ∀ z ∈ insideL 2, toPt z ∈ (2 : ℝ) • W := by
  have hall : (insideL 2).length = WData.cert2.length ∧
      ((insideL 2).zip WData.cert2).all (fun q => cert2Ok q.1 q.2) = true := by
    have := cert2All_true
    simp only [cert2All, Bool.and_eq_true, beq_iff_eq] at this
    exact this
  refine ⟨hall.1.trans cert2_length, fun z hz => ?_⟩
  obtain ⟨c, hc⟩ := forall_zip hall.1 hall.2 z hz
  exact cert2Ok_sound hc

/-- `#(2W ∩ ℤ⁵) = 1815` (l.218). -/
theorem w_L2_proof : latCount (Zn 5) W 2 = 1815 := by
  have h := smulW_inter_eq 2 (fun z hz => by
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num]; exact insideL2_facts.2 z hz)
  unfold latCount
  rw [h, ncard_toPt_image _ (fun z hz => insideL_length5 hz) insideL_nodup2, insideL2_facts.1]

end Wills.Count
