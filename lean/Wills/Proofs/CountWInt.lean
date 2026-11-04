/-
Wills/Proofs/CountWInt.lean — `int(2W) ∩ ℤ⁵ = {-1,0,1}⁵` and `#(int(2W) ∩ ℤ⁵) = 243` (Theorem 1.3, l.218-220).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.CountW

open MeasureTheory Pointwise

namespace Wills.Count

lemma mem_boxL_bounds {k : ℕ} {z : List ℤ} (hz : z ∈ boxL k) :
    ∀ i : Fin 5, -(k : ℤ) ≤ z.getD i.val 0 ∧ z.getD i.val 0 ≤ k := by
  simp only [boxL, List.mem_flatMap, List.mem_map] at hz
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, rfl⟩ := hz
  intro i
  fin_cases i
  · exact mem_rng.1 ha
  · exact mem_rng.1 hb
  · exact mem_rng.1 hc
  · exact mem_rng.1 hd
  · exact mem_rng.1 he

lemma cubePts_eq : cubePts 5 = toPt '' {z | z ∈ boxL 1} := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨List.ofFn p, ofFn_mem_boxL (fun i => by simpa using hp i), toPt_ofFn p⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨fun i => z.getD i.val 0, fun i => by simpa using mem_boxL_bounds hz i, rfl⟩

lemma cert3Ok_sound {s : List ℤ} {c : List (ℕ × ℕ) × ℕ} (h : cert3Ok s c = true) :
    ((3 : ℝ) / 5) • toPt s ∈ W := by
  simp only [cert3Ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hN, hsum⟩, hidx⟩, hlen⟩, hz⟩ := h
  obtain ⟨hclen, hmem⟩ := combo_sound c.1 hidx
  rw [hsum] at hmem
  have e1 := toPt_scale (3 * (c.2 : ℤ)) s hlen
  have e2 := toPt_scale 5 (combo c.1) hclen
  rw [hz, e2] at e1
  have hcombo : toPt (combo c.1) = (((3 : ℝ) * c.2) / 5) • toPt s := by
    have h5 : ((5 : ℤ) : ℝ) ≠ 0 := by norm_num
    calc toPt (combo c.1) = ((5 : ℤ) : ℝ)⁻¹ • (((5 : ℤ) : ℝ) • toPt (combo c.1)) := by
          rw [smul_smul, inv_mul_cancel₀ h5, one_smul]
      _ = ((5 : ℤ) : ℝ)⁻¹ • (((3 * (c.2 : ℤ) : ℤ) : ℝ) • toPt s) := by rw [e1]
      _ = (((3 : ℝ) * c.2) / 5) • toPt s := by
          rw [smul_smul]; congr 1; push_cast; ring
  rw [hcombo, show ((3 : ℝ) * c.2) / 5 = (c.2 : ℝ) * (3 / 5) by ring, ← smul_smul] at hmem
  have hN' : ((c.2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  exact (Set.smul_mem_smul_set_iff₀ hN' _ _).1 hmem

lemma corner_in_W {x : Pt 5} (hx : ∀ i, x i = 1 ∨ x i = -1) : ((3 : ℝ) / 5) • x ∈ W := by
  let p : Fin 5 → ℤ := fun i => if x i = 1 then 1 else -1
  have hpx : toPt (List.ofFn p) = x := by
    rw [toPt_ofFn]
    funext i
    simp only [ofInt, p]
    rcases hx i with h | h <;> simp [h] <;> norm_num
  have hbox : List.ofFn p ∈ boxL 1 := ofFn_mem_boxL (fun i => by simp only [p]; split_ifs <;> norm_num)
  have hcorner : List.ofFn p ∈ cornersL := by
    simp only [cornersL, List.mem_filter, hbox, true_and, List.all_eq_true, List.mem_ofFn]
    rintro a ⟨i, rfl⟩
    simp only [p]; split_ifs <;> decide
  have hall : cornersL.length = WData.cert3.length ∧
      (cornersL.zip WData.cert3).all (fun q => cert3Ok q.1 q.2) = true := by
    have := cert3All_true
    simp only [cert3All, Bool.and_eq_true, beq_iff_eq] at this
    exact this
  obtain ⟨c, hc⟩ := forall_zip hall.1 hall.2 _ hcorner
  rw [← hpx]
  exact cert3Ok_sound hc

lemma cube_sub_W : cube 5 ⊆ ((5 : ℝ) / 3) • W := by
  rw [Sec2.cube_eq_convexHull_corners]
  refine convexHull_min ?_ (W_convex.smul _)
  intro x hx
  refine ⟨((3 : ℝ) / 5) • x, corner_in_W hx, ?_⟩
  show ((5 : ℝ) / 3) • (((3 : ℝ) / 5) • x) = x
  rw [smul_smul]
  norm_num

/-- `int(2W) ∩ ℤ⁵ = {-1,0,1}⁵` (l.220). -/
theorem w_int2_all_proof : interior ((2 : ℝ) • W) ∩ Zn 5 = cubePts 5 := by
  ext x
  constructor
  · rintro ⟨hx, p, rfl⟩
    have hsub : interior ((2 : ℝ) • W) ⊆ (2 : ℝ) • interior (cube 5) := by
      rw [← interior_smul₀ (two_ne_zero)]
      exact interior_mono (Set.smul_set_mono W_sub_cube)
    obtain ⟨y, hy, hxy⟩ := hsub hx
    rw [Sec2.interior_cube] at hy
    refine ⟨p, fun i => ?_, rfl⟩
    have h1 := hy i
    have h2 : (p i : ℝ) = 2 * y i := by
      have := congrFun hxy i
      simp only [ofInt, Pi.smul_apply, smul_eq_mul] at this
      linarith
    rw [abs_lt] at h1
    constructor
    · have : (-2 : ℝ) < p i := by linarith
      have : (-2 : ℤ) < p i := by exact_mod_cast this
      omega
    · have : (p i : ℝ) < 2 := by linarith
      have : p i < (2 : ℤ) := by exact_mod_cast this
      omega
  · rintro ⟨p, hp, rfl⟩
    refine ⟨?_, p, rfl⟩
    have hsub : ((6 : ℝ) / 5) • cube 5 ⊆ (2 : ℝ) • W := by
      calc ((6 : ℝ) / 5) • cube 5 ⊆ ((6 : ℝ) / 5) • (((5 : ℝ) / 3) • W) := Set.smul_set_mono cube_sub_W
        _ = (2 : ℝ) • W := by rw [smul_smul]; norm_num
    refine interior_mono hsub ?_
    rw [interior_smul₀ (by norm_num : ((6 : ℝ) / 5) ≠ 0), Sec2.interior_cube]
    refine ⟨((5 : ℝ) / 6) • ofInt p, fun i => ?_, ?_⟩
    · have hb := hp i
      simp only [ofInt, Pi.smul_apply, smul_eq_mul]
      rw [abs_lt]
      have h1 : (-1 : ℝ) ≤ p i := by exact_mod_cast hb.1
      have h2 : (p i : ℝ) ≤ 1 := by exact_mod_cast hb.2
      constructor <;> nlinarith
    · show ((6 : ℝ) / 5) • (((5 : ℝ) / 6) • ofInt p) = ofInt p
      rw [smul_smul]; norm_num

/-- `#(int(2W) ∩ ℤ⁵) = 243` (l.218). -/
theorem w_int2_proof : intCount (Zn 5) W 2 = 243 := by
  unfold intCount
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, w_int2_all_proof, cubePts_eq,
    ncard_toPt_image _ (fun z hz => mem_boxL_length hz) (nodup_of_chain boxL1_chain), boxL1_length]

end Wills.Count
