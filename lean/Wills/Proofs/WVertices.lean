/-
Wills/Proofs/WVertices.lean — The 50 points of Table 2: they lie in `{-1,0,1}⁵`, form a symmetric set, span `ℝ⁵`, are
distinct, and are all vertices of `W` (Theorem 1.3, l.196, l.216).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.CountW
import Wills.Certs.WVert

open MeasureTheory Pointwise

namespace Wills.Count

/-- The 50 points lie in `{-1,0,1}⁵`. -/
theorem w_pts_cube_proof : wPts ⊆ cubePts 5 := by
  rintro x ⟨p, hp, rfl | rfl⟩
  · exact ⟨p, fun i => wHalf_bounds p hp i, rfl⟩
  · refine ⟨-p, fun i => ?_, ?_⟩
    · have := wHalf_bounds p hp i
      simp only [Pi.neg_apply]
      omega
    · funext i
      simp [ofInt]

/-- The 50 points form a symmetric set. -/
theorem w_symm_proof : -wPts = wPts := by
  ext x
  rw [Set.mem_neg]
  constructor
  · rintro ⟨p, hp, h | h⟩
    · exact ⟨p, hp, Or.inr (by rw [← h, neg_neg])⟩
    · exact ⟨p, hp, Or.inl (by rw [← neg_neg x, h, neg_neg])⟩
  · rintro ⟨p, hp, rfl | rfl⟩
    · exact ⟨p, hp, Or.inr rfl⟩
    · exact ⟨p, hp, Or.inl (neg_neg _)⟩

lemma wHalf_mem_span {p : Fin 5 → ℤ} (hp : p ∈ wHalf) : ofInt p ∈ Submodule.span ℝ wPts :=
  Submodule.subset_span ⟨p, hp, Or.inl rfl⟩

lemma unit_mem_span (i : Fin 5) : (Pi.single i (1 : ℝ) : Pt 5) ∈ Submodule.span ℝ wPts := by
  have q0 := wHalf_mem_span (p := ![0, 0, 1, -1, -1]) (by decide)
  have q2 := wHalf_mem_span (p := ![0, 1, -1, 0, 0]) (by decide)
  have q5 := wHalf_mem_span (p := ![0, 1, 1, -1, -1]) (by decide)
  have q6 := wHalf_mem_span (p := ![0, 1, 1, -1, 0]) (by decide)
  have q7 := wHalf_mem_span (p := ![1, -1, -1, -1, 0]) (by decide)
  have S := Submodule.span ℝ wPts
  fin_cases i
  · show (Pi.single (0 : Fin 5) (1 : ℝ) : Pt 5) ∈ Submodule.span ℝ wPts
    have e : (Pi.single 0 (1 : ℝ) : Pt 5) = (-4 : ℝ) • ofInt ![0, 0, 1, -1, -1] + (-2 : ℝ) • ofInt ![0, 1, -1, 0, 0] +
        (4 : ℝ) • ofInt ![0, 1, 1, -1, -1] + (-1 : ℝ) • ofInt ![0, 1, 1, -1, 0] + ofInt ![1, -1, -1, -1, 0] := by
      funext j; fin_cases j <;> simp [ofInt] <;> norm_num
    rw [e]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ q0) (Submodule.smul_mem _ _ q2)) (Submodule.smul_mem _ _ q5))
      (Submodule.smul_mem _ _ q6)) q7
  · show (Pi.single (1 : Fin 5) (1 : ℝ) : Pt 5) ∈ Submodule.span ℝ wPts
    have e : (Pi.single 1 (1 : ℝ) : Pt 5) = (-1 : ℝ) • ofInt ![0, 0, 1, -1, -1] + ofInt ![0, 1, 1, -1, -1] := by
      funext j; fin_cases j <;> simp [ofInt] <;> norm_num
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ q0) q5
  · show (Pi.single (2 : Fin 5) (1 : ℝ) : Pt 5) ∈ Submodule.span ℝ wPts
    have e : (Pi.single 2 (1 : ℝ) : Pt 5) = (-1 : ℝ) • ofInt ![0, 0, 1, -1, -1] +
        (-1 : ℝ) • ofInt ![0, 1, -1, 0, 0] + ofInt ![0, 1, 1, -1, -1] := by
      funext j; fin_cases j <;> simp [ofInt] <;> norm_num
    rw [e]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ q0) (Submodule.smul_mem _ _ q2)) q5
  · show (Pi.single (3 : Fin 5) (1 : ℝ) : Pt 5) ∈ Submodule.span ℝ wPts
    have e : (Pi.single 3 (1 : ℝ) : Pt 5) = (-2 : ℝ) • ofInt ![0, 0, 1, -1, -1] +
        (-1 : ℝ) • ofInt ![0, 1, -1, 0, 0] + (2 : ℝ) • ofInt ![0, 1, 1, -1, -1] +
        (-1 : ℝ) • ofInt ![0, 1, 1, -1, 0] := by
      funext j; fin_cases j <;> simp [ofInt] <;> norm_num
    rw [e]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ q0)
      (Submodule.smul_mem _ _ q2)) (Submodule.smul_mem _ _ q5)) (Submodule.smul_mem _ _ q6)
  · show (Pi.single (4 : Fin 5) (1 : ℝ) : Pt 5) ∈ Submodule.span ℝ wPts
    have e : (Pi.single 4 (1 : ℝ) : Pt 5) = (-1 : ℝ) • ofInt ![0, 1, 1, -1, -1] + ofInt ![0, 1, 1, -1, 0] := by
      funext j; fin_cases j <;> simp [ofInt] <;> norm_num
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ q5) q6

/-- The 50 points span `ℝ⁵`. -/
theorem w_span_proof : Spans wPts := by
  unfold Spans
  rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin 5)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simpa using unit_mem_span i

/-! ### All 50 points are vertices -/

/-- A point of `s` that a linear functional separates from the other points of `s` (by a margin of 1) is an extreme
point of `conv s`. -/
lemma extreme_of_sep {s : Set (Pt 5)} {v : Pt 5} (hv : v ∈ s) (l : Pt 5 → ℝ) (hl : IsLinearMap ℝ l)
    (hsep : ∀ w ∈ s, w ≠ v → l w ≤ l v - 1) : v ∈ (convexHull ℝ s).extremePoints ℝ := by
  have hK : ∀ k ∈ convexHull ℝ (s \ {v}), l k ≤ l v - 1 :=
    fun k hk => convexHull_min (fun w hw => hsep w hw.1 hw.2) (convex_halfSpace_le hl _) hk
  have hA : ∀ y ∈ convexHull ℝ s, l y ≤ l v ∧ (l v ≤ l y → y = v) := by
    intro y hy
    rcases (s \ {v}).eq_empty_or_nonempty with h0 | hne
    · have hs : s = {v} := by
        ext w; constructor
        · intro hw; by_contra hwv; exact (Set.eq_empty_iff_forall_notMem.1 h0) w ⟨hw, hwv⟩
        · rintro rfl; exact hv
      rw [hs, convexHull_singleton] at hy
      rw [hy]; exact ⟨le_rfl, fun _ => rfl⟩
    · rw [show s = insert v (s \ {v}) by rw [Set.insert_diff_singleton, Set.insert_eq_of_mem hv],
        convexHull_insert hne, mem_convexJoin] at hy
      obtain ⟨a, ha, k, hk, α, β, hα, hβ, hαβ, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      have hlk := hK k hk
      have hlin : l (α • a + β • k) = α * l a + β * l k := by rw [hl.map_add, hl.map_smul, hl.map_smul]; rfl
      rw [hlin]
      have key : l a - (α * l a + β * l k) = β * (l a - l k) := by linear_combination (-(l a)) * hαβ
      have hb1 : β * 1 ≤ β * (l a - l k) := mul_le_mul_of_nonneg_left (by linarith) hβ
      refine ⟨by linarith, fun hle => ?_⟩
      have hβ0 : β = 0 := by linarith
      have hα1 : α = 1 := by linarith
      rw [hβ0, hα1, one_smul, zero_smul, add_zero]
  rw [mem_extremePoints]
  refine ⟨subset_convexHull ℝ s hv, fun x₁ h₁ x₂ h₂ hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hseg
  obtain ⟨h1le, h1eq⟩ := hA x₁ h₁
  obtain ⟨h2le, h2eq⟩ := hA x₂ h₂
  have hlin : l v = a * l x₁ + b * l x₂ := by rw [← hx, hl.map_add, hl.map_smul, hl.map_smul]; rfl
  have hsum : a * (l v - l x₁) + b * (l v - l x₂) = 0 := by linear_combination (l v) * hab + hlin
  have t1 : 0 ≤ a * (l v - l x₁) := mul_nonneg ha.le (sub_nonneg.2 h1le)
  have t2 : 0 ≤ b * (l v - l x₂) := mul_nonneg hb.le (sub_nonneg.2 h2le)
  have z1 : a * (l v - l x₁) = 0 := by linarith
  have z2 : b * (l v - l x₂) = 0 := by linarith
  have e1 : l v - l x₁ = 0 := (mul_eq_zero.1 z1).resolve_left ha.ne'
  have e2 : l v - l x₂ = 0 := (mul_eq_zero.1 z2).resolve_left hb.ne'
  exact ⟨h1eq (by linarith), h2eq (by linarith)⟩

/-- Every separating functional has length 5 and separates its vertex from the 49 others (integers). -/
def sepOk : Bool :=
  WVert.seps.length == 50 && WVert.seps.all (fun u => u.length == 5) &&
    (List.range 50).all fun i => (List.range 50).all fun j =>
      i == j || decide (dotL (WVert.seps.getD i []) (wVertsL.getD j []) <
        dotL (WVert.seps.getD i []) (wVertsL.getD i []))

set_option maxRecDepth 100000 in
lemma sepOk_true : sepOk = true := by decide +kernel

lemma wVertsL_length : wVertsL.length = 50 := by decide +kernel

set_option maxRecDepth 100000 in
lemma wVertsL_nodup : wVertsL.Nodup := by decide +kernel

lemma vertex_extreme (i : ℕ) (hi : i < 50) :
    toPt (wVertsL.getD i []) ∈ W.extremePoints ℝ := by
  have hs := sepOk_true
  simp only [sepOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.mem_range] at hs
  obtain ⟨⟨hlen, hlen5⟩, hsep⟩ := hs
  have hi' : i < wVertsL.length := by rw [wVertsL_length]; exact hi
  have hmemi : wVertsL.getD i [] ∈ wVertsL := by
    rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi'
  have hu : (WVert.seps.getD i []).length = 5 := by
    apply hlen5
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]
    exact List.getElem_mem _
  refine extreme_of_sep (toPt_mem_wPts hmemi) (rdot (WVert.seps.getD i [])) (rdot_isLinear _) ?_
  intro w hw hwv
  rw [wPts_eq] at hw
  obtain ⟨vj, hvj, rfl⟩ := hw
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hvj
  have hj50 : j < 50 := by rw [← wVertsL_length]; exact hj
  have hji : j ≠ i := by
    rintro rfl
    apply hwv
    rw [List.getD_eq_getElem _ _ hj]
  rcases hsep i hi j hj50 with h | h
  · exact absurd h.symm hji
  · have hj' : wVertsL.getD j [] = wVertsL[j] := List.getD_eq_getElem _ _ hj
    rw [hj'] at h
    have hint : dotL (WVert.seps.getD i []) wVertsL[j] ≤ dotL (WVert.seps.getD i []) (wVertsL.getD i []) - 1 := by
      omega
    have d1 := dotL_cast (WVert.seps.getD i []) wVertsL[j] hu (mem_wVertsL_length (List.getElem_mem hj))
    have d2 := dotL_cast (WVert.seps.getD i []) (wVertsL.getD i []) hu (mem_wVertsL_length hmemi)
    calc rdot (WVert.seps.getD i []) (toPt wVertsL[j])
        = ((dotL (WVert.seps.getD i []) wVertsL[j] : ℤ) : ℝ) := d1.symm
      _ ≤ ((dotL (WVert.seps.getD i []) (wVertsL.getD i []) : ℤ) : ℝ) - 1 := by exact_mod_cast hint
      _ = rdot (WVert.seps.getD i []) (toPt (wVertsL.getD i [])) - 1 := by rw [d2]

/-- Table 2 caption (l.196): the 50 points `±p` are distinct, and all 50 are vertices of `W`. -/
theorem tab2_vertices_proof : wPts.ncard = 50 ∧ Set.extremePoints ℝ W = wPts := by
  refine ⟨?_, ?_⟩
  · rw [wPts_eq, ncard_toPt_image _ (fun z hz => mem_wVertsL_length hz) wVertsL_nodup, wVertsL_length]
  · apply Set.Subset.antisymm extremePoints_convexHull_subset
    intro x hx
    rw [wPts_eq] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have := vertex_extreme i (by rw [← wVertsL_length]; exact hi)
    rwa [List.getD_eq_getElem _ _ hi] at this

end Wills.Count
