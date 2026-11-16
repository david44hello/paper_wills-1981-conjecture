/-
Wills/Proofs/Sec7Hyp.lean — the computable part of the facet sentences of Section 7 of "Wills' (1981) conjecture holds if
and only if the dimension is at most 4": the hyperplanes of the 24-cell, of X and of C_4, their primitive normals in the dual lattice, their
values (the lattice distances), and four affinely independent points of the polytope on each hyperplane.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Defs.Basic
import Wills.Defs.Cases
import Wills.Defs.Examples
import Wills.Proofs.Sec5
import Wills.Proofs.Rows7

open MeasureTheory Pointwise

namespace Wills.Sec7H

/-! ### Tools -/

/-- A vector `u` with `u ⬝ x = 1` for a lattice point `x` is primitive in the dual lattice. -/
lemma prim_of_dot_one {Λ : Set (Pt 4)} {u x : Pt 4} (hx : x ∈ Λ) (h1 : u ⬝ᵥ x = 1) :
    ∀ w ∈ dualLat Λ, ∀ k : ℤ, 2 ≤ k → u ≠ (k : ℝ) • w := by
  intro w hw k hk hu
  obtain ⟨m, hm⟩ := hw x hx
  rw [hu, smul_dotProduct, hm, smul_eq_mul] at h1
  have h2 : k * m = 1 := by exact_mod_cast h1
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h2 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

lemma affInd_of_det (p : Fin 4 → Pt 4) (h : (Matrix.of p).det ≠ 0) : AffineIndependent ℝ p := by
  have := (Matrix.linearIndependent_rows_of_det_ne_zero h).affineIndependent
  exact this

lemma dot_unit (a : ℝ) (i : Fin 4) (x : Pt 4) : (a • unitVec i) ⬝ᵥ x = a * x i := by
  rw [smul_dotProduct, unitVec, single_dotProduct, one_mul, smul_eq_mul]

lemma dot_ofInt (a b : Fin 4 → ℤ) : ofInt a ⬝ᵥ ofInt b = ((∑ k, a k * b k : ℤ) : ℝ) := by
  simp [ofInt, dotProduct]

lemma sq_of_pm {c : ℝ} (hc : c = 1 ∨ c = -1) : c * c = 1 := by
  rcases hc with rfl | rfl <;> norm_num

/-- A vertex `s e_a + t e_b` (`a < b`, `s, t = ±1`) of the 24-cell. -/
lemma v24_mem (a b : Fin 4) (hab : a < b) (s t : ℝ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    s • (Pi.single a 1 : Pt 4) + t • Pi.single b 1 ∈ cell24 :=
  subset_convexHull ℝ _ ⟨a, b, hab, s, t, hs, ht, rfl⟩

lemma one_pm : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl

lemma neg_one_pm : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl

/-- A vertex `s e_a + t e_b` (`a ≠ b`) of the 24-cell, in either order. -/
lemma v24_mem' (a b : Fin 4) (hab : a ≠ b) (s t : ℝ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    s • (Pi.single a 1 : Pt 4) + t • Pi.single b 1 ∈ cell24 := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact v24_mem a b h s t hs ht
  · rw [add_comm]
    exact v24_mem b a h t s ht hs

/-- The offsets `1, 1, 2, 3` (mod 4) of the second nonzero coordinate of the face points. -/
def offs : Fin 4 → Fin 4 := ![1, 1, 2, 3]

/-- The signs `+, -, +, +` of the second nonzero coordinate of the face points. -/
def tR : Fin 4 → ℝ := ![1, -1, 1, 1]

lemma offs_ne : ∀ i k : Fin 4, i + offs k ≠ i := by decide

lemma offs_ne_zero : ∀ k : Fin 4, offs k ≠ 0 := by decide

lemma tR_pm (k : Fin 4) : tR k = 1 ∨ tR k = -1 := by
  fin_cases k <;> simp [tR]

/-- Four points `c e_i + t_k e_(i + o_k)` on the hyperplane `{x_i = c}`: vertices of the 24-cell, points of `C_4`. -/
noncomputable def facePts (i : Fin 4) (c : ℝ) (k : Fin 4) : Pt 4 :=
  c • Pi.single i 1 + tR k • Pi.single (i + offs k) 1

lemma facePts_mem24 (i : Fin 4) {c : ℝ} (hc : c = 1 ∨ c = -1) (k : Fin 4) : facePts i c k ∈ cell24 :=
  v24_mem' i (i + offs k) (offs_ne i k).symm c (tR k) hc (tR_pm k)

lemma facePts_apply_i (i : Fin 4) (c : ℝ) (k : Fin 4) : facePts i c k i = c := by
  simp only [facePts, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
    Pi.single_eq_of_ne (offs_ne i k).symm, mul_one, mul_zero, add_zero]

lemma facePts_cube (i : Fin 4) {c : ℝ} (hc : c = 1 ∨ c = -1) (k : Fin 4) : facePts i c k ∈ cube 4 := by
  intro l
  by_cases h1 : l = i
  · rw [h1, facePts_apply_i]
    rcases hc with rfl | rfl <;> norm_num
  · rcases tR_pm k with h | h <;> by_cases h2 : l = i + offs k <;>
      simp [facePts, h, h1, h2, offs_ne_zero k]

lemma facePts_affInd (i : Fin 4) {c : ℝ} (hc : c = 1 ∨ c = -1) : AffineIndependent ℝ (facePts i c) := by
  apply affInd_of_det
  rcases hc with rfl | rfl <;> fin_cases i <;>
    simp [facePts, offs, tR, Pi.single_apply, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove] <;> norm_num

/-- Four vertices `s_a e_a + s_b e_b` of the 24-cell on the hyperplane `{s ⬝ x = 2}`. -/
noncomputable def sPts (s : Pt 4) : Fin 4 → Pt 4 :=
  ![s 0 • Pi.single 0 1 + s 1 • Pi.single 1 1, s 0 • Pi.single 0 1 + s 2 • Pi.single 2 1,
    s 0 • Pi.single 0 1 + s 3 • Pi.single 3 1, s 1 • Pi.single 1 1 + s 2 • Pi.single 2 1]

/-- The 0/1 pattern of `sPts`. -/
def sPat : Matrix (Fin 4) (Fin 4) ℝ := !![1, 1, 0, 0; 1, 0, 1, 0; 1, 0, 0, 1; 0, 1, 1, 0]

lemma sPts_mem24 {s : Pt 4} (hs : ∀ i, s i = 1 ∨ s i = -1) (k : Fin 4) : sPts s k ∈ cell24 := by
  fin_cases k
  · exact v24_mem 0 1 (by decide) _ _ (hs 0) (hs 1)
  · exact v24_mem 0 2 (by decide) _ _ (hs 0) (hs 2)
  · exact v24_mem 0 3 (by decide) _ _ (hs 0) (hs 3)
  · exact v24_mem 1 2 (by decide) _ _ (hs 1) (hs 2)

lemma sPts_dot {s : Pt 4} (hs : ∀ i, s i = 1 ∨ s i = -1) (k : Fin 4) : s ⬝ᵥ sPts s k = 2 := by
  have h := fun i => sq_of_pm (hs i)
  fin_cases k <;> simp [sPts, dotProduct_add, dotProduct_smul, dotProduct_single, h] <;> norm_num

lemma sPts_affInd {s : Pt 4} (hs : ∀ i, s i = 1 ∨ s i = -1) : AffineIndependent ℝ (sPts s) := by
  apply affInd_of_det
  have hM : Matrix.of (sPts s) = sPat * Matrix.diagonal s := by
    ext k j
    rw [Matrix.mul_diagonal]
    fin_cases k <;> fin_cases j <;> simp [sPts, sPat]
  have hpat : sPat.det = 2 := by
    simp [sPat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    norm_num
  rw [hM, Matrix.det_mul, hpat, Matrix.det_diagonal]
  refine mul_ne_zero two_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
  rcases hs i with h | h <;> rw [h] <;> norm_num

/-! ### T7b2 (l.389): the 48 points lie on the hyperplanes, and the 24-cell on one side of each -/

lemma half_coord {y : ℤ} (h : |(y : ℝ) + 1 / 2| ≤ 1) : (y : ℝ) + 1 / 2 = 1 / 2 ∨ (y : ℝ) + 1 / 2 = -1 / 2 := by
  rcases abs_le.1 h with ⟨h1, h2⟩
  have h3 : y < 1 := by
    have : (y : ℝ) < 1 := by linarith
    exact_mod_cast this
  have h4 : -2 < y := by
    have : (-2 : ℝ) < y := by linarith
    exact_mod_cast this
  have : y = 0 ∨ y = -1 := by omega
  rcases this with rfl | rfl <;> norm_num

lemma s_dot_le {x : Pt 4} (hx : ∑ i, |x i| ≤ 2) {s : Pt 4} (hs : ∀ i, s i = 1 ∨ s i = -1) : s ⬝ᵥ x ≤ 2 := by
  calc s ⬝ᵥ x = ∑ i, s i * x i := rfl
    _ ≤ ∑ i, |x i| := Finset.sum_le_sum fun i _ => by
        rcases hs i with h | h <;> rw [h]
        · rw [one_mul]; exact le_abs_self _
        · rw [neg_one_mul]; exact neg_le_abs _
    _ ≤ 2 := hx

/-- l.389: each of the 48 nonzero points of `conv{±e_a ± e_b} ∩ (ℤ⁴ ∪ (ℤ⁴ + ½(1,1,1,1)))` has a coordinate `±1` or
all four coordinates `±½`, so it lies on one of the hyperplanes `{x_i = ±1}` or `{±x_1 ± x_2 ± x_3 ± x_4 = 2}`; and
the 24-cell lies on one side of each of them. -/
theorem cell24_hyperplanes :
    (∀ x ∈ cell24 ∩ latD4star, x ≠ 0 →
      ((∃ i, x i = 1 ∨ x i = -1) ∨ ∀ i, x i = 1 / 2 ∨ x i = -1 / 2) ∧
      ((∃ i, x i = 1 ∨ x i = -1) ∨ ∃ s : Pt 4, (∀ i, s i = 1 ∨ s i = -1) ∧ s ⬝ᵥ x = 2)) ∧
    ∀ x ∈ cell24, (∀ i, |x i| ≤ 1) ∧ ∀ s : Pt 4, (∀ i, s i = 1 ∨ s i = -1) → s ⬝ᵥ x ≤ 2 := by
  have hbound := Rows7.cell24_points.1
  refine ⟨fun x hx hx0 => ?_, fun x hx => ⟨(hbound x hx).1, fun s hs => s_dot_le (hbound x hx).2 hs⟩⟩
  obtain ⟨hxc, hxl⟩ := hx
  have hb := (hbound x hxc).1
  rcases hxl with ⟨z, rfl⟩ | ⟨y, ⟨z, rfl⟩, rfl⟩
  · -- an integer point: a nonzero coordinate is `±1`
    have hz : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (funext fun i => by simp [ofInt, h i])
    obtain ⟨i, hi⟩ := hz
    have hzi : |z i| ≤ 1 := by
      have := hb i
      simp only [ofInt] at this
      exact_mod_cast this
    have : z i = 1 ∨ z i = -1 := by rcases abs_le.1 hzi with ⟨h1, h2⟩; omega
    have hc : ofInt z i = 1 ∨ ofInt z i = -1 := by
      rcases this with h | h <;> simp [ofInt, h]
    exact ⟨Or.inl ⟨i, hc⟩, Or.inl ⟨i, hc⟩⟩
  · -- a half-integer point: all coordinates `±½`, on `{s ⬝ x = 2}` with `s = 2x`
    set x : Pt 4 := ofInt z + fun _ => (1 / 2 : ℝ) with hxdef
    have hh : ∀ i, x i = 1 / 2 ∨ x i = -1 / 2 :=
      fun i => half_coord (y := z i) (by simpa [hxdef, ofInt] using hb i)
    refine ⟨Or.inr hh, Or.inr ⟨(2 : ℝ) • x, fun i => ?_, ?_⟩⟩
    · rcases hh i with h | h <;> rw [Pi.smul_apply, smul_eq_mul, h] <;> norm_num
    · have hsq : ∀ i, x i * x i = 1 / 4 := fun i => by
        rcases hh i with h | h <;> rw [h] <;> norm_num
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, hsq, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      norm_num

/-! ### T7b (l.389): the 49 lattice points of the 24-cell, by name -/

/-- The sign `±1` of a Boolean (`true` = minus), as an integer. -/
def sgnB (b : Bool) : ℤ := if b then -1 else 1

lemma sgnB_pm (b : Bool) : (sgnB b : ℝ) = 1 ∨ (sgnB b : ℝ) = -1 := by
  cases b <;> simp [sgnB]

/-- An integer point with `∑ |z_i| ≤ 2` is `0`, `±e_i` or `±e_a ± e_b` (`a < b`). -/
abbrev SmallClass (z : Fin 4 → ℤ) : Prop :=
  (∑ i, |z i| ≤ 2) → (∀ j, z j = 0) ∨
    (∃ a b : Fin 4, a < b ∧ ∃ s t : Bool, ∀ j, z j = sgnB s * (if j = a then 1 else 0) + sgnB t * (if j = b then 1 else 0)) ∨
    (∃ (i : Fin 4) (c : Bool), ∀ j, z j = sgnB c * (if j = i then 1 else 0))

/-- Kernel check over the 81 points of `{-1,0,1}⁴`. -/
lemma small_class_check : ∀ f : Fin 4 → Fin 3, SmallClass (fun i => ((f i : ℕ) : ℤ) - 1) := by
  decide +kernel

lemma int_point_class {z : Fin 4 → ℤ} (hb : ∀ i, |z i| ≤ 1) : SmallClass z := by
  have hf : ∀ i, (z i + 1).toNat < 3 := fun i => by have := abs_le.1 (hb i); omega
  convert small_class_check (fun i => ⟨(z i + 1).toNat, hf i⟩) using 1
  funext i
  have := abs_le.1 (hb i)
  show z i = ((z i + 1).toNat : ℤ) - 1
  omega

lemma int_pm {s : ℝ} (hs : s = 1 ∨ s = -1) : ∃ k : ℤ, s = k := by
  rcases hs with rfl | rfl
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp⟩

lemma comb_Zn (a b : Fin 4) (s t : ℤ) : (s : ℝ) • (Pi.single a 1 : Pt 4) + (t : ℝ) • Pi.single b 1 ∈ Zn 4 :=
  ⟨s • Pi.single a 1 + t • Pi.single b 1, by funext j; simp [ofInt, Pi.single_apply]⟩

lemma unit_Zn (i : Fin 4) (c : ℤ) : (c : ℝ) • unitVec i ∈ Zn 4 :=
  ⟨c • Pi.single i 1, by funext j; simp [ofInt, unitVec, Pi.single_apply]⟩

/-- `±e_i` is the midpoint of the vertices `±e_i + e_j` and `±e_i - e_j`. -/
lemma unit_mem24 (i : Fin 4) {c : ℝ} (hc : c = 1 ∨ c = -1) : c • unitVec i ∈ cell24 := by
  have heq : c • unitVec i = (1 / 2 : ℝ) • facePts i c 0 + (1 / 2 : ℝ) • facePts i c 1 := by
    funext l
    simp [facePts, tR, offs, unitVec, Pi.single_apply]
    split_ifs <;> ring
  rw [heq]
  exact (convex_convexHull ℝ _) (facePts_mem24 i hc 0) (facePts_mem24 i hc 1) (by norm_num) (by norm_num)
    (by norm_num)

/-- `(±½, ±½, ±½, ±½)` is the midpoint of the vertices `2x_1 e_1 + 2x_2 e_2` and `2x_3 e_3 + 2x_4 e_4`. -/
lemma half_mem24 {x : Pt 4} (hH : ∀ i, x i = 1 / 2 ∨ x i = -1 / 2) : x ∈ cell24 := by
  have h2 : ∀ i, 2 * x i = 1 ∨ 2 * x i = -1 := fun i => by
    rcases hH i with h | h <;> rw [h] <;> norm_num
  have heq : x = (1 / 2 : ℝ) • ((2 * x 0) • (Pi.single 0 1 : Pt 4) + (2 * x 1) • Pi.single 1 1) +
      (1 / 2 : ℝ) • ((2 * x 2) • (Pi.single 2 1 : Pt 4) + (2 * x 3) • Pi.single 3 1) := by
    funext l
    fin_cases l <;> simp
  rw [heq]
  exact (convex_convexHull ℝ _) (v24_mem 0 1 (by decide) _ _ (h2 0) (h2 1))
    (v24_mem 2 3 (by decide) _ _ (h2 2) (h2 3)) (by norm_num) (by norm_num) (by norm_num)

lemma half_lat {x : Pt 4} (hH : ∀ i, x i = 1 / 2 ∨ x i = -1 / 2) : x ∈ latD4star := by
  have hz : ∀ i, ∃ k : ℤ, x i = k + 1 / 2 := fun i => by
    rcases hH i with h | h
    · exact ⟨0, by rw [h]; norm_num⟩
    · exact ⟨-1, by rw [h]; norm_num⟩
  choose z hz using hz
  exact Or.inr ⟨ofInt z, ⟨z, rfl⟩, funext fun i => by simp [ofInt, hz i]⟩

/-- l.389: the lattice points of the 24-cell in `ℤ⁴ ∪ (ℤ⁴ + ½(1,1,1,1))` are `0`, the 24 vertices `±e_a ± e_b`,
the 8 points `±e_i` and the 16 points `(±½, ±½, ±½, ±½)` (with `cell24_points`: 49 points in all). -/
theorem cell24_lattice_points :
    cell24 ∩ latD4star = {0} ∪
      {x | ∃ a b : Fin 4, a < b ∧ ∃ s t : ℝ, (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
        x = s • Pi.single a 1 + t • Pi.single b 1} ∪
      {x | ∃ (i : Fin 4) (c : ℝ), (c = 1 ∨ c = -1) ∧ x = c • unitVec i} ∪
      {x | ∀ i, x i = 1 / 2 ∨ x i = -1 / 2} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hxc, hxl⟩
    have hb := Rows7.cell24_points.1 x hxc
    rcases hxl with ⟨z, rfl⟩ | ⟨y, ⟨z, rfl⟩, rfl⟩
    · have hzb : ∀ i, |z i| ≤ 1 := fun i => by
        have := hb.1 i
        simp only [ofInt] at this
        exact_mod_cast this
      have hzs : ∑ i, |z i| ≤ 2 := by
        have := hb.2
        simp only [ofInt] at this
        exact_mod_cast this
      rcases int_point_class hzb hzs with h0 | ⟨a, b, hab, s, t, hst⟩ | ⟨i, c, hic⟩
      · exact Or.inl (Or.inl (Or.inl (funext fun j => by simp [ofInt, h0 j])))
      · refine Or.inl (Or.inl (Or.inr ⟨a, b, hab, sgnB s, sgnB t, sgnB_pm s, sgnB_pm t, ?_⟩))
        funext j
        simp [ofInt, hst j, Pi.single_apply]
      · refine Or.inl (Or.inr ⟨i, sgnB c, sgnB_pm c, ?_⟩)
        funext j
        simp [ofInt, hic j, unitVec, Pi.single_apply]
    · exact Or.inr fun i => half_coord (y := z i) (by simpa [ofInt] using hb.1 i)
  · rintro (((rfl | ⟨a, b, hab, s, t, hs, ht, rfl⟩) | ⟨i, c, hc, rfl⟩) | hH)
    · have h0 : (0 : Pt 4) ∈ interior cell24 ∩ latD4star := by
        rw [Rows7.cell24_points.2.2]
        exact Set.mem_singleton _
      exact ⟨interior_subset h0.1, h0.2⟩
    · refine ⟨v24_mem a b hab s t hs ht, ?_⟩
      obtain ⟨s', rfl⟩ := int_pm hs
      obtain ⟨t', rfl⟩ := int_pm ht
      exact Or.inl (comb_Zn a b s' t')
    · refine ⟨unit_mem24 i hc, ?_⟩
      obtain ⟨c', rfl⟩ := int_pm hc
      exact Or.inl (unit_Zn i c')
    · exact ⟨half_mem24 hH, half_lat hH⟩

/-! ### T7d (l.389): the primitive normals of these hyperplanes, value 2 -/

/-- l.389: the vectors `±2e_i` and `(±1,±1,±1,±1)` lie in the dual lattice of `ℤ⁴ ∪ (ℤ⁴ + ½(1,1,1,1))` and are
primitive there; they are normal to the hyperplanes `{x_i = ±1}` and `{s ⬝ x = 2}` and take the value 2 on them (the
lattice distance 2); the 24-cell lies on one side, and each hyperplane contains four affinely independent vertices. -/
theorem cell24_normals :
    (∀ (i : Fin 4) (c : ℝ), (c = 1 ∨ c = -1) →
      (2 * c) • unitVec i ∈ dualLat latD4star ∧
      (∀ w ∈ dualLat latD4star, ∀ k : ℤ, 2 ≤ k → (2 * c) • unitVec i ≠ (k : ℝ) • w) ∧
      (∀ x : Pt 4, ((2 * c) • unitVec i) ⬝ᵥ x = 2 ↔ x i = c) ∧
      (∀ x ∈ cell24, ((2 * c) • unitVec i) ⬝ᵥ x ≤ 2) ∧
      ∃ p : Fin 4 → Pt 4, (∀ k, p k ∈ cell24) ∧ (∀ k, ((2 * c) • unitVec i) ⬝ᵥ p k = 2) ∧ AffineIndependent ℝ p) ∧
    ∀ s : Pt 4, (∀ i, s i = 1 ∨ s i = -1) →
      s ∈ dualLat latD4star ∧ (∀ w ∈ dualLat latD4star, ∀ k : ℤ, 2 ≤ k → s ≠ (k : ℝ) • w) ∧
      (∀ x ∈ cell24, s ⬝ᵥ x ≤ 2) ∧
      ∃ p : Fin 4 → Pt 4, (∀ k, p k ∈ cell24) ∧ (∀ k, s ⬝ᵥ p k = 2) ∧ AffineIndependent ℝ p := by
  have hbound := Rows7.cell24_points.1
  have hdual := Rows7.D4star_dual
  refine ⟨fun i c hc => ⟨?_, ?_, fun x => ?_, fun x hx => ?_, facePts i c, facePts_mem24 i hc, fun k => ?_,
    facePts_affInd i hc⟩, fun s hs => ⟨?_, ?_, fun x hx => s_dot_le (hbound x hx).2 hs, sPts s, sPts_mem24 hs,
    sPts_dot hs, sPts_affInd hs⟩⟩
  · -- `2c e_i ∈ Γ_{1234}`
    rw [hdual]
    rcases hc with rfl | rfl
    · refine ⟨Pi.single i 2, ?_, ?_⟩
      · funext j; by_cases h : j = i <;> simp [ofInt, unitVec, h]
      · simp [Pi.single_apply]
    · refine ⟨Pi.single i (-2), ?_, ?_⟩
      · funext j; by_cases h : j = i <;> simp [ofInt, unitVec, h]
      · simp [Pi.single_apply]
  · -- primitive: `x = (c/2, c/2, c/2, c/2)` is a lattice point with value 1
    have hx : (fun _ => c / 2 : Pt 4) ∈ latD4star := by
      rcases hc with rfl | rfl
      · exact Or.inr ⟨0, Sec2.zero_mem_Zn 4, by funext j; norm_num⟩
      · exact Or.inr ⟨ofInt (fun _ => -1), ⟨_, rfl⟩, by funext j; norm_num [ofInt]⟩
    refine prim_of_dot_one hx ?_
    rw [dot_unit]
    show 2 * c * (c / 2) = 1
    linear_combination sq_of_pm hc
  · rw [dot_unit]
    rcases hc with rfl | rfl <;> constructor <;> intro h <;> linarith
  · rw [dot_unit]
    have := abs_le.1 ((hbound x hx).1 i)
    rcases hc with rfl | rfl <;> linarith [this.1, this.2]
  · rw [dot_unit, facePts_apply_i]
    linear_combination 2 * sq_of_pm hc
  · -- `s ∈ Γ_{1234}`: four odd coordinates have an even sum
    rw [hdual]
    have hz : ∀ i, ∃ z : ℤ, s i = z ∧ (z = 1 ∨ z = -1) := fun i => by
      rcases hs i with h | h
      · exact ⟨1, by simp [h], Or.inl rfl⟩
      · exact ⟨-1, by simp [h], Or.inr rfl⟩
    choose z hzs hz1 using hz
    refine ⟨z, funext fun i => hzs i, ?_⟩
    rw [Fin.sum_univ_four]
    rcases hz1 0 with h0 | h0 <;> rcases hz1 1 with h1 | h1 <;> rcases hz1 2 with h2 | h2 <;>
      rcases hz1 3 with h3 | h3 <;> rw [h0, h1, h2, h3] <;> decide
  · -- primitive: `x = s_0 e_0` is a lattice point with value 1
    have hx : s 0 • unitVec 0 ∈ latD4star := by
      refine Or.inl ?_
      rcases hs 0 with h | h
      · exact ⟨Pi.single 0 1, by rw [h, one_smul]; exact Sec5.ofInt_single 0⟩
      · exact ⟨Pi.single 0 (-1), by
          rw [h]; funext j; by_cases hj : j = 0 <;> simp [ofInt, unitVec, hj]⟩
    refine prim_of_dot_one hx ?_
    rw [dotProduct_smul, unitVec, dotProduct_single, mul_one, smul_eq_mul]
    exact sq_of_pm (hs 0)

/-! ### E7b2 (l.393): the hyperplanes `{x_i = ±1}` of `C_4`, value 1 -/

/-- l.393: `±e_i` lies in the dual lattice `ℤ⁴` of `ℤ⁴` and is primitive there; the hyperplane `{±e_i ⬝ x = 1}` is
`{x_i = ±1}`, the cube `C_4` lies on one side, and the hyperplane contains four affinely independent points of `C_4`;
so the lattice distance is 1. -/
theorem cube4_hyperplanes : ∀ (i : Fin 4) (c : ℝ), (c = 1 ∨ c = -1) →
    c • unitVec i ∈ dualLat (Zn 4) ∧ (∀ w ∈ dualLat (Zn 4), ∀ k : ℤ, 2 ≤ k → c • unitVec i ≠ (k : ℝ) • w) ∧
    (∀ x : Pt 4, (c • unitVec i) ⬝ᵥ x = 1 ↔ x i = c) ∧ (∀ x ∈ cube 4, (c • unitVec i) ⬝ᵥ x ≤ 1) ∧
    ∃ p : Fin 4 → Pt 4, (∀ k, p k ∈ cube 4) ∧ (∀ k, (c • unitVec i) ⬝ᵥ p k = 1) ∧ AffineIndependent ℝ p := by
  intro i c hc
  have hcZ : c • unitVec i ∈ Zn 4 := by
    rcases hc with rfl | rfl
    · exact ⟨Pi.single i 1, by rw [one_smul]; exact Sec5.ofInt_single i⟩
    · exact ⟨Pi.single i (-1), by funext j; by_cases hj : j = i <;> simp [ofInt, unitVec, hj]⟩
  refine ⟨fun x hx => Sec5.dot_Zn hcZ hx, prim_of_dot_one hcZ ?_, fun x => ?_, fun x hx => ?_,
    facePts i c, facePts_cube i hc, fun k => ?_, facePts_affInd i hc⟩
  · rw [dot_unit, Pi.smul_apply, unitVec, Pi.single_eq_same, smul_eq_mul, mul_one]
    exact sq_of_pm hc
  · rw [dot_unit]
    rcases hc with rfl | rfl <;> constructor <;> intro h <;> linarith
  · rw [dot_unit]
    have := abs_le.1 (hx i)
    rcases hc with rfl | rfl <;> linarith [this.1, this.2]
  · rw [dot_unit, facePts_apply_i]
    exact sq_of_pm hc

/-! ### X7b (l.391): the 16 hyperplanes of `X`, value 3 -/

/-- The sign `±1` of `ε i` (`true` = minus), as an integer. -/
def sgnZ (ε : Fin 4 → Bool) (i : Fin 4) : ℤ := if ε i then -1 else 1

/-- The adjugate of the matrix with rows `xVec i` (its determinant is 18). -/
def adjX : Fin 4 → Fin 4 → ℤ := ![![18, 0, 0, 0], ![0, 18, 0, 0], ![-6, -6, 6, 0], ![-3, -9, -3, 3]]

/-- The normal `u = 3 A⁻¹ ε = adj(A) ε / 6` of the hyperplane through the points `ε_i xVec i`. -/
def xN (ε : Fin 4 → Bool) (j : Fin 4) : ℤ := (∑ i, adjX j i * sgnZ ε i) / 6

/-- Kernel check over the 16 sign vectors: `⟨u, ε_i xVec i⟩ = 3`, `|⟨u, xVec j⟩| ≤ 3`, `u_0 = ±3`, and the
coordinates of `u` have no common factor 2 or 3. -/
lemma xN_check : ∀ ε : Fin 4 → Bool,
    (∀ i, sgnZ ε i * (∑ k, xN ε k * xVec i k) = 3) ∧ (∀ j, |∑ k, xN ε k * xVec j k| ≤ 3) ∧
      (xN ε 0 = 3 ∨ xN ε 0 = -3) ∧ ¬ (∀ k, 2 ∣ xN ε k) ∧ ¬ (∀ k, 3 ∣ xN ε k) := by
  decide +kernel

lemma dual_Zn_int {w : Pt 4} (hw : w ∈ dualLat (Zn 4)) : ∃ z : Fin 4 → ℤ, w = ofInt z := by
  choose m hm using fun j => hw (unitVec j) ⟨Pi.single j 1, Sec5.ofInt_single j⟩
  refine ⟨m, funext fun j => ?_⟩
  have := hm j
  rw [unitVec, dotProduct_single, mul_one] at this
  exact this

/-- l.391: for each of the 16 sign vectors `ε`, the hyperplane through the four vertices `ε_i xVec i` of `X` is
`{u ⬝ x = 3}` for a primitive vector `u` of the dual lattice `ℤ⁴`; `X` lies on one side, and the four vertices are
affinely independent. So each of these hyperplanes has lattice distance 3. -/
theorem X_hyperplanes : ∀ ε : Fin 4 → Bool, ∃ u : Pt 4,
    u ∈ dualLat (Zn 4) ∧ (∀ w ∈ dualLat (Zn 4), ∀ k : ℤ, 2 ≤ k → u ≠ (k : ℝ) • w) ∧
    (∀ i, (if ε i then -1 else 1 : ℝ) • ofInt (xVec i) ∈ X) ∧
    (∀ i, u ⬝ᵥ ((if ε i then -1 else 1 : ℝ) • ofInt (xVec i)) = 3) ∧ (∀ y ∈ X, u ⬝ᵥ y ≤ 3) ∧
    AffineIndependent ℝ (fun i => (if ε i then -1 else 1 : ℝ) • ofInt (xVec i)) := by
  intro ε
  obtain ⟨hval, hside, h03, h2, h3⟩ := xN_check ε
  have hsgn : ∀ i, (if ε i then -1 else 1 : ℝ) = (sgnZ ε i : ℝ) := fun i => by
    unfold sgnZ; split_ifs <;> simp
  refine ⟨ofInt (xN ε), fun x hx => Sec5.dot_Zn ⟨_, rfl⟩ hx, ?_, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · -- primitive: a common factor `k ≥ 2` of the coordinates divides `u_0 = ±3`, so `k = 2` or `3`
    intro w hw k hk hu
    obtain ⟨z, rfl⟩ := dual_Zn_int hw
    have hdiv : ∀ j, k ∣ xN ε j := fun j => ⟨z j, by
      have := congrFun hu j
      simp only [ofInt, Pi.smul_apply, smul_eq_mul] at this
      exact_mod_cast this⟩
    have hk3 : k ≤ 3 := by
      have h0 := hdiv 0
      rcases h03 with h | h <;> rw [h] at h0
      · exact Int.le_of_dvd (by norm_num) h0
      · exact Int.le_of_dvd (by norm_num) (dvd_neg.1 h0)
    have : k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl
    · exact h2 hdiv
    · exact h3 hdiv
  · -- each `ε_i xVec i` is a vertex of `X`
    refine subset_convexHull ℝ _ ⟨i, ?_⟩
    split_ifs
    · right; simp
    · left; simp
  · rw [dotProduct_smul, smul_eq_mul, hsgn, dot_ofInt]
    exact_mod_cast hval i
  · -- `X` lies in the half-space `{u ⬝ y ≤ 3}`
    have hconv : Convex ℝ {y : Pt 4 | ofInt (xN ε) ⬝ᵥ y ≤ 3} := by
      intro a ha b hb s t hs ht hst
      have ha' : ofInt (xN ε) ⬝ᵥ a ≤ 3 := ha
      have hb' : ofInt (xN ε) ⬝ᵥ b ≤ 3 := hb
      show ofInt (xN ε) ⬝ᵥ (s • a + t • b) ≤ 3
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left ha' hs, mul_le_mul_of_nonneg_left hb' ht]
    intro y hy
    refine convexHull_min ?_ hconv hy
    rintro _ ⟨j, rfl | rfl⟩
    · show ofInt (xN ε) ⬝ᵥ ofInt (xVec j) ≤ 3
      rw [dot_ofInt]
      exact_mod_cast (abs_le.1 (hside j)).2
    · show ofInt (xN ε) ⬝ᵥ (-ofInt (xVec j)) ≤ 3
      rw [dotProduct_neg, dot_ofInt]
      have := (abs_le.1 (hside j)).1
      have : (-(3 : ℝ)) ≤ ((∑ k, xN ε k * xVec j k : ℤ) : ℝ) := by exact_mod_cast this
      linarith
  · -- the four points are affinely independent: `det = (∏ ε_i) · 18`
    apply affInd_of_det
    have hM : Matrix.of (fun i => (if ε i then -1 else 1 : ℝ) • ofInt (xVec i)) =
        Matrix.diagonal (fun i => (if ε i then -1 else 1 : ℝ)) * Matrix.of (fun i => ofInt (xVec i)) := by
      ext a b
      rw [Matrix.diagonal_mul]
      simp
      split_ifs <;> rfl
    have h18 : (Matrix.of (fun i => ofInt (xVec i))).det = 18 := by
      have := Rows7.X_vol.1
      rwa [show colMat (fun i => ofInt (xVec i)) = (Matrix.of (fun i => ofInt (xVec i))).transpose from rfl,
        Matrix.det_transpose] at this
    rw [hM, Matrix.det_mul, h18, Matrix.det_diagonal]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => ?_) (by norm_num)
    split_ifs <;> norm_num

end Wills.Sec7H
