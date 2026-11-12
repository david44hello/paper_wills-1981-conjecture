/-
Wills/Proofs/Cell24Eq.lean — the 24-cell `conv{±e_a ± e_b}` is the set of points `x` with `|x_i| ≤ 1` for all `i` and
`|x_1| + ⋯ + |x_4| ≤ 2` (Section 7).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import Wills.Defs.Basic
import Wills.Defs.Examples
import Wills.Proofs.Rows7

open MeasureTheory Pointwise

namespace Wills.C24

/-- The 24 points `±e_a ± e_b` (`a < b`) form a finite set. -/
lemma gens24_finite : {x : Pt 4 | ∃ a b : Fin 4, a < b ∧ ∃ s t : ℝ, (s = 1 ∨ s = -1) ∧
    (t = 1 ∨ t = -1) ∧ x = s • Pi.single a 1 + t • Pi.single b 1}.Finite := by
  refine (Set.finite_range fun p : Fin 4 × Fin 4 × Bool × Bool =>
    ((if p.2.2.1 then 1 else -1 : ℝ) • Pi.single p.1 1 +
      (if p.2.2.2 then 1 else -1 : ℝ) • Pi.single p.2.1 1 : Pt 4)).subset ?_
  rintro x ⟨a, b, -, s, t, hs, ht, rfl⟩
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact ⟨(a, b, true, true), by simp⟩
  · exact ⟨(a, b, true, false), by simp⟩
  · exact ⟨(a, b, false, true), by simp⟩
  · exact ⟨(a, b, false, false), by simp⟩

/-- A small linear-programming bound: if `d a + d b < u` for all `a ≠ b`, then `∑ d_i t_i < u`
whenever `0 ≤ d_i`, `0 ≤ t_i ≤ 1` and `∑ t_i ≤ 2`. -/
lemma sum_mul_lt_of_pair (d t : Fin 4 → ℝ) (u : ℝ) (hd : ∀ i, 0 ≤ d i) (ht0 : ∀ i, 0 ≤ t i)
    (ht1 : ∀ i, t i ≤ 1) (hts : ∑ i, t i ≤ 2) (hu : ∀ a b : Fin 4, a ≠ b → d a + d b < u) :
    ∑ i, d i * t i < u := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  obtain ⟨b, hb, hbmax⟩ := Finset.exists_max_image (Finset.univ.erase a) d
    Finset.univ_nontrivial.erase_nonempty
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  have hle : ∀ i, d i * t i ≤ d b * t i + if i = a then d a - d b else 0 := by
    intro i
    split_ifs with hi
    · subst hi
      nlinarith [ha b (Finset.mem_univ _), ht1 i, ht0 i]
    · have hib : d i ≤ d b := hbmax i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
      nlinarith [ht0 i]
  calc ∑ i, d i * t i ≤ ∑ i, (d b * t i + if i = a then d a - d b else 0) :=
        Finset.sum_le_sum fun i _ => hle i
    _ = d b * ∑ i, t i + (d a - d b) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
    _ ≤ d b * 2 + (d a - d b) := by nlinarith [hd b]
    _ = d a + d b := by ring
    _ < u := hu a b hba.symm

/-- Reverse inclusion: every `x` with `|x_i| ≤ 1` and `∑ |x_i| ≤ 2` lies in `cell24`
(separation by a linear functional plus `sum_mul_lt_of_pair`). -/
lemma box_subset_cell24 : {x : Pt 4 | (∀ i, |x i| ≤ 1) ∧ ∑ i, |x i| ≤ 2} ⊆ cell24 := by
  rintro x ⟨hx1, hx2⟩
  by_contra hx
  unfold cell24 at hx
  obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
    (gens24_finite.isClosed_convexHull ℝ) hx
  have hf : ∀ y : Pt 4, f y = ∑ i, y i * f (Pi.single i 1) := by
    intro y
    conv_lhs => rw [pi_eq_sum_univ' y]
    simp [map_sum, map_smul]
  have hgen : ∀ a b : Fin 4, a < b → ∀ s t : ℝ, (s = 1 ∨ s = -1) → (t = 1 ∨ t = -1) →
      s * f (Pi.single a 1) + t * f (Pi.single b 1) < u := by
    intro a b hab s t hs ht
    have h := hfu _ (subset_convexHull ℝ _ ⟨a, b, hab, s, t, hs, ht, rfl⟩)
    simpa [map_add, map_smul] using h
  have hlt : ∀ a b : Fin 4, a < b → |f (Pi.single a 1)| + |f (Pi.single b 1)| < u := by
    intro a b hab
    have h1 := hgen a b hab 1 1 (Or.inl rfl) (Or.inl rfl)
    have h2 := hgen a b hab 1 (-1) (Or.inl rfl) (Or.inr rfl)
    have h3 := hgen a b hab (-1) 1 (Or.inr rfl) (Or.inl rfl)
    have h4 := hgen a b hab (-1) (-1) (Or.inr rfl) (Or.inr rfl)
    rcases abs_cases (f (Pi.single a 1)) with ⟨ha, -⟩ | ⟨ha, -⟩ <;>
      rcases abs_cases (f (Pi.single b 1)) with ⟨hb, -⟩ | ⟨hb, -⟩ <;> linarith
  have hpair : ∀ a b : Fin 4, a ≠ b → |f (Pi.single a 1)| + |f (Pi.single b 1)| < u := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact hlt a b h
    · linarith [hlt b a h]
  have hbound := sum_mul_lt_of_pair (fun i => |f (Pi.single i 1)|) (fun i => |x i|) u
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) hx1 hx2 hpair
  have hfx : f x ≤ ∑ i, |f (Pi.single i 1)| * |x i| := by
    rw [hf x]
    refine Finset.sum_le_sum fun i _ => ?_
    calc x i * f (Pi.single i 1) ≤ |x i * f (Pi.single i 1)| := le_abs_self _
      _ = |f (Pi.single i 1)| * |x i| := by rw [abs_mul, mul_comm]
  linarith

/-- l.389: the polytope `conv{±e_a ± e_b}` is the set of points `x` with `|x_i| ≤ 1` for all `i` and
`|x_1| + ⋯ + |x_4| ≤ 2`. -/
theorem cell24_eq_box_proof : cell24 = {x : Pt 4 | (∀ i, |x i| ≤ 1) ∧ ∑ i, |x i| ≤ 2} := by
  exact Set.Subset.antisymm (fun x hx => Wills.Rows7.cell24_bound x hx) box_subset_cell24

end Wills.C24
