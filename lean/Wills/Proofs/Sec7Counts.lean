/-
Wills/Proofs/Sec7Counts.lean — the polytopes `T` and `X` of Section 7 as vertex lists; their lattice-point counts
`L(1)`, `L(2)` and `#(int(2P) ∩ ℤ⁴)`, and membership in `W⁴`, by kernel-checked certificates.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Count4
import Wills.Certs.S7Data
import Wills.Defs.Examples
import Wills.Defs.Cases

open MeasureTheory Pointwise

namespace Wills.S7

open Wills.Count4 Wills.S7Data

/-! ### The vertex lists -/

/-- The 24 points `s f_a + t f_b` (`a < b`, `s, t = ±1`) of `T`. -/
def tVertsFn : List (Fin 4 → ℤ) :=
  [((0 : Fin 4), (1 : Fin 4)), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)].flatMap fun ab =>
    [((1 : ℤ), (1 : ℤ)), (1, -1), (-1, 1), (-1, -1)].map fun st => st.1 • fVec ab.1 + st.2 • fVec ab.2

/-- The vertices of `T` as integer lists. -/
def tVertsL : List (List ℤ) := tVertsFn.map List.ofFn

/-- The 8 points `±x_i` of `X`. -/
def xVertsFn : List (Fin 4 → ℤ) := (List.finRange 4).map xVec ++ (List.finRange 4).map (fun i => -xVec i)

/-- The vertices of `X` as integer lists. -/
def xVertsL : List (List ℤ) := xVertsFn.map List.ofFn

lemma mem_tVertsFn {p : Fin 4 → ℤ} : p ∈ tVertsFn ↔
    ∃ a b : Fin 4, a < b ∧ ∃ s t : ℤ, (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧ p = s • fVec a + t • fVec b := by
  constructor
  · intro hp
    simp only [tVertsFn, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨_, _, by decide, _, _, by norm_num, by norm_num, rfl⟩
  · rintro ⟨a, b, hab, s, t, hs, ht, rfl⟩
    fin_cases a <;> fin_cases b <;> simp at hab <;> rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      decide

lemma tPts_eq : tPts = toPt4 '' {v | v ∈ tVertsL} := by
  ext x
  constructor
  · rintro ⟨a, b, hab, s, t, hs, ht, rfl⟩
    exact ⟨List.ofFn (s • fVec a + t • fVec b), List.mem_map.2 ⟨_, mem_tVertsFn.2 ⟨a, b, hab, s, t, hs, ht, rfl⟩, rfl⟩,
      toPt4_ofFn _⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
    obtain ⟨a, b, hab, s, t, hs, ht, rfl⟩ := mem_tVertsFn.1 hp
    exact ⟨a, b, hab, s, t, hs, ht, toPt4_ofFn _⟩

lemma T_eq : T = polyL tVertsL := by
  unfold T polyL
  rw [tPts_eq]

lemma xPts_eq : {x : Pt 4 | ∃ i, x = ofInt (xVec i) ∨ x = -ofInt (xVec i)} = toPt4 '' {v | v ∈ xVertsL} := by
  ext x
  constructor
  · rintro ⟨i, rfl | rfl⟩
    · exact ⟨List.ofFn (xVec i), List.mem_map.2 ⟨xVec i, List.mem_append_left _ (List.mem_map.2 ⟨i,
        List.mem_finRange i, rfl⟩), rfl⟩, toPt4_ofFn _⟩
    · refine ⟨List.ofFn (-xVec i), List.mem_map.2 ⟨-xVec i, List.mem_append_right _ (List.mem_map.2 ⟨i,
        List.mem_finRange i, rfl⟩), rfl⟩, ?_⟩
      rw [toPt4_ofFn]
      funext j
      simp [ofInt]
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp
      exact ⟨i, Or.inl (toPt4_ofFn _)⟩
    · obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp
      refine ⟨i, Or.inr ?_⟩
      rw [toPt4_ofFn]
      funext j
      simp [ofInt]

lemma X_eq : X = polyL xVertsL := by
  unfold X polyL
  rw [xPts_eq]

/-! ### Kernel checks of the certificates -/

lemma t_ne : tVertsL ≠ [] := by decide
lemma x_ne : xVertsL ≠ [] := by decide

set_option maxRecDepth 100000 in
lemma t_valid : dataValid tVertsL tFacets tBounds = true := by decide +kernel
set_option maxRecDepth 100000 in
lemma x_valid : dataValid xVertsL xFacets xBounds = true := by decide +kernel
set_option maxRecDepth 100000 in
lemma t_neg : negClosed tVertsL = true := by decide +kernel
set_option maxRecDepth 100000 in
lemma x_neg : negClosed xVertsL = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma t_chain1 : (box4 tBounds 1).IsChain (· < ·) := by decide +kernel
set_option maxRecDepth 100000 in
lemma t_chain2 : (box4 tBounds 2).IsChain (· < ·) := by decide +kernel
set_option maxRecDepth 100000 in
lemma x_chain1 : (box4 xBounds 1).IsChain (· < ·) := by decide +kernel
set_option maxRecDepth 100000 in
lemma x_chain2 : (box4 xBounds 2).IsChain (· < ·) := by decide +kernel

set_option maxRecDepth 100000 in
lemma t_mem1 : memAll tVertsL tFacets tBounds 1 tMem1 = true := by decide +kernel
set_option maxRecDepth 100000 in
lemma t_mem2 : memAll tVertsL tFacets tBounds 2 tMem2 = true := by decide +kernel
set_option maxRecDepth 100000 in
lemma x_mem1 : memAll xVertsL xFacets xBounds 1 xMem1 = true := by decide +kernel
set_option maxRecDepth 100000 in
lemma x_mem2 : memAll xVertsL xFacets xBounds 2 xMem2 = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma t_int1 : intAll tVertsL tFacets tBounds 1 tD tInt1 = true := by decide +kernel
set_option maxRecDepth 100000 in
lemma t_int2 : intAll tVertsL tFacets tBounds 2 tD tInt2 = true := by decide +kernel
set_option maxRecDepth 100000 in
lemma x_int1 : intAll xVertsL xFacets xBounds 1 xD xInt1 = true := by decide +kernel
set_option maxRecDepth 100000 in
lemma x_int2 : intAll xVertsL xFacets xBounds 2 xD xInt2 = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma t_strict1 : strictF tFacets tBounds 1 = [[0, 0, 0, 0]] := by decide +kernel
set_option maxRecDepth 100000 in
lemma x_strict1 : strictF xFacets xBounds 1 = [[0, 0, 0, 0]] := by decide +kernel

set_option maxRecDepth 100000 in
lemma t_lens : tMem1.length = 49 ∧ tMem2.length = 433 ∧ tInt2.length = 145 := by decide +kernel
set_option maxRecDepth 100000 in
lemma x_lens : xMem1.length = 33 ∧ xMem2.length = 289 ∧ xInt2.length = 129 := by decide +kernel

/-! ### The counts -/

theorem T_mem_proof : InW (Zn 4) T := by
  rw [T_eq]
  exact inW_polyL t_valid t_ne t_neg tD (by decide) tInt1 t_int1 t_strict1

theorem X_mem_proof : InW (Zn 4) X := by
  rw [X_eq]
  exact inW_polyL x_valid x_ne x_neg xD (by decide) xInt1 x_int1 x_strict1

theorem T_G_proof : G (Zn 4) T = 49 := by
  rw [← latCount_one, T_eq, latCount_eq t_valid t_ne 1 tMem1 t_mem1 t_chain1, t_lens.1]

theorem T_L2_proof : latCount (Zn 4) T 2 = 433 := by
  rw [T_eq, latCount_eq t_valid t_ne 2 tMem2 t_mem2 t_chain2, t_lens.2.1]

theorem T_int2_proof : intCount (Zn 4) T 2 = 145 := by
  rw [T_eq, intCount_eq t_valid t_ne 2 tD (by decide) tInt2 t_int2 t_chain2, t_lens.2.2]

theorem X_G_proof : G (Zn 4) X = 33 := by
  rw [← latCount_one, X_eq, latCount_eq x_valid x_ne 1 xMem1 x_mem1 x_chain1, x_lens.1]

theorem X_L2_proof : latCount (Zn 4) X 2 = 289 := by
  rw [X_eq, latCount_eq x_valid x_ne 2 xMem2 x_mem2 x_chain2, x_lens.2.1]

theorem X_int2_proof : intCount (Zn 4) X 2 = 129 := by
  rw [X_eq, intCount_eq x_valid x_ne 2 xD (by decide) xInt2 x_int2 x_chain2, x_lens.2.2]

end Wills.S7
