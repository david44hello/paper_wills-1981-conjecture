/-
Wills/Proofs/Slices/TMem2A.lean — the membership certificates of the lattice points of `2T`, slices 1-4 of 4: each
slice is one small kernel computation (`Wills/Proofs/Chunks.lean`).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Chunks4
import Wills.Certs.S7Data
import Wills.Proofs.Sec7Verts

namespace Wills.S7

open Wills.Chunk Wills.Count4 Wills.S7Data

set_option maxRecDepth 100000 in
lemma t_mem2_s00 :
    sliceOk (certOk tVertsL 2) (cellInF tFacets tBounds 2) (cells4 tBounds 2) tMem2 (0, 21, 0, 37) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma t_mem2_s01 :
    sliceOk (certOk tVertsL 2) (cellInF tFacets tBounds 2) (cells4 tBounds 2) tMem2 (21, 21, 37, 210) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma t_mem2_s02 :
    sliceOk (certOk tVertsL 2) (cellInF tFacets tBounds 2) (cells4 tBounds 2) tMem2 (42, 21, 247, 171) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma t_mem2_s03 :
    sliceOk (certOk tVertsL 2) (cellInF tFacets tBounds 2) (cells4 tBounds 2) tMem2 (63, 18, 418, 15) = true := by
  decide +kernel

/-- The slices `(i, m, o, n)` of this check: cells `i, …, i+m-1`, certificates `o, …, o+n-1`. -/
def t_mem2Slices : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 21, 0, 37),
    (21, 21, 37, 210),
    (42, 21, 247, 171),
    (63, 18, 418, 15)]

/-- The whole check, from its slices. -/
lemma t_mem2_sliced : memAll tVertsL tFacets tBounds 2 tMem2 = true := by
  rw [memAll_eq_zipOk, insideF_eq_cells]
  refine zipOk_of_slices _ _ _ _ t_mem2Slices (by decide +kernel) ?_
  simp only [t_mem2Slices, List.forall_mem_cons]
  exact ⟨t_mem2_s00, t_mem2_s01, t_mem2_s02, t_mem2_s03, List.forall_mem_nil _⟩

end Wills.S7
