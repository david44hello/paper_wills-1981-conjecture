/-
Wills/Proofs/Slices/XMem2C.lean — the membership certificates of the lattice points of `2X`, slices 11-13 of 13: each
slice is one small kernel computation (`Wills/Proofs/Chunks.lean`).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Chunks4
import Wills.Certs.S7Data
import Wills.Proofs.Sec7Verts
import Wills.Proofs.Slices.XMem2A
import Wills.Proofs.Slices.XMem2B

namespace Wills.S7

open Wills.Chunk Wills.Count4 Wills.S7Data

set_option maxRecDepth 100000 in
lemma x_mem2_s10 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (120, 12, 280, 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_mem2_s11 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (132, 12, 281, 7) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_mem2_s12 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (144, 9, 288, 1) = true := by
  decide +kernel

/-- The slices `(i, m, o, n)` of this check: cells `i, …, i+m-1`, certificates `o, …, o+n-1`. -/
def x_mem2Slices : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 12, 0, 1),
    (12, 12, 1, 8),
    (24, 12, 9, 0),
    (36, 12, 9, 37),
    (48, 12, 46, 58),
    (60, 12, 104, 4),
    (72, 12, 108, 73),
    (84, 12, 181, 51),
    (96, 12, 232, 11),
    (108, 12, 243, 37),
    (120, 12, 280, 1),
    (132, 12, 281, 7),
    (144, 9, 288, 1)]

/-- The whole check, from its slices. -/
lemma x_mem2_sliced : memAll xVertsL xFacets xBounds 2 xMem2 = true := by
  rw [memAll_eq_zipOk, insideF_eq_cells]
  refine zipOk_of_slices _ _ _ _ x_mem2Slices (by decide +kernel) ?_
  simp only [x_mem2Slices, List.forall_mem_cons]
  exact ⟨x_mem2_s00, x_mem2_s01, x_mem2_s02, x_mem2_s03, x_mem2_s04, x_mem2_s05, x_mem2_s06, x_mem2_s07, x_mem2_s08, x_mem2_s09, x_mem2_s10, x_mem2_s11, x_mem2_s12, List.forall_mem_nil _⟩

end Wills.S7
