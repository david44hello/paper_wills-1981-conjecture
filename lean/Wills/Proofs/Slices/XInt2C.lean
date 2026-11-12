/-
Wills/Proofs/Slices/XInt2C.lean — the interior certificates of the interior lattice points of `2X`, slices 11-13 of
13: each slice is one small kernel computation (`Wills/Proofs/Chunks.lean`).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Chunks4
import Wills.Certs.S7Data
import Wills.Proofs.Sec7Verts
import Wills.Proofs.Slices.XInt2A
import Wills.Proofs.Slices.XInt2B

namespace Wills.S7

open Wills.Chunk Wills.Count4 Wills.S7Data

set_option maxRecDepth 100000 in
lemma x_int2_s10 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (120, 12, 129, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_int2_s11 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (132, 12, 129, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_int2_s12 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (144, 9, 129, 0) = true := by
  decide +kernel

/-- The slices `(i, m, o, n)` of this check: cells `i, …, i+m-1`, certificates `o, …, o+n-1`. -/
def x_int2Slices : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 12, 0, 0),
    (12, 12, 0, 0),
    (24, 12, 0, 0),
    (36, 12, 0, 11),
    (48, 12, 11, 34),
    (60, 12, 45, 0),
    (72, 12, 45, 39),
    (84, 12, 84, 28),
    (96, 12, 112, 6),
    (108, 12, 118, 11),
    (120, 12, 129, 0),
    (132, 12, 129, 0),
    (144, 9, 129, 0)]

/-- The whole check, from its slices. -/
lemma x_int2_sliced : intAll xVertsL xFacets xBounds 2 xD xInt2 = true := by
  rw [intAll_eq_zipOk, strictF_eq_cells]
  refine zipOk_of_slices _ _ _ _ x_int2Slices (by decide +kernel) ?_
  simp only [x_int2Slices, List.forall_mem_cons]
  exact ⟨x_int2_s00, x_int2_s01, x_int2_s02, x_int2_s03, x_int2_s04, x_int2_s05, x_int2_s06, x_int2_s07, x_int2_s08, x_int2_s09, x_int2_s10, x_int2_s11, x_int2_s12, List.forall_mem_nil _⟩

end Wills.S7
