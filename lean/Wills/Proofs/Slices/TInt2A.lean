/-
Wills/Proofs/Slices/TInt2A.lean — the interior certificates of the interior lattice points of `2T`, slices 1-4 of 4:
each slice is one small kernel computation (`Wills/Proofs/Chunks.lean`).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Chunks4
import Wills.Certs.S7Data
import Wills.Proofs.Sec7Verts

namespace Wills.S7

open Wills.Chunk Wills.Count4 Wills.S7Data

set_option maxRecDepth 100000 in
lemma t_int2_s00 :
    sliceOk (intOk tVertsL 2 tD) (cellStrictF tFacets tBounds 2) (cells4 tBounds 2) tInt2 (0, 21, 0, 3) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma t_int2_s01 :
    sliceOk (intOk tVertsL 2 tD) (cellStrictF tFacets tBounds 2) (cells4 tBounds 2) tInt2 (21, 21, 3, 88) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma t_int2_s02 :
    sliceOk (intOk tVertsL 2 tD) (cellStrictF tFacets tBounds 2) (cells4 tBounds 2) tInt2 (42, 21, 91, 54) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma t_int2_s03 :
    sliceOk (intOk tVertsL 2 tD) (cellStrictF tFacets tBounds 2) (cells4 tBounds 2) tInt2 (63, 18, 145, 0) = true := by
  decide +kernel

/-- The slices `(i, m, o, n)` of this check: cells `i, …, i+m-1`, certificates `o, …, o+n-1`. -/
def t_int2Slices : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 21, 0, 3),
    (21, 21, 3, 88),
    (42, 21, 91, 54),
    (63, 18, 145, 0)]

/-- The whole check, from its slices. -/
lemma t_int2_sliced : intAll tVertsL tFacets tBounds 2 tD tInt2 = true := by
  rw [intAll_eq_zipOk, strictF_eq_cells]
  refine zipOk_of_slices _ _ _ _ t_int2Slices (by decide +kernel) ?_
  simp only [t_int2Slices, List.forall_mem_cons]
  exact ⟨t_int2_s00, t_int2_s01, t_int2_s02, t_int2_s03, List.forall_mem_nil _⟩

end Wills.S7
