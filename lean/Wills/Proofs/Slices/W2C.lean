/-
Wills/Proofs/Slices/W2C.lean — the certificates that every lattice point of `2W` is a sum of two lattice points of
`W`, slices 11-13 of 13: each slice is one small kernel computation (`Wills/Proofs/Chunks.lean`).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Slices.W2Pts
import Wills.Proofs.Slices.W2A
import Wills.Proofs.Slices.W2B

namespace Wills.Count

open Wills.Chunk

set_option maxRecDepth 100000 in
lemma w2_s10 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (20, 2, 1542, 69) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma w2_s11 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (22, 2, 1611, 159) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma w2_s12 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (24, 1, 1770, 45) = true := by
  decide +kernel

/-- The slices `(i, m, o, n)` of this check: cells `i, …, i+m-1`, certificates `o, …, o+n-1`. -/
def w2Slices : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 2, 0, 120),
    (2, 2, 120, 138),
    (4, 2, 258, 79),
    (6, 2, 337, 209),
    (8, 2, 546, 131),
    (10, 2, 677, 171),
    (12, 2, 848, 222),
    (14, 2, 1070, 109),
    (16, 2, 1179, 198),
    (18, 2, 1377, 165),
    (20, 2, 1542, 69),
    (22, 2, 1611, 159),
    (24, 1, 1770, 45)]

/-- The whole check, from its slices. -/
lemma cert2All_sliced : cert2All = true := by
  rw [cert2All_eq_zipOkL insideL1_eq_wPts1, insideL_eq_cells]
  refine zipOk_of_slices _ _ _ _ w2Slices (by decide +kernel) ?_
  simp only [w2Slices, List.forall_mem_cons]
  exact ⟨w2_s00, w2_s01, w2_s02, w2_s03, w2_s04, w2_s05, w2_s06, w2_s07, w2_s08, w2_s09, w2_s10, w2_s11, w2_s12, List.forall_mem_nil _⟩

end Wills.Count
