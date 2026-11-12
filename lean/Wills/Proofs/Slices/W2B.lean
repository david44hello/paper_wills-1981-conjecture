/-
Wills/Proofs/Slices/W2B.lean — the certificates that every lattice point of `2W` is a sum of two lattice points of
`W`, slices 6-10 of 13: each slice is one small kernel computation (`Wills/Proofs/Chunks.lean`).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Slices.W2Pts

namespace Wills.Count

open Wills.Chunk

set_option maxRecDepth 100000 in
lemma w2_s05 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (10, 2, 677, 171) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma w2_s06 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (12, 2, 848, 222) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma w2_s07 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (14, 2, 1070, 109) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma w2_s08 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (16, 2, 1179, 198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma w2_s09 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (18, 2, 1377, 165) = true := by
  decide +kernel

end Wills.Count
