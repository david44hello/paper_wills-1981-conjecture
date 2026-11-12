/-
Wills/Proofs/Slices/W2A.lean — the certificates that every lattice point of `2W` is a sum of two lattice points of
`W`, slices 1-5 of 13: each slice is one small kernel computation (`Wills/Proofs/Chunks.lean`).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Slices.W2Pts

namespace Wills.Count

open Wills.Chunk

set_option maxRecDepth 100000 in
lemma w2_s00 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (0, 2, 0, 120) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma w2_s01 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (2, 2, 120, 138) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma w2_s02 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (4, 2, 258, 79) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma w2_s03 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (6, 2, 337, 209) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma w2_s04 :
    sliceOk (cert2OkL wPts1) (cellIn 2) (cellsL 2) WData.cert2 (8, 2, 546, 131) = true := by
  decide +kernel

end Wills.Count
