/-
Wills/Proofs/Slices/XMem2B.lean — the membership certificates of the lattice points of `2X`, slices 6-10 of 13: each
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
lemma x_mem2_s05 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (60, 12, 104, 4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_mem2_s06 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (72, 12, 108, 73) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_mem2_s07 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (84, 12, 181, 51) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_mem2_s08 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (96, 12, 232, 11) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_mem2_s09 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (108, 12, 243, 37) = true := by
  decide +kernel

end Wills.S7
