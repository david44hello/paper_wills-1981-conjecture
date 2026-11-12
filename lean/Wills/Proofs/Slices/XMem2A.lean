/-
Wills/Proofs/Slices/XMem2A.lean — the membership certificates of the lattice points of `2X`, slices 1-5 of 13: each
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
lemma x_mem2_s00 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (0, 12, 0, 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_mem2_s01 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (12, 12, 1, 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_mem2_s02 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (24, 12, 9, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_mem2_s03 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (36, 12, 9, 37) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_mem2_s04 :
    sliceOk (certOk xVertsL 2) (cellInF xFacets xBounds 2) (cells4 xBounds 2) xMem2 (48, 12, 46, 58) = true := by
  decide +kernel

end Wills.S7
