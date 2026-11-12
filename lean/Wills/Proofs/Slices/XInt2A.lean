/-
Wills/Proofs/Slices/XInt2A.lean — the interior certificates of the interior lattice points of `2X`, slices 1-5 of 13:
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
lemma x_int2_s00 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (0, 12, 0, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_int2_s01 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (12, 12, 0, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_int2_s02 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (24, 12, 0, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_int2_s03 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (36, 12, 0, 11) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_int2_s04 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (48, 12, 11, 34) = true := by
  decide +kernel

end Wills.S7
