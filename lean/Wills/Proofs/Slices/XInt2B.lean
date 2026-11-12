/-
Wills/Proofs/Slices/XInt2B.lean — the interior certificates of the interior lattice points of `2X`, slices 6-10 of 13:
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
lemma x_int2_s05 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (60, 12, 45, 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_int2_s06 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (72, 12, 45, 39) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_int2_s07 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (84, 12, 84, 28) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_int2_s08 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (96, 12, 112, 6) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma x_int2_s09 :
    sliceOk (intOk xVertsL 2 xD) (cellStrictF xFacets xBounds 2) (cells4 xBounds 2) xInt2 (108, 12, 118, 11) = true := by
  decide +kernel

end Wills.S7
