/-
Wills/Proofs/Sec7Verts.lean — the vertices of the polytopes `T` and `X` of Section 7 as integer lists (used by the
slice files of their lattice-point counts and by `Sec7Counts.lean`).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Defs.Examples

namespace Wills.S7

/-- The 24 points `s f_a + t f_b` (`a < b`, `s, t = ±1`) of `T`. -/
def tVertsFn : List (Fin 4 → ℤ) :=
  [((0 : Fin 4), (1 : Fin 4)), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)].flatMap fun ab =>
    [((1 : ℤ), (1 : ℤ)), (1, -1), (-1, 1), (-1, -1)].map fun st => st.1 • fVec ab.1 + st.2 • fVec ab.2

/-- The vertices of `T` as integer lists. -/
def tVertsL : List (List ℤ) := tVertsFn.map List.ofFn

/-- The 8 points `±x_i` of `X`. -/
def xVertsFn : List (Fin 4 → ℤ) := (List.finRange 4).map xVec ++ (List.finRange 4).map (fun i => -xVec i)

/-- The vertices of `X` as integer lists. -/
def xVertsL : List (List ℤ) := xVertsFn.map List.ofFn

end Wills.S7
