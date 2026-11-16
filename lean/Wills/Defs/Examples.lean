/-
Wills/Defs/Examples.lean — The polytopes of "Wills' (1981) conjecture holds if and only if the dimension is at most 4": W (Table 2), the 24-cell T
and the cross-polytope X (Section 7).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Defs.Basic

open MeasureTheory Pointwise

namespace Wills

/-- The 25 points `p` of Table 2 (one of each pair `±p`), in the table's order. -/
def wHalf : List (Fin 5 → ℤ) :=
  [![0, 0, 1, -1, -1], ![0, 0, 1, 1, -1], ![0, 1, -1, 0, 0], ![0, 1, 0, 1, -1], ![0, 1, 0, 1, 1],
   ![0, 1, 1, -1, -1], ![0, 1, 1, -1, 0], ![1, -1, -1, -1, 0], ![1, -1, 0, 1, 0], ![1, -1, 0, 1, 1],
   ![1, -1, 1, 0, -1], ![1, 0, -1, 0, -1], ![1, 0, -1, 1, -1], ![1, 0, -1, 1, 1], ![1, 0, 0, -1, 1],
   ![1, 0, 0, 1, 1], ![1, 0, 1, -1, 0], ![1, 0, 1, -1, 1], ![1, 0, 1, 0, -1], ![1, 1, -1, -1, -1],
   ![1, 1, -1, -1, 0], ![1, 1, -1, 1, 0], ![1, 1, 1, -1, 0], ![1, 1, 1, -1, 1], ![1, 1, 1, 1, 0]]

/-- The 50 points `±p` of Table 2. -/
def wPts : Set (Pt 5) := {x | ∃ p ∈ wHalf, x = ofInt p ∨ x = -ofInt p}

/-- The polytope `W ⊂ ℝ⁵` of Table 2: the convex hull of the 50 points `±p`. -/
def W : Set (Pt 5) := convexHull ℝ wPts

/-- `f_1, f_2, f_3 = e_1, e_2, e_3` and `f_4 = (-1,-1,-1,2)` (Section 7). -/
def fVec : Fin 4 → (Fin 4 → ℤ) := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![-1, -1, -1, 2]]

/-- The 24 points `±f_a ± f_b`, `a < b`. -/
def tPts : Set (Pt 4) :=
  {x | ∃ a b : Fin 4, a < b ∧ ∃ s t : ℤ, (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
    x = ofInt (s • fVec a + t • fVec b)}

/-- The polytope `T`: the convex hull of the 24 points `±f_a ± f_b` (a 24-cell). -/
def T : Set (Pt 4) := convexHull ℝ tPts

/-- The 24-cell `conv{±e_a ± e_b}` (Section 7). -/
def cell24 : Set (Pt 4) :=
  convexHull ℝ {x | ∃ a b : Fin 4, a < b ∧ ∃ s t : ℝ, (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
    x = s • Pi.single a 1 + t • Pi.single b 1}

/-- The lattice `ℤ⁴ ∪ (ℤ⁴ + ½(1,1,1,1))` (Section 7). -/
def latD4star : Set (Pt 4) := Zn 4 ∪ {x | ∃ y ∈ Zn 4, x = y + fun _ => (1 / 2 : ℝ)}

/-- The four vectors `(1,0,0,0), (0,1,0,0), (1,1,3,0), (2,4,3,6)` of `X`. -/
def xVec : Fin 4 → (Fin 4 → ℤ) := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 3, 0], ![2, 4, 3, 6]]

/-- The polytope `X = conv{±(1,0,0,0), ±(0,1,0,0), ±(1,1,3,0), ±(2,4,3,6)}` (Section 7). -/
def X : Set (Pt 4) := convexHull ℝ {x | ∃ i, x = ofInt (xVec i) ∨ x = -ofInt (xVec i)}

/-- A polynomial `c 0 + c 1 k + ⋯ + c d k^d` from its list of coefficients. -/
noncomputable def polyOf (c : List ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range c.length, Polynomial.C (c.getD i 0) * Polynomial.X ^ i

/-- Theorem 1.3: `1 + 101/10 k + 127/12 k² + 139/6 k³ + 557/12 k⁴ + 386/15 k⁵`. -/
noncomputable def polyW : Polynomial ℝ := polyOf [1, 101 / 10, 127 / 12, 139 / 6, 557 / 12, 386 / 15]

/-- Section 7: `L_{C_4} = 1 + 8k + 24k² + 32k³ + 16k⁴`. -/
noncomputable def polyC4 : Polynomial ℝ := polyOf [1, 8, 24, 32, 16]

/-- Section 7: `L_T = 1 + 8k + 8k² + 16k³ + 16k⁴`. -/
noncomputable def polyT : Polynomial ℝ := polyOf [1, 8, 8, 16, 16]

/-- Section 7: `L_X = 1 + 8k + 4k² + 8k³ + 12k⁴`. -/
noncomputable def polyX : Polynomial ℝ := polyOf [1, 8, 4, 8, 12]

/-- Henze's root condition [Hen14, Corollary 3.3]: every complex root of the polynomial has real part `-1/2`. -/
def HenzeRoots (p : Polynomial ℝ) : Prop := ∀ z ∈ (p.map (algebraMap ℝ ℂ)).roots, z.re = -1 / 2

end Wills
