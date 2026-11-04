/-
Wills/Checks/Computations.lean — Computations 1-5 of Section 6 of "Wills' (1981) conjecture is fully resolved", each
stated exactly as printed (input set, property checked, result). Each is a `Prop`; every theorem that uses one takes
it as an explicit hypothesis. Each is checked by computer, NOT proved in Lean; the programs, their outputs and one
command per claim are in the repository folder wills-1981-conjecture/ (`./reproduce.sh computation-N`).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Defs.Cases
import Wills.Defs.Examples

open MeasureTheory Pointwise

namespace Wills

/-! ### Theorem 1.3: the volume of `W` -/

/-- The proof of Theorem 1.3, l.218: `vol(W) = 386/15`.
Checked by computer, NOT proved in Lean: `./reproduce.sh theorem-1.3` (repository folder wills-1981-conjecture/). -/
def VolW : Prop := volume W = ENNReal.ofReal (386 / 15)

/-! ### Computation 1 (Case I) -/

/-- The input of Computation 1: symmetric sets `S ⊆ {-1,0,1}⁴` with `conv S ∩ ℤ⁴ = S` and `#S ≥ 31`. -/
def Comp1Input (S : Set (Pt 4)) : Prop :=
  S ⊆ cubePts 4 ∧ -S = S ∧ Saturated (Zn 4) S ∧ 31 ≤ S.ncard

/-- Computation 1, result: for all of these sets the linear coefficient `g_1` of `conv S` is at most `8`, with
equality only for `S = {-1,0,1}⁴`.
Checked by computer, NOT proved in Lean: `./reproduce.sh computation-1` (repository folder wills-1981-conjecture/). -/
def Comp1 : Prop :=
  ∀ S : Set (Pt 4), Comp1Input S →
    g (Zn 4) (convexHull ℝ S) 1 ≤ 8 ∧ (g (Zn 4) (convexHull ℝ S) 1 = 8 → S = cubePts 4)

/-- Computation 1, count: there are 2,547,694 classes up to the 384 signed permutations of the coordinates.
Checked by computer, NOT proved in Lean: `./reproduce.sh computation-1` (repository folder wills-1981-conjecture/). -/
def Comp1Count : Prop := numClasses {S | Comp1Input S} (fun _ => True) = 2547694

/-! ### Computation 2 (index bound) -/

/-- Computation 2, result: for every sublattice `Γ = B ℤ⁴ ⊂ ℤ⁴` of index `d = |det B|`, `2 ≤ d ≤ 16`, whose points
in `{-1,0,1}⁴` span `ℝ⁴`, the number of these points is at most `45` if `d = 2` and at most `27` if `d ≥ 3`; the
maximum `45` for `d = 2` is attained.
Checked by computer, NOT proved in Lean: `./reproduce.sh computation-2` (repository folder wills-1981-conjecture/). -/
def Comp2 : Prop :=
  (∀ B : Matrix (Fin 4) (Fin 4) ℤ, 2 ≤ |B.det| → |B.det| ≤ 16 → Spans (subLat B ∩ cubePts 4) →
      (subLat B ∩ cubePts 4).ncard ≤ (if |B.det| = 2 then 45 else 27)) ∧
    ∃ B : Matrix (Fin 4) (Fin 4) ℤ, |B.det| = 2 ∧ Spans (subLat B ∩ cubePts 4) ∧ (subLat B ∩ cubePts 4).ncard = 45

/-- Computation 2, count: there are 40,406 sublattices of `ℤ⁴` of index `d` with `2 ≤ d ≤ 16`.
Checked by computer, NOT proved in Lean: `./reproduce.sh computation-2` (repository folder wills-1981-conjecture/). -/
def Comp2Count : Prop :=
  {Γ : Set (Pt 4) | ∃ B : Matrix (Fin 4) (Fin 4) ℤ, 2 ≤ |B.det| ∧ |B.det| ≤ 16 ∧ Γ = subLat B}.ncard = 40406

/-! ### Computation 3 (Case II) -/

/-- The input of Computation 3 for `m`: `Γ_m`-saturated symmetric sets `S ⊆ Γ_m ∩ {-1,0,1}⁴` that span `ℝ⁴`, with
`#S ≥ 31`. -/
def Comp3Input (m : ℕ) (S : Set (Pt 4)) : Prop :=
  S ⊆ gammaM m ∩ cubePts 4 ∧ -S = S ∧ Saturated (gammaM m) S ∧ Spans S ∧ 31 ≤ S.ncard

/-- Computation 3, result: for `m = 2, 3, 4` and all of these sets the linear coefficient `g_1` of `conv S` with
respect to `Γ_m` is at most `6`.
Checked by computer, NOT proved in Lean: `./reproduce.sh computation-3` (repository folder wills-1981-conjecture/). -/
def Comp3 : Prop :=
  ∀ m ∈ ({2, 3, 4} : Finset ℕ), ∀ S : Set (Pt 4), Comp3Input m S → g (gammaM m) (convexHull ℝ S) 1 ≤ 6

/-- Computation 3, counts: 531, 58 and 27 classes for `m = 2, 3, 4`, up to the signed permutations that preserve
`Γ_m`. Checked by computer, NOT proved in Lean: `./reproduce.sh computation-3` (repository folder
wills-1981-conjecture/). -/
def Comp3Count : Prop :=
  numClasses {S | Comp3Input 2 S} (Preserves (gammaM 2)) = 531 ∧
    numClasses {S | Comp3Input 3 S} (Preserves (gammaM 3)) = 58 ∧
    numClasses {S | Comp3Input 4 S} (Preserves (gammaM 4)) = 27

/-! ### Computation 4 (the frame lattices) -/

/-- The 39 matrices `H` of the representatives (repository file data/frame_lattices.json, key "H", in its order):
lower-triangular column Hermite normal forms; the frame vectors `v_1, …, v_4` are the rows of `H`, so the frame
matrix with columns `v_i` is `V = Hᵀ` (upper-triangular, Hermite normal form under row operations) and the
representative lattice is `Λ = V⁻¹ ℤ⁴ = (Hᵀ)⁻¹ ℤ⁴`, of index `det H` over `ℤ⁴`. -/
def frameRepH : Fin 39 → Matrix (Fin 4) (Fin 4) ℤ :=
  ![!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 1, 2],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 1, 1, 2],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 1, 1, 2],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 1, 1, 3],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 1, 1, 3],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 2, 0; 0, 1, 0, 2],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 2, 0; 1, 0, 0, 2],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 1, 2, 4],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 2, 0; 1, 1, 0, 2],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 2, 2, 4],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 1, 2, 4],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 1, 1, 4],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 1, 2, 5],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 2, 2, 5],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 2, 2, 3, 6],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 2, 3, 6],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 2, 2, 6],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 1, 3, 6],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 2, 3, 7],
    !![1, 0, 0, 0; 1, 2, 0, 0; 1, 0, 2, 0; 1, 0, 0, 2],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 2, 0; 2, 1, 0, 4],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 2, 0; 1, 2, 0, 4],
    !![1, 0, 0, 0; 0, 1, 0, 0; 1, 1, 2, 0; 1, 2, 0, 4],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 2, 0; 1, 0, 2, 4],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 2, 4, 8],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 2, 3, 4, 8],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 2, 2, 3, 8],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 3, 3, 8],
    !![1, 0, 0, 0; 0, 1, 0, 0; 1, 1, 3, 0; 1, 2, 0, 3],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 2, 3, 4, 9],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 2, 3, 4, 10],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 2, 0; 2, 1, 4, 6],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 2, 4, 5, 12],
    !![1, 0, 0, 0; 1, 2, 0, 0; 1, 0, 2, 0; 1, 2, 2, 4],
    !![1, 0, 0, 0; 0, 1, 0, 0; 1, 2, 4, 0; 2, 1, 0, 4],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 2, 0; 3, 2, 6, 8],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 3, 5, 7, 16],
    !![1, 0, 0, 0; 0, 1, 0, 0; 1, 1, 3, 0; 2, 4, 3, 6]]

/-- The `j`-th representative frame lattice `(Hᵀ)⁻¹ ℤ⁴`. -/
def frameRep (j : Fin 39) : Set (Pt 4) := lat (Matrix.transpose (toReal (frameRepH j)))⁻¹

/-- Computation 4, result: the 39 representatives are frame lattices in 39 different orbits under the signed
permutations, and every frame lattice is the image of one of them under a signed permutation.
Checked by computer, NOT proved in Lean: `./reproduce.sh computation-4` (repository folder wills-1981-conjecture/). -/
def Comp4 : Prop :=
  (∀ j, IsFrameLattice (frameRep j)) ∧
    (∀ j j', ∀ σ, frameRep j' = signedPerm σ '' frameRep j → j = j') ∧
    ∀ Λ, IsFrameLattice Λ → ∃ j σ, Λ = signedPerm σ '' frameRep j

/-- Computation 4, counts: there are 1,040 frame lattices, in 39 orbits under signed permutations, and their indices
`D` are exactly `1, …, 10, 12, 16, 18`.
Checked by computer, NOT proved in Lean: `./reproduce.sh computation-4` (repository folder wills-1981-conjecture/). -/
def Comp4Count : Prop :=
  {Λ | IsFrameLattice Λ}.ncard = 1040 ∧ numClasses {Λ | IsFrameLattice Λ} (fun _ => True) = 39 ∧
    {D : ℤ | ∃ V : Matrix (Fin 4) (Fin 4) ℤ, V.det ≠ 0 ∧ |V.det| = D ∧ D ≤ 23 ∧ NoShortL1 (lat (toReal V)⁻¹)} =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 16, 18}

/-! ### Computation 5 (Case III) -/

/-- The input of Computation 5 for the representative `j`: `S ∈ A(Λ)` with `#S ≥ 31` and `r(S) ≤ 3`. -/
def Comp5Input (j : Fin 39) (S : Set (Pt 4)) : Prop :=
  InA (frameRep j) S ∧ 31 ≤ S.ncard ∧ rS (frameRep j) S ≤ 3

/-- Computation 5, result: for all of these sets the linear coefficient `g_1` of `conv S` with respect to `Λ` is at
most `8`, with equality for exactly two sets (up to the signed permutations that preserve `Λ`), one with `G = 49`
and one with `G = 33`.
Checked by computer, NOT proved in Lean: `./reproduce.sh computation-5` (repository folder wills-1981-conjecture/). -/
def Comp5 : Prop :=
  (∀ j S, Comp5Input j S → g (frameRep j) (convexHull ℝ S) 1 ≤ 8) ∧
    (∀ j S, Comp5Input j S → g (frameRep j) (convexHull ℝ S) 1 = 8 → S.ncard = 49 ∨ S.ncard = 33) ∧
    (∀ j j' S S', Comp5Input j S → Comp5Input j' S' → g (frameRep j) (convexHull ℝ S) 1 = 8 →
      g (frameRep j') (convexHull ℝ S') 1 = 8 → S.ncard = S'.ncard →
        j = j' ∧ ∃ σ, Preserves (frameRep j) σ ∧ S' = signedPerm σ '' S) ∧
    (∃ j S, Comp5Input j S ∧ g (frameRep j) (convexHull ℝ S) 1 = 8 ∧ S.ncard = 49) ∧
    (∃ j S, Comp5Input j S ∧ g (frameRep j) (convexHull ℝ S) 1 = 8 ∧ S.ncard = 33)

/-- Computation 5, count: 588,592 classes in all (summed over the 39 representatives, each up to the signed
permutations that preserve it).
Checked by computer, NOT proved in Lean: `./reproduce.sh computation-5` (repository folder wills-1981-conjecture/). -/
def Comp5Count : Prop :=
  ∑ j : Fin 39, numClasses {S | Comp5Input j S} (Preserves (frameRep j)) = 588592

end Wills
