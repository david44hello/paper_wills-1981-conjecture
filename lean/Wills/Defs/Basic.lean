/-
Wills/Defs/Basic.lean — Basic definitions for "Wills' (1981) conjecture is fully resolved" (Section 2 of the paper).

Points of `ℝⁿ` are functions `Fin n → ℝ`; `volume` is Lebesgue measure on them. A lattice is given as a set of points
`Λ`; the lattice `B ℤⁿ` of a real matrix `B` with `det B ≠ 0` is `lat B`, and `det (lat B) = |det B|`.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib

open MeasureTheory Polynomial Pointwise

namespace Wills

/-- Points of `ℝⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → ℝ

/-- The point of `ℝⁿ` with integer coordinates `z`. -/
def ofInt {n : ℕ} (z : Fin n → ℤ) : Pt n := fun i => (z i : ℝ)

/-- The integer lattice `ℤⁿ ⊂ ℝⁿ`. -/
def Zn (n : ℕ) : Set (Pt n) := Set.range (@ofInt n)

/-- The lattice `B ℤⁿ` spanned by the columns of the real matrix `B` (a lattice when `det B ≠ 0`). -/
def lat {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Set (Pt n) :=
  Set.range (fun z : Fin n → ℤ => B.mulVec (ofInt z))

/-- `P` is a polytope with vertices in `Λ`: the convex hull of finitely many points of `Λ`. -/
def IsLatticePolytope {n : ℕ} (Λ : Set (Pt n)) (P : Set (Pt n)) : Prop :=
  ∃ V : Finset (Pt n), (↑V : Set (Pt n)) ⊆ Λ ∧ P = convexHull ℝ (↑V : Set (Pt n))

/-- `L_{P,Λ}(k) = #(kP ∩ Λ)`. -/
noncomputable def latCount {n : ℕ} (Λ : Set (Pt n)) (P : Set (Pt n)) (k : ℕ) : ℕ :=
  (((k : ℝ) • P) ∩ Λ).ncard

/-- `#(int(kP) ∩ Λ)`. -/
noncomputable def intCount {n : ℕ} (Λ : Set (Pt n)) (P : Set (Pt n)) (k : ℕ) : ℕ :=
  (interior ((k : ℝ) • P) ∩ Λ).ncard

/-- The Ehrhart polynomial of `P` with respect to `Λ`: the polynomial of degree at most `n` that takes the
values `L_{P,Λ}(k)` at `k = 0, 1, …, n`. Ehrhart's theorem (`EhrhartThm`) says that it agrees with
`L_{P,Λ}(k)` at every integer `k ≥ 0`, so it is the polynomial `L_{P,Λ}` of the paper. -/
noncomputable def ehrhartPoly {n : ℕ} (Λ : Set (Pt n)) (P : Set (Pt n)) : ℝ[X] :=
  Lagrange.interpolate (Finset.range (n + 1)) (fun k : ℕ => (k : ℝ)) (fun k => (latCount Λ P k : ℝ))

/-- The Ehrhart coefficient `g_i(P)` with respect to `Λ`. -/
noncomputable def g {n : ℕ} (Λ : Set (Pt n)) (P : Set (Pt n)) (i : ℕ) : ℝ :=
  (ehrhartPoly Λ P).coeff i

/-- `G(P) = #(P ∩ Λ)`. -/
noncomputable def G {n : ℕ} (Λ : Set (Pt n)) (P : Set (Pt n)) : ℕ :=
  (P ∩ Λ).ncard

/-- The class `W^n_Λ`: polytopes with vertices in `Λ`, `P = -P`, and `int P ∩ Λ = {0}`. -/
def InW {n : ℕ} (Λ : Set (Pt n)) (P : Set (Pt n)) : Prop :=
  IsLatticePolytope Λ P ∧ -P = P ∧ interior P ∩ Λ = {0}

/-- The cube `C_n = [-1,1]ⁿ`. -/
def cube (n : ℕ) : Set (Pt n) := {x | ∀ i, |x i| ≤ 1}

/-- The lattice points `{-1,0,1}ⁿ` of the cube. -/
def cubePts (n : ℕ) : Set (Pt n) := ofInt '' {z : Fin n → ℤ | ∀ i, -1 ≤ z i ∧ z i ≤ 1}

/-- The product `P × Q ⊂ ℝ^{p+q}` (coordinates of `P` first). -/
def prod {p q : ℕ} (P : Set (Pt p)) (Q : Set (Pt q)) : Set (Pt (p + q)) :=
  {x | (fun i : Fin p => x (Fin.castAdd q i)) ∈ P ∧ (fun j : Fin q => x (Fin.natAdd p j)) ∈ Q}

end Wills
