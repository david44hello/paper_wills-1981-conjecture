/-
Wills/Defs/Cases.lean — Definitions for Sections 2 and 5-7 of "Wills' (1981) conjecture is fully resolved": isomorphic
pairs, saturated sets, the sublattices Γ_I, the dual lattice, M and r, frame lattices, the families S(Λ) (Lean:
`InA`), signed permutations, and Wills' conjecture.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Defs.Basic

open MeasureTheory Pointwise

namespace Wills

/-- `(P, Λ)` and `(P', Λ')` are isomorphic: a linear isomorphism `φ` of `ℝⁿ` has `φ(P) = P'` and `φ(Λ) = Λ'`. -/
def IsoPair {n : ℕ} (P Λ P' Λ' : Set (Pt n)) : Prop :=
  ∃ φ : Pt n ≃ₗ[ℝ] Pt n, φ '' P = P' ∧ φ '' Λ = Λ'

/-- The real matrix of an integer matrix. -/
def toReal {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ := U.map (fun a => (a : ℝ))

/-- `U ∈ GL_n(ℤ)`: an integer matrix with determinant `±1`. -/
def IsGLZ {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ) : Prop := U.det = 1 ∨ U.det = -1

/-- `P` and `P'` are unimodularly equivalent: `P' = U P` for some `U ∈ GL_n(ℤ)`. -/
def UnimodEquiv {n : ℕ} (P P' : Set (Pt n)) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℤ, IsGLZ U ∧ (fun x => (toReal U).mulVec x) '' P = P'

/-- `S` is `Λ`-saturated: `conv S ∩ Λ = S`. -/
def Saturated {n : ℕ} (Λ S : Set (Pt n)) : Prop := convexHull ℝ S ∩ Λ = S

/-- `S` spans `ℝⁿ`. -/
def Spans {n : ℕ} (S : Set (Pt n)) : Prop := Submodule.span ℝ S = ⊤

/-- The sublattice `Γ_I = {x ∈ ℤ⁴ : Σ_{i ∈ I} x_i even}`. -/
def gammaI (I : Finset (Fin 4)) : Set (Pt 4) :=
  {x | ∃ z : Fin 4 → ℤ, x = ofInt z ∧ Even (∑ i ∈ I, z i)}

/-- `Γ_m = Γ_{1,…,m} = {x : x_1 + ⋯ + x_m even}` (coordinates `0, …, m-1` in Lean). -/
def gammaM (m : ℕ) : Set (Pt 4) := gammaI (Finset.univ.filter (fun i : Fin 4 => i.val < m))

/-- The sublattice `B ℤ⁴` of `ℤ⁴` for an integer matrix `B`; its index is `|det B|`. -/
def subLat (B : Matrix (Fin 4) (Fin 4) ℤ) : Set (Pt 4) := lat (toReal B)

/-- The dual lattice `Λ* = {w : ⟨w, x⟩ ∈ ℤ for every x ∈ Λ}`. -/
def dualLat {n : ℕ} (Λ : Set (Pt n)) : Set (Pt n) := {w | ∀ x ∈ Λ, ∃ z : ℤ, w ⬝ᵥ x = z}

/-- `M(P) = {u ∈ ℤ⁴ : |⟨u, x⟩| ≤ 1 for all x ∈ P}` (Section 5). -/
def MP (P : Set (Pt 4)) : Set (Pt 4) := {u | u ∈ Zn 4 ∧ ∀ x ∈ P, |u ⬝ᵥ x| ≤ 1}

/-- `r(P) = dim span M(P)`. -/
noncomputable def rP (P : Set (Pt 4)) : ℕ := Module.finrank ℝ (Submodule.span ℝ (MP P))

/-- `M(S) = {w ∈ Λ* : |⟨w, s⟩| ≤ 1 for s ∈ S}` (Section 5, for `S ⊆ Λ`). -/
def MS (Λ S : Set (Pt 4)) : Set (Pt 4) := {w | w ∈ dualLat Λ ∧ ∀ s ∈ S, |w ⬝ᵥ s| ≤ 1}

/-- `r(S) = dim span M(S)`. -/
noncomputable def rS (Λ S : Set (Pt 4)) : ℕ := Module.finrank ℝ (Submodule.span ℝ (MS Λ S))

/-- Case I: `M(P)` contains a basis of `ℤ⁴` (the rows of some `U ∈ GL_4(ℤ)`). -/
def CaseI (P : Set (Pt 4)) : Prop :=
  ∃ U : Matrix (Fin 4) (Fin 4) ℤ, IsGLZ U ∧ ∀ i, ofInt (U i) ∈ MP P

/-- The unit vector `e_i`. -/
def unitVec (i : Fin 4) : Pt 4 := Pi.single i 1

/-- The matrix with columns `s 0, …, s 3`. -/
def colMat (s : Fin 4 → Pt 4) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => s j i

/-- `(v_1, …, v_4)` is a frame of `P` (Section 5, Case III): lattice points of `P` whose determinant
`D = |det(v_1, …, v_4)|` is as large as possible among lattice points of `P`. -/
def IsFrame (P : Set (Pt 4)) (v : Fin 4 → Pt 4) : Prop :=
  (∀ i, v i ∈ P ∩ Zn 4) ∧ ∀ w : Fin 4 → Pt 4, (∀ i, w i ∈ P ∩ Zn 4) → |(colMat w).det| ≤ |(colMat v).det|

/-- The lattice `Λ = V⁻¹ ℤ⁴` of a frame, `V` the matrix with columns `v_i`. -/
def frameLat (v : Fin 4 → Pt 4) : Set (Pt 4) := lat (colMat v)⁻¹

/-- The image `S = V⁻¹ (P ∩ ℤ⁴)` of the lattice points of `P` in the coordinates of the frame. -/
def frameSet (P : Set (Pt 4)) (v : Fin 4 → Pt 4) : Set (Pt 4) :=
  (fun x => ((colMat v)⁻¹).mulVec x) '' (P ∩ Zn 4)

/-- The index of a lattice `Λ ⊇ ℤ⁴` over `ℤ⁴`: the number of its points in `[0,1)⁴` (one in each coset of `ℤ⁴`). -/
noncomputable def indexOver (Λ : Set (Pt 4)) : ℕ := (Λ ∩ {x | ∀ i, 0 ≤ x i ∧ x i < 1}).ncard

/-- Lemma 5.1 (iv) for a lattice `Λ`: no `c ≠ 0` in `Λ` has `|c_1| + ⋯ + |c_4| < 1`. -/
def NoShortL1 (Λ : Set (Pt 4)) : Prop := ∀ c ∈ Λ, c ≠ 0 → 1 ≤ ∑ i, |c i|

/-- The frame lattices `𝓛`: the lattices `Λ = V⁻¹ ℤ⁴ ⊇ ℤ⁴` (`V` an integer matrix) of index `|det V| ≤ 23` over
`ℤ⁴` that satisfy Lemma 5.1 (iv). -/
def IsFrameLattice (Λ : Set (Pt 4)) : Prop :=
  ∃ V : Matrix (Fin 4) (Fin 4) ℤ, V.det ≠ 0 ∧ |V.det| ≤ 23 ∧ Λ = lat (toReal V)⁻¹ ∧ NoShortL1 Λ

/-- The family `S(Λ)` (printed `A(Λ)` up to text version 2.30): the sets `S` with Lemma 5.1 (i)-(iii):
(i) `S ⊂ Λ ∩ C_4`, `S = -S`, `±e_i ∈ S`; (ii) `|det(s_1, …, s_4)| ≤ 1` for `s_i ∈ S`;
(iii) `conv S ∩ Λ = S` and `int(conv S) ∩ Λ = {0}`. -/
def InA (Λ S : Set (Pt 4)) : Prop :=
  S ⊆ Λ ∩ cube 4 ∧ -S = S ∧ (∀ i, unitVec i ∈ S) ∧
    (∀ s : Fin 4 → Pt 4, (∀ i, s i ∈ S) → |(colMat s).det| ≤ 1) ∧
    Saturated Λ S ∧ interior (convexHull ℝ S) ∩ Λ = {0}

/-- A signed permutation of the coordinates of `ℝ⁴`: `x ↦ (ε_i x_{π i})_i` with signs `ε_i = ±1`
(`true` = minus). There are `24 · 16 = 384`. -/
def signedPerm (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (x : Pt 4) : Pt 4 :=
  fun i => (if σ.2 i then -1 else 1) * x (σ.1 i)

/-- `σ` preserves the lattice `Λ`. -/
def Preserves (Λ : Set (Pt 4)) (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : Prop := signedPerm σ '' Λ = Λ

/-- The number of classes of a family `𝓕` of sets under the signed permutations that satisfy `ok`:
the number of distinct sets `{S' ∈ 𝓕 : S' = σ(S) for some σ with ok σ}`, `S ∈ 𝓕`. -/
noncomputable def numClasses (𝓕 : Set (Set (Pt 4))) (ok : Equiv.Perm (Fin 4) × (Fin 4 → Bool) → Prop) : ℕ :=
  {C : Set (Set (Pt 4)) | ∃ S ∈ 𝓕, C = {S' | S' ∈ 𝓕 ∧ ∃ σ, ok σ ∧ S' = signedPerm σ '' S}}.ncard

/-- Wills' conjecture (Conjecture 1.1) in dimension `n`: `g_i(P) ≤ 2^i binom(n,i)` for `P ∈ Wⁿ`, `0 ≤ i ≤ n`. -/
def WillsConj (n : ℕ) : Prop :=
  ∀ P : Set (Pt n), InW (Zn n) P → ∀ i ≤ n, g (Zn n) P i ≤ (2 : ℝ) ^ i * (Nat.choose n i : ℝ)

end Wills
