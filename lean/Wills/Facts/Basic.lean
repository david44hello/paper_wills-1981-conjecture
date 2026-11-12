/-
Wills/Facts/Basic.lean — Facts the paper uses from areas that Lean's library (Mathlib) does not cover: Ehrhart theory,
facets of polytopes, triangulations of spheres and translation tilings. Each fact is a `Prop`; every theorem that uses
one takes it as an explicit hypothesis (nothing is assumed globally). A theorem proved from these hypotheses has the
status PROVED GIVEN <facts>; the facts themselves are "not formalized: no <area> in Lean's library".
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Defs.Basic

open MeasureTheory Pointwise

namespace Wills

/-- Ehrhart's theorem [Ehr62] (Section 1, Section 2): for a lattice `Λ = B ℤⁿ` and a polytope `P` of dimension `n`
with vertices in `Λ`, `L_{P,Λ}(k) = #(kP ∩ Λ)` is a polynomial in `k ≥ 0` of degree `n`. Here: it agrees at every
`k ≥ 0` with `ehrhartPoly`, the polynomial of degree at most `n` through `k = 0, …, n` (its degree is exactly `n`
by `EhrhartLeading`, since the volume is positive). Not formalized: no Ehrhart theory in Lean's library. -/
def EhrhartThm : Prop :=
  ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ), B.det ≠ 0 → ∀ P : Set (Pt n),
    IsLatticePolytope (lat B) P → (interior P).Nonempty →
      ∀ k : ℕ, (latCount (lat B) P k : ℝ) = (ehrhartPoly (lat B) P).eval (k : ℝ)

/-- (E1), second half [BR15, Chapters 3-5]: `g_n(P) = vol(P) / det Λ`, with `det (B ℤⁿ) = |det B|`.
Not formalized: no Ehrhart theory in Lean's library. -/
def EhrhartLeading : Prop :=
  ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ), B.det ≠ 0 → ∀ P : Set (Pt n),
    IsLatticePolytope (lat B) P → (interior P).Nonempty →
      g (lat B) P n = (volume P).toReal / |B.det|

/-- (E2) Reciprocity (Ehrhart, Macdonald) [BR15, Chapters 3-5]: for every integer `k ≥ 1`,
`L_{P,Λ}(-k) = (-1)ⁿ #(int(kP) ∩ Λ)`, where `L_{P,Λ}(-k)` is the value of the Ehrhart polynomial at `-k`.
Not formalized: no Ehrhart theory in Lean's library. -/
def EhrhartReciprocity : Prop :=
  ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ), B.det ≠ 0 → ∀ P : Set (Pt n),
    IsLatticePolytope (lat B) P → (interior P).Nonempty →
      ∀ k : ℕ, 1 ≤ k → (ehrhartPoly (lat B) P).eval (-(k : ℝ)) = (-1) ^ n * (intCount (lat B) P k : ℝ)

/-- The numbers that (E3) gives for the facets `F_1, …, F_m` of `P` (`Λ = B ℤⁿ`): relative volumes
`relvol j ≥ 0` and lattice distances `b j ≥ 1` with `g_{n-1}(P) = ½ Σ_j relvol j` and
`vol(P) / det Λ = (1/n) Σ_j (b j) (relvol j)`. The lattice surface area is `σ(P) = Σ_j relvol j` and the normalized
volume of `F_j` is `NVol(F_j) = 3! relvol j` (`n = 4`). -/
def IsFacetData {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (P : Set (Pt n)) (m : ℕ) (relvol : Fin m → ℝ)
    (b : Fin m → ℤ) : Prop :=
  (∀ j, 0 ≤ relvol j) ∧ (∀ j, 1 ≤ b j) ∧ g (lat B) P (n - 1) = (1 / 2) * ∑ j, relvol j ∧
    (volume P).toReal / |B.det| = (1 / (n : ℝ)) * ∑ j, (b j : ℝ) * relvol j

/-- (E3) [BR15, Chapters 3-5] for `P ∈ W^n_Λ`, `Λ = B ℤⁿ`, `n ≥ 1`: `P` has finitely many facets `F_1, …, F_m`; let
`relvol j ≥ 0` be the `(n-1)`-dimensional volume of `F_j`, measured so that a fundamental domain of the lattice
`Λ ∩ aff(F_j - F_j)` has volume 1 (l.163), and
`b j` the integer with `F_j ⊂ {x : ⟨u_j, x⟩ = b j}` for the primitive outer normal `u_j` in the dual lattice;
`b j ≥ 1` since `0 ∈ int P` (the lattice distance of `F_j` from the origin). Then
`g_{n-1}(P) = ½ σ(P)` with `σ(P) = Σ_j relvol j` (the lattice surface area), and
`vol(P) / det Λ = (1/n) Σ_j (b j) (relvol j)`. Lean's library has no facets of polytopes, so the facets enter
only through these numbers (`IsFacetData`). Not formalized: no facets of polytopes in Lean's library. -/
def FacetFormula : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℝ), B.det ≠ 0 → ∀ P : Set (Pt n), InW (lat B) P →
    ∃ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b

/-- The facts used in the proof of Lemma 4.3, for `P ∈ W^4_Λ`, `Λ = B ℤ⁴`: there is a triangulation `Δ` of the
boundary of `P` whose vertex set is the set of all `G(P) - 1` boundary lattice points and whose tetrahedra lie in
facets: take a triangulation of `P` whose vertices are exactly the points of `P ∩ Λ` (one exists, for example by
strong pulling: [HPPS21, Lemma 2.1(2)], as numbered in arXiv:1405.1687v3, applied in the coordinates of a basis of
`Λ`; its words: AUDIT_NOTES.md, section 2); its faces in the boundary of `P` form `Δ` (l.262); `Δ` is a triangulated
3-sphere. Its f-vector
`(f 0, f 1, f 2, f 3)` satisfies:
* `f 0 = G(P) - 1`;
* `f 3 ≤ Σ_F NVol(F) = 12 g_3(P)`: each tetrahedron is a lattice tetrahedron in the affine hull of a facet, of
  normalized volume a positive integer, and `Σ_F NVol(F) = 3! σ(P) = 12 g_3(P)` by (E3);
* Walkup's lower bound theorem [Wal70, Theorem 1]: `f 1 ≥ 4 f 0 - 10` for every triangulated 3-sphere;
* the Dehn-Sommerville relations: `f 0 - f 1 + f 2 - f 3 = 0` and `2 f 2 = 4 f 3`.
Not formalized: no triangulations of spheres, no f-vectors, no facets of polytopes in Lean's library. -/
def BoundaryTriangulation : Prop :=
  ∀ B : Matrix (Fin 4) (Fin 4) ℝ, B.det ≠ 0 → ∀ P : Set (Pt 4), InW (lat B) P →
    ∃ f : Fin 4 → ℕ, (f 0 : ℤ) = (G (lat B) P : ℤ) - 1 ∧ (f 3 : ℝ) ≤ 12 * g (lat B) P 3 ∧
      (f 1 : ℤ) ≥ 4 * (f 0 : ℤ) - 10 ∧ (f 0 : ℤ) - f 1 + f 2 - f 3 = 0 ∧ 2 * f 2 = 4 * f 3

/-- The translates `K + z`, `z ∈ ℤ⁴`, tile `ℝ⁴`: they cover `ℝ⁴` and have pairwise disjoint interiors. -/
def TilesByZ4 (K : Set (Pt 4)) : Prop :=
  (⋃ z ∈ Zn 4, z +ᵥ K) = Set.univ ∧
    ∀ z ∈ Zn 4, ∀ z' ∈ Zn 4, z ≠ z' → Disjoint (interior (z +ᵥ K)) (interior (z' +ᵥ K))

/-- The tile theorem (Minkowski [Min97]; see Venkov [Ven54] and McMullen [McM80]) in the form used in the proof of
Lemma 5.1 (v): a convex polytope that tiles space by lattice translations has centrally symmetric facets, and the
facets of a cross-polytope `conv{±v_1, …, ±v_4}` (`v_i` linearly independent) are tetrahedra, which are not centrally
symmetric; so such a cross-polytope does not tile `ℝ⁴` by its translates by `ℤ⁴`.
Not formalized: no tilings and no facets of polytopes in Lean's library. -/
def CrossPolytopeNoTiling : Prop :=
  ∀ v : Fin 4 → Pt 4, LinearIndependent ℝ v →
    ¬ TilesByZ4 (convexHull ℝ (Set.range v ∪ Set.range (fun i => -v i)))

end Wills
