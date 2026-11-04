/-
Wills/Proofs/CountData.lean — Computable checks for the lattice-point counts of `W`: integer lists, the box
`{-k,…,k}⁵`, the facet filter, and the certificate checkers.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Defs.Examples
import Wills.Certs.WData

namespace Wills.Count

/-- Integer dot product of two lists. -/
def dotL (u x : List ℤ) : ℤ := (List.zipWith (· * ·) u x).sum

/-- `{-k, …, k}` in increasing order. -/
def rng (k : ℕ) : List ℤ := (List.range (2 * k + 1)).map (fun i : ℕ => (i : ℤ) - (k : ℤ))

/-- The box `{-k, …, k}⁵` as lists of length 5, in lexicographic order. -/
def boxL (k : ℕ) : List (List ℤ) :=
  (rng k).flatMap fun a => (rng k).flatMap fun b => (rng k).flatMap fun c =>
    (rng k).flatMap fun d => (rng k).map fun e => [a, b, c, d, e]

/-- The 50 vertices of `W` as lists: the 25 points of Table 2, then their negatives. -/
def wVertsL : List (List ℤ) := wHalf.map List.ofFn ++ wHalf.map (fun p => List.ofFn (-p))

/-- Every facet inequality holds at every vertex. -/
def facetsValid : Bool :=
  WData.facets.all fun f => f.1.length == 5 && wVertsL.all fun v => decide (dotL f.1 v ≤ f.2)

/-- The points of the box `{-k,…,k}⁵` that satisfy every facet inequality of `kW`. -/
def insideL (k : ℕ) : List (List ℤ) :=
  (boxL k).filter fun z => WData.facets.all fun f => decide (dotL f.1 z ≤ k * f.2)

/-- `Σ n_j v_j` over a list of pairs `(j, n_j)`. -/
def combo (pairs : List (ℕ × ℕ)) : List ℤ :=
  pairs.foldr (fun p acc => List.zipWith (· + ·) acc ((wVertsL.getD p.1 []).map (fun c => (p.2 : ℤ) * c)))
    [0, 0, 0, 0, 0]

/-- One membership certificate: `N > 0`, the weights sum to `N`, every index is a vertex, and `N z = Σ n_j v_j`. -/
def cert1Ok (z : List ℤ) (c : List (ℕ × ℕ) × ℕ) : Bool :=
  decide (0 < c.2) && (c.1.map Prod.snd).sum == c.2 && c.1.all (fun p => decide (p.1 < 50)) &&
    z.length == 5 && z.map (fun a => (c.2 : ℤ) * a) == combo c.1

/-- All membership certificates for the lattice points of `W`. -/
def cert1All : Bool :=
  (insideL 1).length == WData.cert1.length && ((insideL 1).zip WData.cert1).all fun q => cert1Ok q.1 q.2

/-- One 2W certificate: `z = p_i + p_j` for two lattice points of `W`. -/
def cert2Ok (z : List ℤ) (ij : ℕ × ℕ) : Bool :=
  decide (ij.1 < (insideL 1).length) && decide (ij.2 < (insideL 1).length) &&
    z == List.zipWith (· + ·) ((insideL 1).getD ij.1 []) ((insideL 1).getD ij.2 [])

/-- All 2W certificates. -/
def cert2All : Bool :=
  (insideL 2).length == WData.cert2.length && ((insideL 2).zip WData.cert2).all fun q => cert2Ok q.1 q.2

/-- The corners of `{-1,1}⁵` (lexicographic order). -/
def cornersL : List (List ℤ) := (boxL 1).filter fun z => z.all fun a => a != 0

/-- One corner certificate: `5 Σ n_j v_j = 3 N s`. -/
def cert3Ok (s : List ℤ) (c : List (ℕ × ℕ) × ℕ) : Bool :=
  decide (0 < c.2) && (c.1.map Prod.snd).sum == c.2 && c.1.all (fun p => decide (p.1 < 50)) &&
    s.length == 5 && s.map (fun a => 3 * (c.2 : ℤ) * a) == (combo c.1).map (fun a => 5 * a)

/-- All corner certificates. -/
def cert3All : Bool :=
  cornersL.length == WData.cert3.length && (cornersL.zip WData.cert3).all fun q => cert3Ok q.1 q.2

end Wills.Count
