/-
Wills/Proofs/Chunks4.lean — the box `∏_i {-k B_i, …, k B_i}` of `ℝ⁴` as cells `{(a, b)} × …`, so that the membership
and interior checks of `Count4.lean` can be done in slices (`Chunks.lean`).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Count4
import Wills.Proofs.Chunks

namespace Wills.Count4

open Wills.Count (dotL rng)
open Wills.Chunk

/-- The cells' keys `(a, b)`, in lexicographic order. -/
def cells4 (B : List ℕ) (k : ℕ) : List (ℤ × ℤ) :=
  (rng (k * B.getD 0 0)).flatMap fun a => (rng (k * B.getD 1 0)).map fun b => (a, b)

/-- The cell `{(a, b)} × {-k B_2, …, k B_2} × {-k B_3, …, k B_3}`, in lexicographic order. -/
def cell4 (B : List ℕ) (k : ℕ) (ab : ℤ × ℤ) : List (List ℤ) :=
  (rng (k * B.getD 2 0)).flatMap fun c => (rng (k * B.getD 3 0)).map fun d => [ab.1, ab.2, c, d]

/-- The points of one cell that satisfy every facet inequality `⟨u, z⟩ ≤ k b` of `kP`. -/
def cellInF (F : List (List ℤ × ℤ)) (B : List ℕ) (k : ℕ) (ab : ℤ × ℤ) : List (List ℤ) :=
  (cell4 B k ab).filter fun z => F.all fun f => decide (dotL f.1 z ≤ k * f.2)

/-- The points of one cell that satisfy every facet inequality of `kP` strictly. -/
def cellStrictF (F : List (List ℤ × ℤ)) (B : List ℕ) (k : ℕ) (ab : ℤ × ℤ) : List (List ℤ) :=
  (cell4 B k ab).filter fun z => F.all fun f => decide (dotL f.1 z < k * f.2)

lemma box4_eq_cells (B : List ℕ) (k : ℕ) : box4 B k = (cells4 B k).flatMap (cell4 B k) := by
  simp only [box4, cells4, cell4, List.flatMap_assoc, List.flatMap_map]

lemma insideF_eq_cells (F : List (List ℤ × ℤ)) (B : List ℕ) (k : ℕ) :
    insideF F B k = (cells4 B k).flatMap (cellInF F B k) := by
  rw [insideF, box4_eq_cells, List.filter_flatMap]
  rfl

lemma strictF_eq_cells (F : List (List ℤ × ℤ)) (B : List ℕ) (k : ℕ) :
    strictF F B k = (cells4 B k).flatMap (cellStrictF F B k) := by
  rw [strictF, box4_eq_cells, List.filter_flatMap]
  rfl

lemma memAll_eq_zipOk (V : List (List ℤ)) (F : List (List ℤ × ℤ)) (B : List ℕ) (k : ℕ)
    (C : List (List (ℕ × ℕ) × ℕ)) : memAll V F B k C = zipOk (certOk V k) (insideF F B k) C := rfl

lemma intAll_eq_zipOk (V : List (List ℤ)) (F : List (List ℤ × ℤ)) (B : List ℕ) (k d : ℕ)
    (C : List (List (List (ℕ × ℕ) × ℕ))) : intAll V F B k d C = zipOk (intOk V k d) (strictF F B k) C := rfl

end Wills.Count4
