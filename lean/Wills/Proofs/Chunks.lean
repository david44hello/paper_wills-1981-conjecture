/-
Wills/Proofs/Chunks.lean — a certificate check over a list built by `flatMap`, done in slices: each slice is a small
kernel computation, and the slices together give the whole check.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.CountData

namespace Wills.Chunk

variable {α β γ : Type}

/-- `L` and `C` have the same length, and `ok (L[i]) (C[i])` holds for every `i`. -/
def zipOk (ok : β → γ → Bool) (L : List β) (C : List γ) : Bool :=
  L.length == C.length && (L.zip C).all fun q => ok q.1 q.2

/-- A slice `(i, m, o, n)`: the keys `K[i], …, K[i+m-1]`, checked against `C[o], …, C[o+n-1]`. -/
def sliceOk (ok : β → γ → Bool) (g : α → List β) (K : List α) (C : List γ) (s : ℕ × ℕ × ℕ × ℕ) : Bool :=
  zipOk ok (((K.drop s.1).take s.2.1).flatMap g) ((C.drop s.2.2.1).take s.2.2.2)

/-- The slices follow each other from `(i, o)` and end exactly at `(p, n)`. -/
def offsetsOk : List (ℕ × ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ → Bool
  | [], i, o, p, n => i == p && o == n
  | s :: S, i, o, p, n => s.1 == i && s.2.2.1 == o && offsetsOk S (i + s.2.1) (o + s.2.2.2) p n

lemma offsetsOk_le {S : List (ℕ × ℕ × ℕ × ℕ)} {i o p n : ℕ} (h : offsetsOk S i o p n = true) : o ≤ n := by
  induction S generalizing i o with
  | nil =>
    simp only [offsetsOk, Bool.and_eq_true, beq_iff_eq] at h
    omega
  | cons s S ih =>
    simp only [offsetsOk, Bool.and_eq_true, beq_iff_eq] at h
    have := ih h.2
    omega

lemma zipOk_append {ok : β → γ → Bool} {L₁ L₂ : List β} {C : List γ} {n : ℕ} (hn : n ≤ C.length)
    (h₁ : zipOk ok L₁ (C.take n) = true) (h₂ : zipOk ok L₂ (C.drop n) = true) : zipOk ok (L₁ ++ L₂) C = true := by
  simp only [zipOk, Bool.and_eq_true, beq_iff_eq, List.length_take, List.length_drop] at h₁ h₂ ⊢
  have hlen : L₁.length = (C.take n).length := by rw [List.length_take]; omega
  refine ⟨by rw [List.length_append]; omega, ?_⟩
  rw [← List.take_append_drop n C, List.zip_append hlen, List.all_append, h₁.2, h₂.2]
  rfl

/-- The slices, checked one by one, give the check of the rest of the list from `(i, o)`. -/
lemma zipOk_drop_of_slices (ok : β → γ → Bool) (g : α → List β) (K : List α) (C : List γ) :
    ∀ (S : List (ℕ × ℕ × ℕ × ℕ)) (i o : ℕ), offsetsOk S i o K.length C.length = true →
      (∀ s ∈ S, sliceOk ok g K C s = true) → zipOk ok ((K.drop i).flatMap g) (C.drop o) = true
  | [], i, o, h, _ => by
    simp only [offsetsOk, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2, List.drop_length, List.drop_length]
    rfl
  | s :: S, i, o, h, hS => by
    have h' := h
    simp only [offsetsOk, Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨hi, ho⟩, hrest⟩ := h'
    have hs := hS s (List.mem_cons_self ..)
    rw [sliceOk, hi, ho] at hs
    have hle := offsetsOk_le hrest
    have ih := zipOk_drop_of_slices ok g K C S _ _ hrest (fun t ht => hS t (List.mem_cons_of_mem _ ht))
    rw [← List.take_append_drop s.2.1 (K.drop i), List.flatMap_append]
    refine zipOk_append (n := s.2.2.2) (by rw [List.length_drop]; omega) hs ?_
    rw [List.drop_drop, List.drop_drop]
    exact ih

/-- **The slice lemma.** If the slices tile `K` and `C` (checked by `offsetsOk`) and each slice passes, then the
whole check `zipOk ok (K.flatMap g) C` passes. -/
theorem zipOk_of_slices (ok : β → γ → Bool) (g : α → List β) (K : List α) (C : List γ)
    (S : List (ℕ × ℕ × ℕ × ℕ)) (h : offsetsOk S 0 0 K.length C.length = true)
    (hS : ∀ s ∈ S, sliceOk ok g K C s = true) : zipOk ok (K.flatMap g) C = true := by
  simpa using zipOk_drop_of_slices ok g K C S 0 0 h hS

end Wills.Chunk

namespace Wills.Count

open Wills.Chunk

/-! ### The box `{-k,…,k}⁵` as cells `{(a, b)} × {-k,…,k}³` -/

/-- The cells' keys `(a, b)`, in lexicographic order. -/
def cellsL (k : ℕ) : List (ℤ × ℤ) := (rng k).flatMap fun a => (rng k).map fun b => (a, b)

/-- The cell `{(a, b)} × {-k,…,k}³` of the box, in lexicographic order. -/
def cellL (k : ℕ) (ab : ℤ × ℤ) : List (List ℤ) :=
  (rng k).flatMap fun c => (rng k).flatMap fun d => (rng k).map fun e => [ab.1, ab.2, c, d, e]

/-- The points of one cell that satisfy every facet inequality of `kW`. -/
def cellIn (k : ℕ) (ab : ℤ × ℤ) : List (List ℤ) :=
  (cellL k ab).filter fun z => WData.facets.all fun f => decide (dotL f.1 z ≤ k * f.2)

lemma boxL_eq_cells (k : ℕ) : boxL k = (cellsL k).flatMap (cellL k) := by
  simp only [boxL, cellsL, cellL, List.flatMap_assoc, List.flatMap_map]

lemma insideL_eq_cells (k : ℕ) : insideL k = (cellsL k).flatMap (cellIn k) := by
  rw [insideL, boxL_eq_cells, List.filter_flatMap]
  rfl

lemma cert2All_eq_zipOk : cert2All = zipOk cert2Ok (insideL 2) WData.cert2 := rfl

/-! ### The 2W certificates against a given list `P` of the lattice points of `W`

Each slice of the 2W check looks up lattice points of `W`. With `P` an explicit list proved equal to `insideL 1`
once, no slice recomputes `insideL 1`. -/

/-- `cert2Ok` with the lattice points of `W` given as the list `P`. -/
def cert2OkL (P : List (List ℤ)) (z : List ℤ) (ij : ℕ × ℕ) : Bool :=
  decide (ij.1 < P.length) && decide (ij.2 < P.length) &&
    z == List.zipWith (· + ·) (P.getD ij.1 []) (P.getD ij.2 [])

lemma cert2Ok_eq_cert2OkL {P : List (List ℤ)} (hP : insideL 1 = P) : cert2Ok = cert2OkL P := by
  subst hP
  rfl

lemma cert2All_eq_zipOkL {P : List (List ℤ)} (hP : insideL 1 = P) :
    cert2All = zipOk (cert2OkL P) (insideL 2) WData.cert2 := by
  rw [cert2All_eq_zipOk, cert2Ok_eq_cert2OkL hP]

end Wills.Count
