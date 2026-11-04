/-
Wills/Proofs/Interp.lean — The interpolating polynomial `ehrhartPoly`: values at the nodes, degree, uniqueness,
`g_0 = 1`.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Defs.Basic

open MeasureTheory Polynomial Pointwise

namespace Wills

lemma nat_cast_injOn (n : ℕ) : Set.InjOn (fun k : ℕ => (k : ℝ)) (Finset.range (n + 1) : Set ℕ) := by
  intro a _ b _ h
  exact Nat.cast_injective h

/-- At a node `k ≤ n` the Ehrhart polynomial takes the value `L(k)`. -/
lemma ehrhartPoly_eval_node {n : ℕ} (Λ P : Set (Pt n)) {k : ℕ} (hk : k ≤ n) :
    (ehrhartPoly Λ P).eval (k : ℝ) = (latCount Λ P k : ℝ) := by
  unfold ehrhartPoly
  exact Lagrange.eval_interpolate_at_node _ (nat_cast_injOn n) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

lemma ehrhartPoly_degree_lt {n : ℕ} (Λ P : Set (Pt n)) : (ehrhartPoly Λ P).degree < (n + 1 : ℕ) := by
  unfold ehrhartPoly
  have := Lagrange.degree_interpolate_lt (r := fun k => (latCount Λ P k : ℝ)) (nat_cast_injOn n)
  simpa using this

lemma ehrhartPoly_natDegree_le {n : ℕ} (Λ P : Set (Pt n)) : (ehrhartPoly Λ P).natDegree ≤ n := by
  have h := ehrhartPoly_degree_lt Λ P
  by_cases h0 : ehrhartPoly Λ P = 0
  · simp [h0]
  · rw [Polynomial.degree_eq_natDegree h0] at h
    exact Nat.lt_succ_iff.1 (by exact_mod_cast h)

/-- Two real polynomials of degree at most `n` that agree at `0, 1, …, n` are equal. -/
lemma poly_eq_of_nodes {n : ℕ} (p q : ℝ[X]) (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : ∀ k ≤ n, p.eval (k : ℝ) = q.eval (k : ℝ)) : p = q := by
  classical
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq
    ((Finset.range (n + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_
  · rw [Finset.card_image_of_injOn (nat_cast_injOn n), Finset.card_range]
    calc (p - q).degree ≤ max p.degree q.degree := Polynomial.degree_sub_le p q
      _ < (n + 1 : ℕ) := by
        apply max_lt
        · exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_of_le hp)
        · exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_of_le hq)
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    exact h k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

/-- A polynomial of degree at most `n` through the values `L(0), …, L(n)` is the Ehrhart polynomial. -/
lemma ehrhartPoly_eq_of {n : ℕ} (Λ P : Set (Pt n)) (p : ℝ[X]) (hp : p.natDegree ≤ n)
    (h : ∀ k ≤ n, p.eval (k : ℝ) = (latCount Λ P k : ℝ)) : ehrhartPoly Λ P = p :=
  poly_eq_of_nodes _ _ (ehrhartPoly_natDegree_le Λ P) hp
    (fun k hk => by rw [ehrhartPoly_eval_node Λ P hk, h k hk])

/-- The value of a polynomial of degree at most `n` as the sum `Σ_{i ≤ n} c_i x^i`. -/
lemma eval_eq_sum_coeff {n : ℕ} (p : ℝ[X]) (hp : p.natDegree ≤ n) (x : ℝ) :
    p.eval x = ∑ i ∈ Finset.range (n + 1), p.coeff i * x ^ i :=
  Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp) x

/-- The Ehrhart polynomial in terms of the coefficients `g_i`. -/
lemma ehrhartPoly_eval_eq_sum {n : ℕ} (Λ P : Set (Pt n)) (x : ℝ) :
    (ehrhartPoly Λ P).eval x = ∑ i ∈ Finset.range (n + 1), g Λ P i * x ^ i :=
  eval_eq_sum_coeff _ (ehrhartPoly_natDegree_le Λ P) x

/-- `L(1) = G(P)`. -/
lemma latCount_one {n : ℕ} (Λ P : Set (Pt n)) : latCount Λ P 1 = G Λ P := by
  simp [latCount, G]

/-- `ℤⁿ = 1 · ℤⁿ`. -/
lemma lat_one' (n : ℕ) : lat (1 : Matrix (Fin n) (Fin n) ℝ) = Zn n := by
  ext x
  simp [lat, Zn]

/-- `0 ∈ B ℤⁿ`. -/
lemma ofInt_zero {n : ℕ} : ofInt (0 : Fin n → ℤ) = 0 := funext fun i => by simp [ofInt]

lemma zero_mem_lat {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : (0 : Pt n) ∈ lat B :=
  ⟨0, by show B.mulVec (ofInt 0) = 0; rw [ofInt_zero]; exact Matrix.mulVec_zero B⟩

/-- `L(0) = 1` for a nonempty `P` and a lattice containing `0`. -/
lemma latCount_zero {n : ℕ} (Λ P : Set (Pt n)) (h0 : (0 : Pt n) ∈ Λ) (hP : P.Nonempty) :
    latCount Λ P 0 = 1 := by
  unfold latCount
  rw [Nat.cast_zero, Set.zero_smul_set hP, ← Set.singleton_zero]
  rw [show ({0} : Set (Pt n)) ∩ Λ = {0} from Set.inter_eq_left.2 (Set.singleton_subset_iff.2 h0)]
  exact Set.ncard_singleton 0

/-- `g_0 = L(0)`. -/
lemma g_zero_eq {n : ℕ} (Λ P : Set (Pt n)) : g Λ P 0 = (latCount Λ P 0 : ℝ) := by
  unfold g
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have := ehrhartPoly_eval_node Λ P (Nat.zero_le n)
  simpa using this

lemma g0_eq_one_proof (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (P : Set (Pt n))
    (hint : (interior P).Nonempty) : g (lat B) P 0 = 1 := by
  rw [g_zero_eq, latCount_zero _ _ (zero_mem_lat B) (hint.mono interior_subset)]
  simp

end Wills
