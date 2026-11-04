/-
Wills/Proofs/Sec7C.lean — Section 7 pure polynomial facts: polyT and polyX fail Henze's root condition; a degree-≤4
polynomial is determined by its values at -2, -1, 0, 1, 2.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import Wills.Defs.Basic
import Wills.Defs.Examples
import Wills.Proofs.Thm13

open MeasureTheory Pointwise

namespace Wills.S7C

/-- `polyOf c` has natural degree `n` when `c` has length `n + 1` and a nonzero last entry. -/
lemma polyOf_natDegree (c : List ℝ) (n : ℕ) (hc : c.length = n + 1) (hlast : c.getD n 0 ≠ 0) :
    (polyOf c).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [polyOf_coeff, List.getD_eq_default _ _ (by rw [hc]; exact_mod_cast Nat.succ_le_of_lt hi)]
  · rwa [polyOf_coeff]

/-- Real part of a multiset sum of complex numbers. -/
lemma re_multiset_sum (s : Multiset ℂ) : s.sum.re = (s.map Complex.re).sum :=
  map_multiset_sum Complex.reAddGroupHom s

/-- Vieta for a quartic: if every complex root has real part `-1/2`, then `coeff 3 = 2 * coeff 4`. -/
lemma coeff3_of_henze (p : Polynomial ℝ) (hdeg : p.natDegree = 4) (hH : HenzeRoots p) :
    p.coeff 3 = 2 * p.coeff 4 := by
  have hqdeg : (p.map (algebraMap ℝ ℂ)).natDegree = 4 := by rw [Polynomial.natDegree_map, hdeg]
  have hcard : (p.map (algebraMap ℝ ℂ)).roots.card = 4 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hqdeg]
  have hvieta := (IsAlgClosed.splits (p.map (algebraMap ℝ ℂ))).nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [Polynomial.nextCoeff_of_natDegree_pos (by omega), Polynomial.leadingCoeff, hqdeg,
    Polynomial.coeff_map, Polynomial.coeff_map] at hvieta
  have hsum : ((p.map (algebraMap ℝ ℂ)).roots.sum).re = -2 := by
    rw [re_multiset_sum, Multiset.map_congr rfl (g := fun _ => (-1 / 2 : ℝ)) hH, Multiset.map_const',
      Multiset.sum_replicate, hcard]
    norm_num
  have hre : p.coeff 3 = -p.coeff 4 * -2 := by
    have h := congrArg Complex.re hvieta
    rw [← map_neg, Complex.coe_algebraMap, Complex.ofReal_re, Complex.re_ofReal_mul, hsum] at h
    simpa using h
  linarith

/-- Section 7: `L_T = 1 + 8k + 8k² + 16k³ + 16k⁴` fails Henze's root condition (root sum `-1`, not `-2`). -/
theorem henze_polyT_not : ¬ HenzeRoots polyT := by
  intro hH
  have h := coeff3_of_henze polyT (polyOf_natDegree ([1, 8, 8, 16, 16] : List ℝ) 4 rfl (by norm_num)) hH
  rw [polyT, polyOf_coeff, polyOf_coeff] at h
  norm_num at h

/-- Section 7: `L_X = 1 + 8k + 4k² + 8k³ + 12k⁴` fails Henze's root condition (root sum `-2/3`, not `-2`). -/
theorem henze_polyX_not : ¬ HenzeRoots polyX := by
  intro hH
  have h := coeff3_of_henze polyX (polyOf_natDegree ([1, 8, 4, 8, 12] : List ℝ) 4 rfl (by norm_num)) hH
  rw [polyX, polyOf_coeff, polyOf_coeff] at h
  norm_num at h

/-- Two real polynomials of degree at most 4 that agree at `-2, -1, 0, 1, 2` are equal. -/
theorem poly_eq_of_five (p q : Polynomial ℝ) (hp : p.natDegree ≤ 4) (hq : q.natDegree ≤ 4)
    (h : ∀ x ∈ ({-2, -1, 0, 1, 2} : Finset ℝ), p.eval x = q.eval x) : p = q := by
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ ?_ h
  have hcard : ({-2, -1, 0, 1, 2} : Finset ℝ).card = 5 := by
    rw [Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num),
      Finset.card_insert_of_notMem (by norm_num), Finset.card_insert_of_notMem (by norm_num),
      Finset.card_singleton]
  rw [hcard]
  have hd : (p - q).natDegree ≤ 4 := (Polynomial.natDegree_sub_le p q).trans (max_le hp hq)
  exact (Polynomial.degree_le_of_natDegree_le hd).trans_lt (WithBot.coe_lt_coe.mpr (by norm_num))

end Wills.S7C
