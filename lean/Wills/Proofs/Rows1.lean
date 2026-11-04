/-
Wills/Proofs/Rows1.lean — proofs of the rows of Sections 1-4 and of Theorem 1.3, each with exactly the type of the row
of the same name in Wills/Paper/Statements.lean (the rows state `ℤⁿ` as `Zn n`; the proofs use `Zn n = lat 1`).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Algebra
import Wills.Proofs.Thm13
import Wills.Proofs.Sec2
import Wills.Proofs.CountW2
import Wills.Proofs.CountWInt
import Wills.Proofs.WVertices

open MeasureTheory Pointwise

namespace Wills.Rows1

/-! ### Auxiliary lemmas -/

lemma det_one_ne (n : ℕ) : (1 : Matrix (Fin n) (Fin n) ℝ).det ≠ 0 := by simp

/-- Minkowski's theorem in the form `vol(P) / det Λ ≤ 16` for `P ∈ W^4_Λ`. -/
lemma vol16 (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P) :
    (volume P).toReal / |B.det| ≤ 16 :=
  (Sec2.vol_div_det_le B hB P hP).trans_eq (by norm_num)

/-- From (E3)'s facet data in dimension `n ≥ 1`: `σ ≤ n vol(P) / det Λ` (all lattice distances are `≥ 1`). -/
lemma sigma_le_n {n : ℕ} (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (P : Set (Pt n)) (m : ℕ)
    (relvol : Fin m → ℝ) (b : Fin m → ℤ) (hd : IsFacetData B P m relvol b) :
    ∑ j, relvol j ≤ n * ((volume P).toReal / |B.det|) := by
  obtain ⟨hrel, hb, _, hvol⟩ := hd
  have key : ∑ j, relvol j ≤ ∑ j, (b j : ℝ) * relvol j := by
    apply Finset.sum_le_sum
    intro j _
    have : (1 : ℝ) ≤ (b j : ℝ) := by exact_mod_cast hb j
    nlinarith [hrel j]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hvol, ← mul_assoc, mul_one_div_cancel hn', one_mul]
  exact key

/-! ### Sections 1 and 2 -/

theorem lat_one (n : ℕ) : lat (1 : Matrix (Fin n) (Fin n) ℝ) = Zn n :=
  lat_one' n

theorem g0_eq_one (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (_hB : B.det ≠ 0) (P : Set (Pt n))
    (_hP : IsLatticePolytope (lat B) P) (hint : (interior P).Nonempty) : g (lat B) P 0 = 1 :=
  g0_eq_one_proof n B P hint

theorem conj_in (hE1 : EhrhartLeading) (n : ℕ) (P : Set (Pt n)) (hP : InW (Zn n) P) :
    g (Zn n) P n ≤ (2 : ℝ) ^ n * (Nat.choose n n : ℝ) := by
  rw [← lat_one'] at hP ⊢
  rw [hE1 n 1 (det_one_ne n) P hP.1 (inW_interior_nonempty hP), Nat.choose_self, Nat.cast_one, mul_one]
  exact Sec2.vol_div_det_le 1 (det_one_ne n) P hP

theorem conj_in1 (hE3 : FacetFormula) (n : ℕ) (hn : 1 ≤ n) (P : Set (Pt n))
    (hP : InW (Zn n) P) : g (Zn n) P (n - 1) ≤ (2 : ℝ) ^ (n - 1) * (Nat.choose n (n - 1) : ℝ) := by
  rw [← lat_one'] at hP ⊢
  obtain ⟨m, relvol, b, hd⟩ := hE3 n hn 1 (det_one_ne n) P hP
  have hs := sigma_le_n hn 1 P m relvol b hd
  have hv := Sec2.vol_div_det_le 1 (det_one_ne n) P hP
  have key : (n : ℝ) * ((volume P).toReal / |(1 : Matrix (Fin n) (Fin n) ℝ).det|) ≤ n * 2 ^ n :=
    mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg n)
  have h2 : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h2] at key
  rw [hd.2.2.1, Nat.choose_symm hn, Nat.choose_one_right]
  linarith

theorem conj_le_two (hE1 : EhrhartLeading) (hE3 : FacetFormula) (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ 2) :
    WillsConj n := by
  intro P hP i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [Sec2.conj_i0 n P hP, Sec2.cube_g]
  · rcases eq_or_lt_of_le hi with rfl | hlt
    · exact conj_in hE1 _ P hP
    · have hi' : i = n - 1 := by omega
      subst hi'
      exact conj_in1 hE3 n hn1 P hP

/-! ### Section 3: Proposition 3.1 and Theorem 1.3 -/

theorem prop_3_1 (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (P : Set (Pt 5))
    (hP : InW (Zn 5) P) :
    g (Zn 5) P 1 = (4 * ((G (Zn 5) P : ℝ) + 1) + 24 * (volume P).toReal -
      (1 / 2) * ((latCount (Zn 5) P 2 : ℝ) + (intCount (Zn 5) P 2 : ℝ))) / 6 := by
  rw [← lat_one'] at hP ⊢
  exact prop_3_1_proof hE1 hE2 P hP

theorem w_pts_cube : wPts ⊆ cubePts 5 := Count.w_pts_cube_proof

theorem w_symm : -wPts = wPts := Count.w_symm_proof

theorem w_span : Spans wPts := Count.w_span_proof

theorem thm_1_3_mem : InW (Zn 5) W :=
  Sec2.lem_2_1_sub 5 (by norm_num) (Zn 5) subset_rfl (Sec2.zero_mem_Zn 5) wPts
    (fun _ hx => ⟨(Sec2.cubePts_subset 5 (w_pts_cube hx)).2, (Sec2.cubePts_subset 5 (w_pts_cube hx)).1⟩)
    w_symm w_span

theorem tab2_vertices : wPts.ncard = 50 ∧ Set.extremePoints ℝ W = wPts := Count.tab2_vertices_proof

theorem w_G : G (Zn 5) W = 117 := Count.w_G_proof

theorem w_L2 : latCount (Zn 5) W 2 = 1815 := Count.w_L2_proof

theorem w_int2 : intCount (Zn 5) W 2 = 243 := Count.w_int2_proof

theorem w_A : (1 / 2 : ℝ) * ((latCount (Zn 5) W 2 : ℝ) + (intCount (Zn 5) W 2 : ℝ)) = 1029 := by
  rw [w_L2, w_int2]
  norm_num

theorem w_int2_all : interior ((2 : ℝ) • W) ∩ Zn 5 = cubePts 5 := Count.w_int2_all_proof

/-! The four numbers of `W` with the lattice written `lat 1` (the form of the Ehrhart facts). -/

lemma w_mem_lat1 : InW (lat 1) W := by
  rw [lat_one']
  exact thm_1_3_mem

lemma w_G_lat1 : G (lat 1) W = 117 := by
  rw [lat_one']
  exact w_G

lemma w_L2_lat1 : latCount (lat 1) W 2 = 1815 := by
  rw [lat_one']
  exact w_L2

lemma w_int2_lat1 : intCount (lat 1) W 2 = 243 := by
  rw [lat_one']
  exact w_int2

theorem thm_1_3_poly (hEHR : EhrhartThm) (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hVolW : VolW) :
    ehrhartPoly (Zn 5) W = polyW ∧ ∀ k : ℕ, (latCount (Zn 5) W k : ℝ) = polyW.eval (k : ℝ) := by
  have hp := w_poly_of hE1 hE2 hVolW w_mem_lat1 w_G_lat1 w_L2_lat1 w_int2_lat1
  have hL := hEHR 5 1 (det_one_ne 5) W w_mem_lat1.1 (inW_interior_nonempty w_mem_lat1)
  rw [hp, lat_one'] at hL
  rw [lat_one'] at hp
  exact ⟨hp, hL⟩

theorem thm_1_3_g1 (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hVolW : VolW) :
    g (Zn 5) W 1 = 101 / 10 ∧ (101 / 10 : ℝ) > 10 ∧ g (Zn 5) (cube 5) 1 = 10 := by
  have h := (w_coeffs_of hE1 hE2 hVolW w_mem_lat1 w_G_lat1 w_L2_lat1 w_int2_lat1).2.1
  rw [lat_one'] at h
  refine ⟨h, by norm_num, ?_⟩
  rw [Sec2.cube_g1]
  norm_num

theorem interp_unique (n : ℕ) (p q : Polynomial ℝ) (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : ∀ k ≤ n, p.eval (k : ℝ) = q.eval (k : ℝ)) : p = q :=
  poly_eq_of_nodes p q hp hq h

/-- `L_W(k)` is the value of the polynomial of Theorem 1.3 at `k`. -/
lemma latW_of_eval (hEHR : EhrhartThm) (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hVolW : VolW)
    (k v : ℕ) (hv : polyW.eval (k : ℝ) = v) : latCount (Zn 5) W k = v := by
  have h := (thm_1_3_poly hEHR hE1 hE2 hVolW).2 k
  exact_mod_cast h.trans hv

theorem w_L3456 (hEHR : EhrhartThm) (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hVolW : VolW) :
    latCount (Zn 5) W 0 = 1 ∧ latCount (Zn 5) W 1 = 117 ∧ latCount (Zn 5) W 2 = 1815 ∧
      latCount (Zn 5) W 3 = 10765 ∧ latCount (Zn 5) W 4 = 39927 ∧ latCount (Zn 5) W 5 = 112639 ∧
      latCount (Zn 5) W 6 = 265705 :=
  ⟨latW_of_eval hEHR hE1 hE2 hVolW 0 1 (by rw [polyW_eval]; norm_num),
    latW_of_eval hEHR hE1 hE2 hVolW 1 117 (by rw [polyW_eval]; norm_num),
    latW_of_eval hEHR hE1 hE2 hVolW 2 1815 (by rw [polyW_eval]; norm_num),
    latW_of_eval hEHR hE1 hE2 hVolW 3 10765 (by rw [polyW_eval]; norm_num),
    latW_of_eval hEHR hE1 hE2 hVolW 4 39927 (by rw [polyW_eval]; norm_num),
    latW_of_eval hEHR hE1 hE2 hVolW 5 112639 (by rw [polyW_eval]; norm_num),
    latW_of_eval hEHR hE1 hE2 hVolW 6 265705 (by rw [polyW_eval]; norm_num)⟩

theorem thm_1_3_prod (hEHR : EhrhartThm) (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hVolW : VolW)
    (m : ℕ) (_hm : 1 ≤ m) :
    InW (Zn (5 + m)) (prod W (cube m)) ∧
      g (Zn (5 + m)) (prod W (cube m)) 1 = 101 / 10 + 2 * m ∧
      (101 / 10 + 2 * m : ℝ) = 2 * ((5 + m : ℕ) : ℝ) + 1 / 10 ∧
      2 * ((5 + m : ℕ) : ℝ) + 1 / 10 > 2 * ((5 + m : ℕ) : ℝ) ∧
      g (Zn (5 + m)) (cube (5 + m)) 1 = 2 * ((5 + m : ℕ) : ℝ) := by
  obtain ⟨hmem, hg⟩ := Sec2.lem_2_2 hEHR 5 m W (cube m) thm_1_3_mem (Sec2.cube_mem m)
  refine ⟨hmem, ?_, by push_cast; ring, by linarith, Sec2.cube_g1 (5 + m)⟩
  rw [hg, (thm_1_3_g1 hE1 hE2 hVolW).1, Sec2.cube_g1]

/-! ### Section 4 -/

theorem lem_4_1 (hE2 : EhrhartReciprocity) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4))
    (hP : InW (lat B) P) :
    g (lat B) P 1 + g (lat B) P 3 = ((G (lat B) P : ℝ) - 1) / 2 ∧
      g (lat B) P 2 + g (lat B) P 4 = ((G (lat B) P : ℝ) - 1) / 2 :=
  lem_4_1_proof hE2 B hB P hP

theorem recip_m1_dim4 (hE2 : EhrhartReciprocity) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0)
    (P : Set (Pt 4)) (hP : InW (lat B) P) : (ehrhartPoly (lat B) P).eval (-1) = 1 :=
  recip_m1_dim4_proof hE2 B hB P hP

theorem prop_4_2_g4 (hE1 : EhrhartLeading) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4))
    (hP : InW (lat B) P) : g (lat B) P 4 = (volume P).toReal / |B.det| ∧ g (lat B) P 4 ≤ 16 :=
  prop_4_2_g4_of hE1 B hB P hP (vol16 B hB P hP)

theorem prop_4_2_g3 (hE1 : EhrhartLeading) (hE3 : FacetFormula) (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P) :
    g (lat B) P 3 ≤ 2 * g (lat B) P 4 ∧ 2 * g (lat B) P 4 ≤ 32 :=
  prop_4_2_g3_of hE1 hE3 B hB P hP (vol16 B hB P hP)

theorem prop_4_2_iff (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P) :
    (∃ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b) ∧
      ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b →
        (g (lat B) P 1 ≤ 8 ↔ (G (lat B) P : ℝ) ≤ ∑ j, relvol j + 17) :=
  prop_4_2_iff_proof hE2 hE3 B hB P hP

theorem prop_4_2_g2 (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P)
    (h1 : g (lat B) P 1 ≤ 8) : g (lat B) P 2 ≤ g (lat B) P 4 + 8 ∧ g (lat B) P 4 + 8 ≤ 24 :=
  prop_4_2_g2_of hE1 hE2 hE3 B hB P hP (vol16 B hB P hP) h1

theorem key_equiv (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) :
    (∀ P : Set (Pt 4), InW (Zn 4) P → g (Zn 4) P 1 ≤ 8 ∧ g (Zn 4) P 2 ≤ 24) ↔
      ∀ P : Set (Pt 4), InW (Zn 4) P → ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ),
        IsFacetData 1 P m relvol b → (G (Zn 4) P : ℝ) ≤ ∑ j, relvol j + 17 := by
  rw [← lat_one']
  constructor
  · intro h P hP m relvol b hd
    exact ((prop_4_2_iff_proof hE2 hE3 1 (det_one_ne 4) P hP).2 m relvol b hd).1 (h P hP).1
  · intro h P hP
    obtain ⟨⟨m, relvol, b, hd⟩, hiff⟩ := prop_4_2_iff_proof hE2 hE3 1 (det_one_ne 4) P hP
    have hg1 : g (lat 1) P 1 ≤ 8 := (hiff m relvol b hd).2 (h P hP m relvol b hd)
    obtain ⟨hg2, hg4⟩ := prop_4_2_g2_of hE1 hE2 hE3 1 (det_one_ne 4) P hP (vol16 1 (det_one_ne 4) P hP) hg1
    exact ⟨hg1, hg2.trans hg4⟩

theorem star_iff (hE3 : FacetFormula) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4))
    (hP : InW (lat B) P) :
    (∃ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b) ∧
      ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b →
        ((G (lat B) P : ℝ) ≤ ∑ j, relvol j + 17 ↔ ∑ j, 6 * relvol j ≥ 6 * (G (lat B) P : ℝ) - 102) :=
  star_iff_proof hE3 B hB P hP

theorem lem_4_3_arith (f : Fin 4 → ℕ) (hW : (f 1 : ℤ) ≥ 4 * (f 0 : ℤ) - 10)
    (hDS1 : (f 0 : ℤ) - f 1 + f 2 - f 3 = 0) (hDS2 : 2 * f 2 = 4 * f 3) :
    (f 3 : ℤ) = f 1 - f 0 ∧ (f 3 : ℤ) ≥ 3 * (f 0 : ℤ) - 10 ∧ ∀ Gc : ℤ, Gc ≤ 29 → 3 * Gc - 13 > 6 * Gc - 102 :=
  lem_4_3_arith_proof f hW hDS1 hDS2

theorem lem_4_3 (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) (hTRI : BoundaryTriangulation)
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P)
    (hG : G (lat B) P ≤ 29) :
    ((∃ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b) ∧
      ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b →
        ∑ j, 6 * relvol j > 6 * (G (lat B) P : ℝ) - 102) ∧ g (lat B) P 1 < 8 :=
  lem_4_3_proof hE2 hE3 hTRI B hB P hP hG

theorem rem_4_4_only (Gc : ℤ) : 3 * Gc - 13 > 6 * Gc - 102 ↔ Gc ≤ 29 :=
  rem_4_4_only_proof Gc

end Wills.Rows1
