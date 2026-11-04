/-
Wills/Proofs/Rows7.lean — proofs of the rows of Section 7 (the equality cases `C_4`, `T`, `X`), each with exactly the
type of the row of the same name in Wills/Paper/Statements.lean.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Sec7Counts
import Wills.Proofs.Sec7A
import Wills.Proofs.Sec7B
import Wills.Proofs.Sec7C
import Wills.Proofs.Algebra
import Wills.Proofs.Sec5

open MeasureTheory Pointwise

namespace Wills.Rows7

lemma det_one4 : (1 : Matrix (Fin 4) (Fin 4) ℝ).det ≠ 0 := by simp

/-! ### The Ehrhart polynomial from five values -/

/-- If `P ∈ W⁴` and a polynomial `p` of degree at most 4 takes the values `L(0) = 1`, `L(1) = G`, `L(2)` and (by
reciprocity) `L(-1) = 1`, `L(-2) = #(int(2P) ∩ ℤ⁴)`, then `p` is the Ehrhart polynomial of `P`. -/
lemma ehrhartPoly_eq_of_five (hE2 : EhrhartReciprocity) {P : Set (Pt 4)} (hP : InW (Zn 4) P) {p : Polynomial ℝ}
    (hp : p.natDegree ≤ 4) (h0 : p.eval 0 = 1) (h1 : p.eval 1 = G (Zn 4) P)
    (h2 : p.eval 2 = latCount (Zn 4) P 2) (hm1 : p.eval (-1) = 1) (hm2 : p.eval (-2) = intCount (Zn 4) P 2) :
    ehrhartPoly (Zn 4) P = p := by
  have hP1 : InW (lat 1) P := by
    rw [lat_one']
    exact hP
  have hrec := recip_of_inW hE2 1 det_one4 hP1
  refine S7C.poly_eq_of_five _ p (ehrhartPoly_natDegree_le _ _) hp (fun x hx => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · have h := hrec 2 (by norm_num)
    rw [lat_one'] at h
    rw [hm2, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, h]
    norm_num
  · have h := hrec 1 le_rfl
    rw [lat_one', intCount_one_of_inW hP] at h
    rw [hm1, show (-1 : ℝ) = -((1 : ℕ) : ℝ) by norm_num, h]
    norm_num
  · have h := ehrhartPoly_eval_node (Zn 4) P (k := 0) (by norm_num)
    have hne : P.Nonempty := ⟨0, interior_subset (inW_zero_interior hP)⟩
    rw [latCount_zero (Zn 4) P (Sec2.zero_mem_Zn 4) hne, Nat.cast_zero] at h
    rw [h0, h]
    norm_num
  · have h := ehrhartPoly_eval_node (Zn 4) P (k := 1) (by norm_num)
    rw [latCount_one, Nat.cast_one] at h
    rw [h1, h]
  · have h := ehrhartPoly_eval_node (Zn 4) P (k := 2) (by norm_num)
    rw [h2, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, h]

lemma polyT_eval (x : ℝ) : polyT.eval x = 1 + 8 * x + 8 * x ^ 2 + 16 * x ^ 3 + 16 * x ^ 4 := by
  simp [polyT, polyOf, Finset.sum_range_succ]

lemma polyX_eval (x : ℝ) : polyX.eval x = 1 + 8 * x + 4 * x ^ 2 + 8 * x ^ 3 + 12 * x ^ 4 := by
  simp [polyX, polyOf, Finset.sum_range_succ]

lemma polyT_natDegree : polyT.natDegree ≤ 4 :=
  (S7C.polyOf_natDegree ([1, 8, 8, 16, 16] : List ℝ) 4 rfl (by norm_num)).le

lemma polyX_natDegree : polyX.natDegree ≤ 4 :=
  (S7C.polyOf_natDegree ([1, 8, 4, 8, 12] : List ℝ) 4 rfl (by norm_num)).le

lemma polyT_eq (hE2 : EhrhartReciprocity) : ehrhartPoly (Zn 4) T = polyT :=
  ehrhartPoly_eq_of_five hE2 S7.T_mem_proof polyT_natDegree (by rw [polyT_eval]; norm_num)
    (by rw [polyT_eval, S7.T_G_proof]; norm_num) (by rw [polyT_eval, S7.T_L2_proof]; norm_num)
    (by rw [polyT_eval]; norm_num) (by rw [polyT_eval, S7.T_int2_proof]; norm_num)

lemma polyX_eq (hE2 : EhrhartReciprocity) : ehrhartPoly (Zn 4) X = polyX :=
  ehrhartPoly_eq_of_five hE2 S7.X_mem_proof polyX_natDegree (by rw [polyX_eval]; norm_num)
    (by rw [polyX_eval, S7.X_G_proof]; norm_num) (by rw [polyX_eval, S7.X_L2_proof]; norm_num)
    (by rw [polyX_eval]; norm_num) (by rw [polyX_eval, S7.X_int2_proof]; norm_num)

/-- `L_P(k)` is the value of the Ehrhart polynomial at every `k ≥ 0` (Ehrhart's theorem), for `P ∈ W⁴`. -/
lemma latCount_eval (hEHR : EhrhartThm) {P : Set (Pt 4)} (hP : InW (Zn 4) P) (k : ℕ) :
    (latCount (Zn 4) P k : ℝ) = (ehrhartPoly (Zn 4) P).eval (k : ℝ) := by
  have hP1 : InW (lat 1) P := by
    rw [lat_one']
    exact hP
  have h := hEHR 4 1 det_one4 P hP1.1 (inW_interior_nonempty hP1) k
  rw [lat_one'] at h
  exact h

/-! ### Volume from the leading coefficient -/

lemma polyL_compact (V : List (List ℤ)) : IsCompact (Count4.polyL V) := by
  unfold Count4.polyL
  exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) ((List.finite_toSet V).image _)

/-- (E1) for `P ∈ W⁴`: `vol P = g_4(P)`, as an equality of measures. -/
lemma volume_eq_of_g4 (hE1 : EhrhartLeading) {P : Set (Pt 4)} (hP : InW (Zn 4) P) (hcpt : IsCompact P) {c : ℝ}
    (hg : g (Zn 4) P 4 = c) : volume P = ENNReal.ofReal c := by
  have hP1 : InW (lat 1) P := by
    rw [lat_one']
    exact hP
  have h := hE1 4 1 det_one4 P hP1.1 (inW_interior_nonempty hP1)
  rw [lat_one', hg, Matrix.det_one, abs_one, div_one] at h
  rw [← ENNReal.ofReal_toReal hcpt.measure_lt_top.ne, ← h]

/-! ### The rows -/

theorem T_iso :
    latD4star = lat (Matrix.of ![![1, 0, 0, 1 / 2], ![0, 1, 0, 1 / 2], ![0, 0, 1, 1 / 2], ![0, 0, 0, 1 / 2]]) ∧
      IsoPair T (Zn 4) cell24 latD4star :=
  S7B.T_iso

theorem T_mem : InW (Zn 4) T := S7.T_mem_proof

theorem T_G : G (Zn 4) T = 49 := S7.T_G_proof

theorem D4star_dual : dualLat latD4star = gammaI Finset.univ := S7B.D4star_dual

theorem T_vol (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) : volume T = 16 := by
  have hg : g (Zn 4) T 4 = 16 := by
    unfold g
    rw [polyT_eq hE2, polyT, polyOf_coeff]
    norm_num
  have hcpt : IsCompact T := by
    rw [S7.T_eq]
    exact polyL_compact _
  rw [volume_eq_of_g4 hE1 S7.T_mem_proof hcpt hg]
  norm_num

/-! ### The 24-cell -/

lemma cell24_eq : cell24 = (fun x => S7B.Mh.mulVec x) '' T := by
  unfold cell24 T
  rw [Sec5.image_convexHull_mulVec, S7B.image_tPts]

lemma D4_eq : latD4star = (fun x => S7B.Mh.mulVec x) '' Zn 4 := by
  rw [S7B.lat_Mh]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨ofInt z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

lemma cell24_inW : InW latD4star cell24 := by
  rw [cell24_eq, D4_eq]
  exact Sec5.inW_image S7.T_mem_proof _ S7B.Mh_det

lemma cell24_bound : ∀ x ∈ cell24, (∀ i, |x i| ≤ 1) ∧ ∑ i, |x i| ≤ 2 := by
  have hconv : Convex ℝ {x : Pt 4 | (∀ i, |x i| ≤ 1) ∧ ∑ i, |x i| ≤ 2} := by
    intro a ha b hb s t hs ht hst
    have key : ∀ i, |s * a i + t * b i| ≤ s * |a i| + t * |b i| := fun i =>
      (abs_add_le _ _).trans (le_of_eq (by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]))
    refine ⟨fun i => ?_, ?_⟩
    · show |s * a i + t * b i| ≤ 1
      have h1 : s * |a i| ≤ s * 1 := mul_le_mul_of_nonneg_left (ha.1 i) hs
      have h2 : t * |b i| ≤ t * 1 := mul_le_mul_of_nonneg_left (hb.1 i) ht
      linarith [key i]
    · show ∑ i, |s * a i + t * b i| ≤ 2
      have hsum : ∑ i, |s * a i + t * b i| ≤ s * ∑ i, |a i| + t * ∑ i, |b i| := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => key i
      have h1 : s * ∑ i, |a i| ≤ s * 2 := mul_le_mul_of_nonneg_left ha.2 hs
      have h2 : t * ∑ i, |b i| ≤ t * 2 := mul_le_mul_of_nonneg_left hb.2 ht
      linarith
  have hgen : {x : Pt 4 | ∃ a b : Fin 4, a < b ∧ ∃ s t : ℝ, (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
      x = s • Pi.single a 1 + t • Pi.single b 1} ⊆ {x : Pt 4 | (∀ i, |x i| ≤ 1) ∧ ∑ i, |x i| ≤ 2} := by
    rintro x ⟨a, b, hab, s, t, hs, ht, rfl⟩
    fin_cases a <;> fin_cases b <;> simp at hab <;> rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      refine ⟨fun i => ?_, ?_⟩ <;> (try fin_cases i) <;> simp [Pi.single_apply, Fin.sum_univ_four] <;> norm_num
  intro x hx
  exact convexHull_min hgen hconv hx

theorem cell24_points :
    (∀ x ∈ cell24, (∀ i, |x i| ≤ 1) ∧ ∑ i, |x i| ≤ 2) ∧ (cell24 ∩ latD4star).ncard = 49 ∧
      interior cell24 ∩ latD4star = {0} := by
  refine ⟨cell24_bound, ?_, cell24_inW.2.2⟩
  have h := Sec5.latCount_iso S7B.T_iso.2 1
  rw [latCount_one, latCount_one, S7.T_G_proof] at h
  exact h

lemma Mh_det_eq : S7B.Mh.det = 1 / 2 := by
  simp [S7B.Mh, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

theorem cell24_vol (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) : volume cell24 = 8 := by
  have himg : (fun x => S7B.Mh.mulVec x) '' T = ⇑(Matrix.toLin' S7B.Mh) '' T := by
    ext x
    simp [Matrix.toLin'_apply]
  rw [cell24_eq, himg, MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin', Mh_det_eq,
    T_vol hE1 hE2]
  rw [show (16 : ENNReal) = ENNReal.ofReal 16 by norm_num, ← ENNReal.ofReal_mul (abs_nonneg _),
    show |(1 / 2 : ℝ)| * 16 = 8 by norm_num]
  norm_num

theorem X_mem : InW (Zn 4) X := S7.X_mem_proof

theorem X_G : G (Zn 4) X = 33 := S7.X_G_proof

/-- The four vectors of `X` have determinant 18 (Section 7, l.391). -/
lemma xVec_det : (colMat (fun i => ofInt (xVec i))).det = 18 := by
  simp [colMat, ofInt, xVec, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num

lemma X_eq_crosspoly :
    X = convexHull ℝ (Set.range (fun i => ofInt (xVec i)) ∪ Set.range (fun i => -(ofInt (xVec i)))) := by
  unfold X
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl | rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr rfl⟩

/-- l.391: `vol(X) = (2⁴/4!) · 18 = 12`, by the volume of a cross-polytope. -/
theorem X_vol : (colMat (fun i => ofInt (xVec i))).det = 18 ∧ volume X = 12 := by
  refine ⟨xVec_det, ?_⟩
  rw [X_eq_crosspoly, Sec5.crosspoly_vol, xVec_det, show (2 : ℝ) ^ 4 / 24 * |(18 : ℝ)| = 12 by norm_num]
  norm_num

theorem g3_of_dist (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (P : Set (Pt 4)) (hP : InW (Zn 4) P)
    (l : ℤ) (hl : 1 ≤ l) :
    (∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData 1 P m relvol b → (∀ j, b j = l) →
        g (Zn 4) P 3 = (1 / 2) * ∑ j, relvol j ∧ g (Zn 4) P 3 = 2 * g (Zn 4) P 4 / l) ∧
      g (Zn 4) P 1 = ((G (Zn 4) P : ℝ) - 1) / 2 - g (Zn 4) P 3 ∧
      g (Zn 4) P 2 = ((G (Zn 4) P : ℝ) - 1) / 2 - g (Zn 4) P 4 :=
  S7A.g3_of_dist hE1 hE2 P hP l hl

theorem cube4_G_vol : G (Zn 4) (cube 4) = 81 ∧ volume (cube 4) = 16 := S7A.cube4_G_vol

theorem poly_C4 : ehrhartPoly (Zn 4) (cube 4) = polyC4 ∧
    ∀ k : ℕ, (latCount (Zn 4) (cube 4) k : ℝ) = polyC4.eval (k : ℝ) :=
  S7A.poly_C4

theorem poly_T (hEHR : EhrhartThm) (hE2 : EhrhartReciprocity) : ehrhartPoly (Zn 4) T = polyT ∧
    ∀ k : ℕ, (latCount (Zn 4) T k : ℝ) = polyT.eval (k : ℝ) :=
  ⟨polyT_eq hE2, fun k => by rw [latCount_eval hEHR S7.T_mem_proof k, polyT_eq hE2]⟩

theorem poly_X (hEHR : EhrhartThm) (hE2 : EhrhartReciprocity) : ehrhartPoly (Zn 4) X = polyX ∧
    ∀ k : ℕ, (latCount (Zn 4) X k : ℝ) = polyX.eval (k : ℝ) :=
  ⟨polyX_eq hE2, fun k => by rw [latCount_eval hEHR S7.X_mem_proof k, polyX_eq hE2]⟩

/-- A vertex `p` of `polyL V` bounds an integer functional `z` with `|⟨z, x⟩| ≤ 1` on `polyL V`. -/
lemma dot_bound_of_vert {V : List (List ℤ)} {z : Fin 4 → ℤ} (hu : ∀ x ∈ Count4.polyL V, |ofInt z ⬝ᵥ x| ≤ 1)
    {p : Fin 4 → ℤ} (hp : List.ofFn p ∈ V) : -1 ≤ z ⬝ᵥ p ∧ z ⬝ᵥ p ≤ 1 := by
  have h := hu (ofInt p) (by rw [← Count4.toPt4_ofFn]; exact Count4.mem_polyL_vert hp)
  have hcast : ofInt z ⬝ᵥ ofInt p = ((z ⬝ᵥ p : ℤ) : ℝ) := by
    simp [ofInt, dotProduct]
  rw [hcast] at h
  have h' : |z ⬝ᵥ p| ≤ 1 := by exact_mod_cast h
  exact abs_le.1 h'

lemma MP_eq_zero_of {P : Set (Pt 4)} (h : ∀ z : Fin 4 → ℤ, (∀ x ∈ P, |ofInt z ⬝ᵥ x| ≤ 1) → z = 0) :
    MP P = {0} := by
  ext u
  constructor
  · rintro ⟨⟨z, rfl⟩, hu⟩
    rw [h z hu, Set.mem_singleton_iff]
    funext i
    simp [ofInt]
  · intro hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    refine ⟨⟨0, ?_⟩, fun x _ => by simp⟩
    funext i
    simp [ofInt]

theorem M_T : MP T = {0} := by
  apply MP_eq_zero_of
  intro z hu
  rw [S7.T_eq] at hu
  have h1 := dot_bound_of_vert hu (p := ![1, 1, 0, 0]) (by decide)
  have h2 := dot_bound_of_vert hu (p := ![1, -1, 0, 0]) (by decide)
  have h3 := dot_bound_of_vert hu (p := ![1, 0, 1, 0]) (by decide)
  have h4 := dot_bound_of_vert hu (p := ![1, 0, -1, 0]) (by decide)
  have h5 := dot_bound_of_vert hu (p := ![0, 1, 1, 0]) (by decide)
  have h6 := dot_bound_of_vert hu (p := ![0, 1, -1, 0]) (by decide)
  have h7 := dot_bound_of_vert hu (p := ![0, -1, -1, 2]) (by decide)
  have h8 := dot_bound_of_vert hu (p := ![2, 1, 1, -2]) (by decide)
  have h9 := dot_bound_of_vert hu (p := ![-1, 0, -1, 2]) (by decide)
  have h10 := dot_bound_of_vert hu (p := ![1, 2, 1, -2]) (by decide)
  have h11 := dot_bound_of_vert hu (p := ![-1, -1, 0, 2]) (by decide)
  have h12 := dot_bound_of_vert hu (p := ![1, 1, 2, -2]) (by decide)
  simp [dotProduct, Fin.sum_univ_four] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have key : z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0 ∧ z 3 = 0 := by
    generalize z 0 = a at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    generalize z 1 = b at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    generalize z 2 = c at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    generalize z 3 = d at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    have ha1 : -1 ≤ a := by omega
    have ha2 : a ≤ 1 := by omega
    have hb1 : -1 ≤ b := by omega
    have hb2 : b ≤ 1 := by omega
    have hc1 : -1 ≤ c := by omega
    have hc2 : c ≤ 1 := by omega
    have hd1 : -1 ≤ d := by omega
    have hd2 : d ≤ 1 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> omega
  funext i
  fin_cases i <;> simp [key.1, key.2.1, key.2.2.1, key.2.2.2]

theorem M_X : MP X = {0} := by
  apply MP_eq_zero_of
  intro z hu
  rw [S7.X_eq] at hu
  have h1 := dot_bound_of_vert hu (p := ![1, 0, 0, 0]) (by decide)
  have h2 := dot_bound_of_vert hu (p := ![0, 1, 0, 0]) (by decide)
  have h3 := dot_bound_of_vert hu (p := ![1, 1, 3, 0]) (by decide)
  have h4 := dot_bound_of_vert hu (p := ![2, 4, 3, 6]) (by decide)
  simp [dotProduct, Fin.sum_univ_four] at h1 h2 h3 h4
  have key : z 0 = 0 ∧ z 1 = 0 ∧ z 2 = 0 ∧ z 3 = 0 := by
    generalize z 0 = a at h1 h2 h3 h4
    generalize z 1 = b at h1 h2 h3 h4
    generalize z 2 = c at h1 h2 h3 h4
    generalize z 3 = d at h1 h2 h3 h4
    have ha1 : -1 ≤ a := by omega
    have ha2 : a ≤ 1 := by omega
    have hb1 : -1 ≤ b := by omega
    have hb2 : b ≤ 1 := by omega
    have hc1 : -1 ≤ c := by omega
    have hc2 : c ≤ 1 := by omega
    have hd1 : -2 ≤ d := by omega
    have hd2 : d ≤ 2 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> omega
  funext i
  fin_cases i <;> simp [key.1, key.2.1, key.2.2.1, key.2.2.2]

theorem henze_C4 : HenzeRoots (ehrhartPoly (Zn 4) (cube 4)) := S7A.henze_C4

theorem henze_T_not (hE2 : EhrhartReciprocity) : ¬ HenzeRoots (ehrhartPoly (Zn 4) T) := by
  rw [polyT_eq hE2]
  exact S7C.henze_polyT_not

theorem henze_X_not (hE2 : EhrhartReciprocity) : ¬ HenzeRoots (ehrhartPoly (Zn 4) X) := by
  rw [polyX_eq hE2]
  exact S7C.henze_polyX_not

theorem G_unimod_inv (P P' : Set (Pt 4)) (h : UnimodEquiv P P') : G (Zn 4) P' = G (Zn 4) P :=
  S7B.G_unimod_inv P P' h

end Wills.Rows7
