/-
Wills/Proofs/Sec2.lean — proofs for Section 2 of "Wills' (1981) conjecture holds if and only if the dimension is at most 4": the cube, its corners,
its lattice-point counts and Ehrhart coefficients, Minkowski's first theorem, Lemmas 2.1 and 2.2.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Defs.Basic
import Wills.Defs.Cases
import Wills.Facts.Basic
import Wills.Proofs.Interp

open MeasureTheory Pointwise Polynomial

namespace Wills.Sec2

/-! ### The cube `C_n = [-1,1]ⁿ` -/

lemma cube_eq_pi (n : ℕ) : cube n = Set.pi Set.univ (fun _ : Fin n => Set.Icc (-1 : ℝ) 1) := by
  ext x; rw [Set.mem_univ_pi]; exact forall_congr' fun i => abs_le

lemma cube_convex (n : ℕ) : Convex ℝ (cube n) := by
  rw [cube_eq_pi]; exact convex_pi (fun _ _ => convex_Icc _ _)

lemma cube_compact (n : ℕ) : IsCompact (cube n) := by
  rw [cube_eq_pi]; exact isCompact_univ_pi (fun _ => isCompact_Icc)

lemma zero_mem_cube (n : ℕ) : (0 : Pt n) ∈ cube n := by
  intro i; simp

lemma neg_cube (n : ℕ) : -cube n = cube n := by
  ext x; simp [cube]

lemma interior_cube (n : ℕ) : interior (cube n) = {x : Pt n | ∀ i, |x i| < 1} := by
  rw [cube_eq_pi, interior_pi_set Set.finite_univ]
  ext x; simp [abs_lt]

/-- The corners `{±1}ⁿ` of the cube. -/
def corners (n : ℕ) : Set (Pt n) := {x | ∀ i, x i = 1 ∨ x i = -1}

lemma corners_finite (n : ℕ) : (corners n).Finite := by
  have : corners n = Set.pi Set.univ (fun _ : Fin n => ({1, -1} : Set ℝ)) := by
    ext x; simp [corners]
  rw [this]; exact Set.Finite.pi (fun _ => Set.toFinite _)

lemma corners_subset_cube (n : ℕ) : corners n ⊆ cube n := by
  intro x hx i; rcases hx i with h | h <;> simp [h]

/-- An extreme point of the cube is a corner: if `|x_i| < 1`, then `x` is the midpoint of `x ± ε e_i`. -/
lemma extremePoints_cube_subset (n : ℕ) : Set.extremePoints ℝ (cube n) ⊆ corners n := by
  intro x hx i
  rw [mem_extremePoints] at hx
  obtain ⟨hxc, hext⟩ := hx
  by_contra hne
  push_neg at hne
  have hlt : |x i| < 1 := by
    obtain ⟨h1, h2⟩ := abs_le.1 (hxc i)
    rw [abs_lt]
    exact ⟨lt_of_le_of_ne h1 (fun e => hne.2 e.symm), lt_of_le_of_ne h2 hne.1⟩
  set ε := 1 - |x i| with hε
  have hεpos : 0 < ε := by linarith
  set e : Pt n := Pi.single i (1 : ℝ) with he
  have hmem : ∀ c : ℝ, |c| ≤ ε → x + c • e ∈ cube n := by
    intro c hc j
    by_cases hj : j = i
    · subst hj
      simp only [he, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (x j), le_abs_self (x j), neg_abs_le c, le_abs_self c]
    · simp only [he, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_eq_mul, mul_zero, add_zero]
      exact hxc j
  have hy := hmem ε (by rw [abs_of_pos hεpos])
  have hz := hmem (-ε) (by rw [abs_neg, abs_of_pos hεpos])
  have hseg : x ∈ openSegment ℝ (x + ε • e) (x + (-ε) • e) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
      ext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩
  have h1 := (hext _ hy _ hz hseg).1
  have : (x + ε • e) i = x i := by rw [h1]
  simp only [he, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at this
  linarith

/-- The cube is the convex hull of its corners (Krein-Milman: the cube is compact and convex, its extreme points
are corners, and the convex hull of the finitely many corners is closed). -/
theorem cube_eq_convexHull_corners (n : ℕ) :
    cube n = convexHull ℝ {x : Pt n | ∀ i, x i = 1 ∨ x i = -1} := by
  change cube n = convexHull ℝ (corners n)
  apply le_antisymm
  · have hclosed : IsClosed (convexHull ℝ (corners n)) := ((corners_finite n).isCompact_convexHull ℝ).isClosed
    calc cube n = closure (convexHull ℝ (Set.extremePoints ℝ (cube n))) :=
          (closure_convexHull_extremePoints (cube_compact n) (cube_convex n)).symm
      _ ⊆ closure (convexHull ℝ (corners n)) :=
          closure_mono (convexHull_mono (extremePoints_cube_subset n))
      _ = convexHull ℝ (corners n) := hclosed.closure_eq
  · exact convexHull_min (corners_subset_cube n) (cube_convex n)

lemma ofInt_injective {n : ℕ} : Function.Injective (@ofInt n) := by
  intro a b h; funext i
  have := congrFun h i
  simp only [ofInt] at this
  exact_mod_cast this

lemma corners_subset_Zn (n : ℕ) : corners n ⊆ Zn n := by
  intro x hx
  refine ⟨fun i => if x i = 1 then 1 else -1, ?_⟩
  funext i
  simp only [ofInt]
  rcases hx i with h | h
  · simp [h]
  · norm_num [h]

/-- An integer point with all coordinates of absolute value `< 1` is `0`. -/
lemma Zn_abs_lt_one {n : ℕ} {x : Pt n} (hx : x ∈ Zn n) (h : ∀ i, |x i| < 1) : x = 0 := by
  obtain ⟨z, rfl⟩ := hx
  funext i
  have := h i
  simp only [ofInt, Pi.zero_apply] at this ⊢
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at this
  simp [this]

lemma zero_mem_Zn (n : ℕ) : (0 : Pt n) ∈ Zn n := ⟨0, ofInt_zero⟩

/-- The integer points of the open cube `(-1,1)ⁿ`: only `0`. -/
lemma interior_cube_inter_Zn (n : ℕ) : interior (cube n) ∩ Zn n = {0} := by
  rw [interior_cube]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, hx⟩; exact Zn_abs_lt_one hx h
  · rintro rfl; exact ⟨fun i => by simp, zero_mem_Zn n⟩

/-- l.58: the cube `C_n` belongs to `Wⁿ`. -/
theorem cube_mem (n : ℕ) : InW (Zn n) (cube n) := by
  refine ⟨⟨(corners_finite n).toFinset, ?_, ?_⟩, neg_cube n, interior_cube_inter_Zn n⟩
  · rw [Set.Finite.coe_toFinset]; exact corners_subset_Zn n
  · rw [Set.Finite.coe_toFinset]; exact cube_eq_convexHull_corners n

/-- l.58: the volume of the cube `C_n` is `2ⁿ`. -/
theorem cube_vol (n : ℕ) : volume (cube n) = 2 ^ n := by
  rw [cube_eq_pi, volume_pi_pi, Real.volume_Icc]
  norm_num

/-! ### Lattice-point counts and Ehrhart coefficients of the cube -/

lemma smul_cube {n : ℕ} {c : ℝ} (hc : 0 ≤ c) : c • cube n = {x : Pt n | ∀ i, |x i| ≤ c} := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [Set.zero_smul_set ⟨0, zero_mem_cube n⟩]
    ext x
    simp only [Set.mem_zero, Set.mem_ofPred_eq]
    constructor
    · rintro rfl i; simp
    · intro h; funext i; exact abs_nonpos_iff.1 (h i)
  · ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
    simp only [cube, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hc]
    refine forall_congr' fun i => ?_
    rw [inv_mul_le_iff₀ hc, mul_one]

/-- l.58: `L_{C_n}(k) = (2k+1)ⁿ`. -/
theorem cube_count (n k : ℕ) : latCount (Zn n) (cube n) k = (2 * k + 1) ^ n := by
  unfold latCount
  rw [smul_cube (Nat.cast_nonneg k)]
  have hset : {x : Pt n | ∀ i, |x i| ≤ (k : ℝ)} ∩ Zn n =
      ofInt '' (↑(Fintype.piFinset fun _ : Fin n => Finset.Icc (-(k : ℤ)) k) : Set (Fin n → ℤ)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Zn, Set.mem_range, Set.mem_image, Finset.mem_coe,
      Fintype.mem_piFinset, Finset.mem_Icc]
    constructor
    · rintro ⟨hx, z, rfl⟩
      refine ⟨z, fun i => ?_, rfl⟩
      have := hx i
      simp only [ofInt] at this
      rw [← Int.cast_abs, ← Int.cast_natCast, Int.cast_le] at this
      exact abs_le.1 this
    · rintro ⟨z, hz, rfl⟩
      refine ⟨fun i => ?_, z, rfl⟩
      simp only [ofInt]
      rw [← Int.cast_abs, ← Int.cast_natCast, Int.cast_le]
      exact abs_le.2 (hz i)
  rw [hset, Set.ncard_image_of_injective _ ofInt_injective, Set.ncard_coe_finset, Fintype.card_piFinset,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
  congr 1
  omega

/-- The Ehrhart polynomial (interpolant) of the cube is `(2X+1)ⁿ`. -/
lemma ehrhartPoly_cube (n : ℕ) : ehrhartPoly (Zn n) (cube n) = (C 2 * Polynomial.X + 1) ^ n := by
  apply ehrhartPoly_eq_of
  · calc ((C 2 * Polynomial.X + 1 : ℝ[X]) ^ n).natDegree ≤ n * (C 2 * Polynomial.X + 1 : ℝ[X]).natDegree := natDegree_pow_le
      _ ≤ n * 1 := by gcongr; compute_degree
      _ = n := mul_one n
  · intro k _
    rw [cube_count]
    simp

/-- l.58: `g_i(C_n) = 2^i binom(n,i)`. -/
theorem cube_g (n i : ℕ) : g (Zn n) (cube n) i = (2 : ℝ) ^ i * (Nat.choose n i : ℝ) := by
  unfold g
  rw [ehrhartPoly_cube]
  have hfac : (C 2 * Polynomial.X + 1 : ℝ[X]) = C 2 * (Polynomial.X + C (1 / 2)) := by
    rw [mul_add, ← C_mul]; norm_num
  rw [hfac, mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow]
  rcases le_or_gt i n with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left, pow_add]
    have h2 : (2 : ℝ) ^ d * (1 / 2) ^ d = 1 := by rw [← mul_pow]; norm_num
    linear_combination (2 ^ i * ((i + d).choose i : ℝ)) * h2
  · rw [Nat.choose_eq_zero_of_lt h]; simp

/-- l.222: `g_1(C_m) = 2m`. -/
theorem cube_g1 (m : ℕ) : g (Zn m) (cube m) 1 = 2 * m := by
  rw [cube_g]; simp

/-- l.67: for `i = 0` there is equality: `g_0(P) = g_0(C_n) = 1` for `P ∈ Wⁿ`. -/
theorem conj_i0 (n : ℕ) (P : Set (Pt n)) (hP : InW (Zn n) P) : g (Zn n) P 0 = g (Zn n) (cube n) 0 := by
  have h0P : (0 : Pt n) ∈ P := by
    have : (0 : Pt n) ∈ interior P ∩ Zn n := by rw [hP.2.2]; rfl
    exact interior_subset this.1
  rw [g_zero_eq, g_zero_eq, latCount_zero _ _ (zero_mem_Zn n) ⟨0, h0P⟩,
    latCount_zero _ _ (zero_mem_Zn n) ⟨0, zero_mem_cube n⟩]

/-! ### Finiteness of lattice points, and the linear map of a lattice basis -/

/-- The integer points of a bounded set are finitely many. -/
lemma Zn_inter_finite {n : ℕ} {S : Set (Pt n)} (hS : Bornology.IsBounded S) : (S ∩ Zn n).Finite := by
  obtain ⟨R, hR⟩ := hS.subset_closedBall 0
  refine ((Finset.finite_toSet (Fintype.piFinset fun _ : Fin n => Finset.Icc (-⌈R⌉) ⌈R⌉)).image ofInt).subset ?_
  rintro x ⟨hxS, z, rfl⟩
  refine ⟨z, ?_, rfl⟩
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  have h1 : ‖ofInt z‖ ≤ R := mem_closedBall_zero_iff.1 (hR hxS)
  have h2 : |(z i : ℝ)| ≤ R := by
    simpa [ofInt, Real.norm_eq_abs] using (norm_le_pi_norm (ofInt z) i).trans h1
  have h3 : ((|z i| : ℤ) : ℝ) ≤ (⌈R⌉ : ℝ) := by rw [Int.cast_abs]; exact h2.trans (Int.le_ceil R)
  have h4 : |z i| ≤ ⌈R⌉ := by exact_mod_cast h3
  rw [Finset.mem_Icc]; exact abs_le.1 h4

/-- `x ↦ B x` as a continuous linear equivalence (for `det B ≠ 0`). -/
noncomputable def linEquiv {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) : Pt n ≃L[ℝ] Pt n :=
  (LinearMap.equivOfDetNeZero (Matrix.toLin' B) (by rw [LinearMap.det_toLin']; exact hB)).toContinuousLinearEquiv

lemma linEquiv_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (x : Pt n) :
    linEquiv B hB x = B.mulVec x := by
  simp [linEquiv, Matrix.toLin'_apply]

lemma linEquiv_det {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) :
    LinearMap.det ((linEquiv B hB).toLinearEquiv.toLinearMap) = B.det := by
  have : (linEquiv B hB).toLinearEquiv.toLinearMap = Matrix.toLin' B := by
    ext x; simp [linEquiv_apply]
  rw [this, LinearMap.det_toLin']

/-- The points of `lat B` in a compact set are finitely many. -/
lemma lat_inter_finite {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) {S : Set (Pt n)}
    (hS : IsCompact S) : (S ∩ lat B).Finite := by
  set e := linEquiv B hB
  have hfin : ((e.symm '' S) ∩ Zn n).Finite := Zn_inter_finite (hS.image e.symm.continuous).isBounded
  refine (hfin.image e).subset ?_
  rintro x ⟨hxS, z, rfl⟩
  refine ⟨ofInt z, ⟨⟨B.mulVec (ofInt z), hxS, ?_⟩, z, rfl⟩, ?_⟩
  · rw [← linEquiv_apply B hB]; exact e.symm_apply_apply _
  · exact linEquiv_apply B hB _

/-! ### Minkowski's first theorem (l.58) -/

/-- The volume of a convex set is the volume of its interior (its frontier has measure zero). -/
lemma volume_le_interior {n : ℕ} {K : Set (Pt n)} (hconv : Convex ℝ K) : volume K ≤ volume (interior K) :=
  calc volume K ≤ volume (closure K) := measure_mono subset_closure
    _ = volume (interior K ∪ frontier K) := by rw [closure_eq_interior_union_frontier]
    _ ≤ volume (interior K) + volume (frontier K) := measure_union_le _ _
    _ = volume (interior K) := by rw [hconv.addHaar_frontier volume, add_zero]

/-- l.58: Minkowski's first theorem — a convex body `K` symmetric about the origin with no lattice point other than
`0` in its interior has volume at most `2ⁿ`. -/
theorem minkowski_first (n : ℕ) (K : Set (Pt n)) (hconv : Convex ℝ K) (hcpt : IsCompact K)
    (hsymm : ∀ x ∈ K, -x ∈ K) (hlat : interior K ∩ Zn n ⊆ {0}) : volume K ≤ 2 ^ n := by
  by_contra hlt
  push_neg at hlt
  set b := Pi.basisFun ℝ (Fin n)
  have h_fund := ZSpan.isAddFundamentalDomain b volume
  have : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range b))
    infer_instance
  have hF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi_pi]; simp
  have hsymmI : ∀ x ∈ interior K, -x ∈ interior K := by
    intro x hx
    have hK2 : (Homeomorph.neg (Pt n)) '' K = K := by
      ext y; simp only [Set.mem_image]
      constructor
      · rintro ⟨w, hw, rfl⟩; exact hsymm w hw
      · intro hy; exact ⟨-y, hsymm y hy, neg_neg y⟩
    have : -x ∈ (Homeomorph.neg (Pt n)) '' interior K := ⟨x, hx, rfl⟩
    rw [(Homeomorph.neg (Pt n)).image_interior K, hK2] at this
    exact this
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (Submodule.span ℤ (Set.range b)).toAddSubgroup) h_fund hsymmI hconv.interior
    (by rw [hF, one_mul, Module.finrank_fin_fun]; exact hlt.trans_le (volume_le_interior hconv))
  rw [Submodule.mem_toAddSubgroup] at hx
  have hrep := (b.mem_span_iff_repr_mem ℤ x).mp hx
  choose z hz using hrep
  have hxZ : x ∈ Zn n := ⟨z, by funext i; simpa [ofInt, b] using hz i⟩
  have hx0 : x = 0 := hlat ⟨h_mem, hxZ⟩
  exact h_nz (by simpa using hx0)

/-- Minkowski's theorem in the coordinates of a basis of `Λ = B ℤⁿ` (used in Proposition 4.2, l.248): a convex body
`K` symmetric about `0` with no point of `Λ` other than `0` in its interior has volume at most `2ⁿ det Λ`. -/
theorem minkowski_lat (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (K : Set (Pt n))
    (hconv : Convex ℝ K) (hcpt : IsCompact K) (hsymm : ∀ x ∈ K, -x ∈ K) (hlat : interior K ∩ lat B ⊆ {0}) :
    volume K ≤ 2 ^ n * ENNReal.ofReal |B.det| := by
  set e := linEquiv B hB
  set K' := e.symm '' K with hK'
  have hK : K = e '' K' := by rw [hK', Set.image_image]; simp
  have hconv' : Convex ℝ K' := hconv.linear_image e.symm.toLinearEquiv.toLinearMap
  have hcpt' : IsCompact K' := hcpt.image e.symm.continuous
  have hsymm' : ∀ x ∈ K', -x ∈ K' := by
    rintro _ ⟨y, hy, rfl⟩; exact ⟨-y, hsymm y hy, map_neg e.symm y⟩
  have hint : interior K' = e.symm '' interior K := (e.symm.toHomeomorph.image_interior K).symm
  have hlat' : interior K' ∩ Zn n ⊆ {0} := by
    rintro x ⟨hxi, z, rfl⟩
    rw [hint] at hxi
    obtain ⟨y, hy, hyx⟩ := hxi
    have hyl : y ∈ lat B := ⟨z, by
      show B.mulVec (ofInt z) = y
      rw [← linEquiv_apply B hB, ← hyx]; exact e.apply_symm_apply y⟩
    have hy0 : y = 0 := hlat ⟨hy, hyl⟩
    rw [← hyx, hy0, map_zero]; rfl
  have h1 := minkowski_first n K' hconv' hcpt' hsymm' hlat'
  have h2 : volume K = ENNReal.ofReal |B.det| * volume K' := by
    rw [hK]
    have := MeasureTheory.Measure.addHaar_image_linearMap volume e.toLinearEquiv.toLinearMap K'
    rw [linEquiv_det] at this
    exact this
  calc volume K = ENNReal.ofReal |B.det| * volume K' := h2
    _ ≤ ENNReal.ofReal |B.det| * 2 ^ n := by gcongr
    _ = 2 ^ n * ENNReal.ofReal |B.det| := mul_comm _ _

/-- A lattice polytope is compact and convex. -/
lemma latticePolytope_compact_convex {n : ℕ} {Λ P : Set (Pt n)} (hP : IsLatticePolytope Λ P) :
    IsCompact P ∧ Convex ℝ P := by
  obtain ⟨V, _, rfl⟩ := hP
  exact ⟨(V.finite_toSet).isCompact_convexHull ℝ, convex_convexHull ℝ _⟩

/-- For `P ∈ W^n_Λ`, `Λ = B ℤⁿ`: `vol(P) / det Λ ≤ 2ⁿ` (Minkowski in the coordinates of a basis of `Λ`, l.248). -/
theorem vol_div_det_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (P : Set (Pt n))
    (hP : InW (lat B) P) : (volume P).toReal / |B.det| ≤ 2 ^ n := by
  obtain ⟨hcpt, hconv⟩ := latticePolytope_compact_convex hP.1
  have hsymm : ∀ x ∈ P, -x ∈ P := fun x hx => by rw [← hP.2.1]; simpa using hx
  have hle := minkowski_lat n B hB P hconv hcpt hsymm (by rw [hP.2.2])
  have hdet : 0 < |B.det| := abs_pos.2 hB
  rw [div_le_iff₀ hdet]
  have := ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) hle
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hdet.le] using this

/-! ### Section 2: dimension, parity of `G` -/

/-- l.170: a polytope in `W^n_Λ` has dimension `n`, because `0` is an interior point. -/
theorem inW_full_dim (n : ℕ) (Λ P : Set (Pt n)) (hP : InW Λ P) :
    (0 : Pt n) ∈ interior P ∧ affineSpan ℝ P = ⊤ := by
  have h0 : (0 : Pt n) ∈ interior P := by
    have : (0 : Pt n) ∈ interior P ∩ Λ := by rw [hP.2.2]; rfl
    exact this.1
  exact ⟨h0, affineSpan_eq_top_of_nonempty_interior ⟨0, interior_mono (subset_convexHull ℝ P) h0⟩⟩

/-- A finite symmetric set that contains `0` has an odd number of points (`x ↦ -x` is an involution whose only
fixed point is `0`). -/
lemma odd_ncard_symm {n : ℕ} (A : Set (Pt n)) (hfin : A.Finite) (hsymm : ∀ x ∈ A, -x ∈ A)
    (h0 : (0 : Pt n) ∈ A) : Odd A.ncard := by
  classical
  haveI : Fintype A := hfin.fintype
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Function.End A := fun x => ⟨-x.1, hsymm x.1 x.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    apply _root_.funext
    intro x
    exact Subtype.ext (neg_neg x.1)
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  have hfix : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨0, h0⟩, Subtype.ext (neg_zero (G := Pt n))⟩, ?_⟩
    rintro ⟨⟨x, hx⟩, hfx⟩
    have hneg : -x = x := congrArg Subtype.val hfx
    have hx0 : x = 0 := by
      have : (2 : ℝ) • x = 0 := by rw [two_smul]; nth_rw 1 [← hneg]; exact neg_add_cancel x
      exact (smul_eq_zero.1 this).resolve_left two_ne_zero
    subst hx0; rfl
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Nat.odd_iff]
  rw [hfix] at hmod
  exact hmod

/-- l.170, l.151: `G(P)` is odd (the lattice points other than `0` come in pairs `±x`). -/
theorem G_odd (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (P : Set (Pt n)) (hP : InW (lat B) P) :
    Odd (G (lat B) P) := by
  obtain ⟨hcpt, _⟩ := latticePolytope_compact_convex hP.1
  have h0 : (0 : Pt n) ∈ P ∩ lat B := by
    have : (0 : Pt n) ∈ interior P ∩ lat B := by rw [hP.2.2]; rfl
    exact ⟨interior_subset this.1, this.2⟩
  refine odd_ncard_symm _ (lat_inter_finite B hB hcpt) ?_ h0
  rintro x ⟨hxP, z, rfl⟩
  refine ⟨by rw [← hP.2.1]; simpa using hxP, -z, ?_⟩
  have hneg : ofInt (-z) = -ofInt z := by funext i; simp [ofInt]
  show B.mulVec (ofInt (-z)) = -B.mulVec (ofInt z)
  rw [hneg, Matrix.mulVec_neg]

/-! ### Lemma 2.1 (l.172-180) -/

/-- If `K` is symmetric about `0`, so is its interior. -/
lemma neg_mem_interior {n : ℕ} {K : Set (Pt n)} (hsymm : ∀ x ∈ K, -x ∈ K) {x : Pt n} (hx : x ∈ interior K) :
    -x ∈ interior K := by
  have hK2 : (Homeomorph.neg (Pt n)) '' K = K := by
    ext y; simp only [Set.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hsymm w hw
    · intro hy; exact ⟨-y, hsymm y hy, neg_neg y⟩
  have : -x ∈ (Homeomorph.neg (Pt n)) '' interior K := ⟨x, hx, rfl⟩
  rw [(Homeomorph.neg (Pt n)).image_interior K, hK2] at this
  exact this

/-- The core of Lemma 2.1 and of the remark after it: a finite symmetric set `S ⊆ Γ ∩ C_n`, with `Γ ⊆ ℤⁿ` and
`0 ∈ Γ`, whose convex hull has an interior point, has `conv S ∈ W^n_Γ`. -/
lemma inW_of_cube_core {n : ℕ} (Γ S : Set (Pt n)) (hΓ : Γ ⊆ Zn n) (h0 : (0 : Pt n) ∈ Γ) (hfin : S.Finite)
    (hSΓ : S ⊆ Γ) (hcube : S ⊆ cube n) (hsymm : -S = S) (hint : (interior (convexHull ℝ S)).Nonempty) :
    InW Γ (convexHull ℝ S) := by
  have hneg : -convexHull ℝ S = convexHull ℝ S := by rw [← convexHull_neg, hsymm]
  refine ⟨⟨hfin.toFinset, by rw [Set.Finite.coe_toFinset]; exact hSΓ, by rw [Set.Finite.coe_toFinset]⟩,
    hneg, ?_⟩
  have hsub : convexHull ℝ S ⊆ cube n := convexHull_min hcube (cube_convex n)
  ext x
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hxΓ⟩
    have : x ∈ interior (cube n) ∩ Zn n := ⟨interior_mono hsub hx, hΓ hxΓ⟩
    rw [interior_cube_inter_Zn] at this
    exact this
  · rintro rfl
    refine ⟨?_, h0⟩
    obtain ⟨y, hy⟩ := hint
    have hsymmC : ∀ z ∈ convexHull ℝ S, -z ∈ convexHull ℝ S := fun z hz => by
      rw [← hneg]; simpa using hz
    have hny := neg_mem_interior hsymmC hy
    have := (convex_convexHull ℝ S).interior hy hny (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa using this

lemma cubePts_subset (n : ℕ) : cubePts n ⊆ cube n ∩ Zn n := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨fun i => ?_, z, rfl⟩
  simp only [ofInt]
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  exact abs_le.2 (hz i)

lemma cube_inter_Zn_finite (n : ℕ) : (cube n ∩ Zn n).Finite := Zn_inter_finite (cube_compact n).isBounded

/-- Lemma 2.1, l.172-178: if `Y ⊆ {-1,0,1}ⁿ`, `Y = -Y`, and `conv Y` has dimension `n`, then `conv Y ∈ Wⁿ`. -/
theorem lem_2_1 (n : ℕ) (Y : Set (Pt n)) (hY : Y ⊆ cubePts n) (hsymm : -Y = Y)
    (hdim : affineSpan ℝ (convexHull ℝ Y) = ⊤) : InW (Zn n) (convexHull ℝ Y) := by
  have hY' : Y ⊆ cube n ∩ Zn n := hY.trans (cubePts_subset n)
  exact inW_of_cube_core (Zn n) Y subset_rfl (zero_mem_Zn n) ((cube_inter_Zn_finite n).subset hY')
    (fun x hx => (hY' hx).2) (fun x hx => (hY' hx).1) hsymm
    ((convex_convexHull ℝ Y).interior_nonempty_iff_affineSpan_eq_top.2 hdim)

/-- l.180: the same for a sublattice `Γ ⊆ ℤⁿ` containing `0`: if `S ⊆ Γ ∩ C_n` is symmetric and spans `ℝⁿ`
(`n ≥ 1`), then `conv S ∈ W^n_Γ`. -/
theorem lem_2_1_sub (n : ℕ) (hn : 1 ≤ n) (Γ : Set (Pt n)) (hΓ : Γ ⊆ Zn n) (h0 : (0 : Pt n) ∈ Γ) (S : Set (Pt n))
    (hS : S ⊆ Γ ∩ cube n) (hsymm : -S = S) (hspan : Spans S) : InW Γ (convexHull ℝ S) := by
  have hSZ : S ⊆ cube n ∩ Zn n := fun x hx => ⟨(hS hx).2, hΓ (hS hx).1⟩
  have hne : S.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have htop : Submodule.span ℝ (∅ : Set (Pt n)) = ⊤ := by rw [← hemp]; exact hspan
    rw [Submodule.span_empty] at htop
    haveI : Nontrivial (Pt n) := by
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      infer_instance
    exact bot_ne_top htop
  obtain ⟨s, hs⟩ := hne
  have hns : -s ∈ S := by rw [← hsymm]; simpa using hs
  have h0conv : (0 : Pt n) ∈ convexHull ℝ S := by
    have := (convex_convexHull ℝ S) (subset_convexHull ℝ S hs) (subset_convexHull ℝ S hns)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa using this
  have hvec : vectorSpan ℝ (convexHull ℝ S) = ⊤ := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ h0conv]
    simp only [vsub_eq_sub, sub_zero, Set.image_id']
    exact top_le_iff.1 (hspan ▸ Submodule.span_mono (subset_convexHull ℝ S))
  have hdim : affineSpan ℝ (convexHull ℝ S) = ⊤ :=
    (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (Pt n) (Pt n) ⟨0, h0conv⟩).2 hvec
  exact inW_of_cube_core Γ S hΓ h0 ((cube_inter_Zn_finite n).subset hSZ) (fun x hx => (hS hx).1)
    (fun x hx => (hS hx).2) hsymm ((convex_convexHull ℝ S).interior_nonempty_iff_affineSpan_eq_top.2 hdim)

/-! ### Products (Lemma 2.2, (E4)) -/

/-- `ℝ^{p+q} ≅ ℝᵖ × ℝ^q`, `x ↦ (first p coordinates, last q coordinates)`. -/
def splitL (p q : ℕ) : Pt (p + q) ≃ₗ[ℝ] Pt p × Pt q where
  toFun x := (fun i => x (Fin.castAdd q i), fun j => x (Fin.natAdd p j))
  invFun ab := Fin.append ab.1 ab.2
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := Fin.append_castAdd_natAdd
  right_inv ab := by
    ext i
    · exact Fin.append_left ab.1 ab.2 i
    · exact Fin.append_right ab.1 ab.2 i

lemma prod_eq_preimage {p q : ℕ} (P : Set (Pt p)) (Q : Set (Pt q)) : prod P Q = splitL p q ⁻¹' (P ×ˢ Q) := rfl

lemma prod_eq_image {p q : ℕ} (P : Set (Pt p)) (Q : Set (Pt q)) :
    prod P Q = (splitL p q).symm '' (P ×ˢ Q) := by
  rw [prod_eq_preimage, LinearEquiv.image_symm_eq_preimage]

/-- Lemma 2.2's proof, l.187: `int(P×Q) = int P × int Q`. -/
theorem prod_interior (p q : ℕ) (P : Set (Pt p)) (Q : Set (Pt q)) :
    interior (prod P Q) = prod (interior P) (interior Q) := by
  rw [prod_eq_preimage, prod_eq_preimage, ← interior_prod_eq]
  exact ((splitL p q).toContinuousLinearEquiv.toHomeomorph.preimage_interior (P ×ˢ Q)).symm

lemma Zn_prod_iff {p q : ℕ} (x : Pt (p + q)) :
    x ∈ Zn (p + q) ↔ (splitL p q x).1 ∈ Zn p ∧ (splitL p q x).2 ∈ Zn q := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨⟨fun i => z (Fin.castAdd q i), rfl⟩, ⟨fun j => z (Fin.natAdd p j), rfl⟩⟩
  · rintro ⟨⟨z1, h1⟩, ⟨z2, h2⟩⟩
    refine ⟨Fin.append z1 z2, ?_⟩
    have hx : x = (splitL p q).symm (splitL p q x) := ((splitL p q).symm_apply_apply x).symm
    rw [hx]
    funext i
    induction i using Fin.addCases with
    | left i =>
      show ((Fin.append z1 z2 (Fin.castAdd q i) : ℤ) : ℝ) = Fin.append (splitL p q x).1 (splitL p q x).2 (Fin.castAdd q i)
      rw [Fin.append_left, Fin.append_left, ← h1]; rfl
    | right j =>
      show ((Fin.append z1 z2 (Fin.natAdd p j) : ℤ) : ℝ) = Fin.append (splitL p q x).1 (splitL p q x).2 (Fin.natAdd p j)
      rw [Fin.append_right, Fin.append_right, ← h2]; rfl

lemma prod_inter_Zn {p q : ℕ} (A : Set (Pt p)) (B : Set (Pt q)) :
    prod A B ∩ Zn (p + q) = splitL p q ⁻¹' ((A ∩ Zn p) ×ˢ (B ∩ Zn q)) := by
  ext x
  rw [Set.mem_inter_iff, Zn_prod_iff, prod_eq_preimage]
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]
  tauto

lemma ncard_prod_inter_Zn {p q : ℕ} (A : Set (Pt p)) (B : Set (Pt q)) :
    (prod A B ∩ Zn (p + q)).ncard = (A ∩ Zn p).ncard * (B ∩ Zn q).ncard := by
  rw [prod_inter_Zn, ← LinearEquiv.image_symm_eq_preimage,
    Set.ncard_image_of_injective _ (splitL p q).symm.injective, Set.ncard_prod]

lemma smul_prod {p q : ℕ} {c : ℝ} (hc : c ≠ 0) (P : Set (Pt p)) (Q : Set (Pt q)) :
    c • prod P Q = prod (c • P) (c • Q) := by
  ext x
  simp only [Set.mem_smul_set_iff_inv_smul_mem₀ hc, prod, Set.mem_ofPred_eq]
  rfl

/-- (E4), l.164: `L_{P×Q} = L_P L_Q`, since `k(P×Q) ∩ ℤ^{p+q} = (kP ∩ ℤᵖ) × (kQ ∩ ℤ^q)`. -/
theorem e4_prod_count (p q : ℕ) (P : Set (Pt p)) (Q : Set (Pt q)) (k : ℕ) :
    latCount (Zn (p + q)) (prod P Q) k = latCount (Zn p) P k * latCount (Zn q) Q k := by
  unfold latCount
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero]
    rcases P.eq_empty_or_nonempty with rfl | hP
    · have : prod (∅ : Set (Pt p)) Q = ∅ := by ext x; simp [prod]
      simp [this]
    rcases Q.eq_empty_or_nonempty with rfl | hQ
    · have : prod P (∅ : Set (Pt q)) = ∅ := by ext x; simp [prod]
      simp [this]
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    have hPQ : (prod P Q).Nonempty := ⟨(splitL p q).symm (a, b), by
      rw [prod_eq_preimage, Set.mem_preimage, LinearEquiv.apply_symm_apply]; exact ⟨ha, hb⟩⟩
    have e1 := latCount_zero (Zn (p + q)) (prod P Q) (zero_mem_Zn _) hPQ
    have e2 := latCount_zero (Zn p) P (zero_mem_Zn _) ⟨a, ha⟩
    have e3 := latCount_zero (Zn q) Q (zero_mem_Zn _) ⟨b, hb⟩
    unfold latCount at e1 e2 e3
    simp only [Nat.cast_zero] at e1 e2 e3
    rw [e1, e2, e3]
  · rw [smul_prod (by exact_mod_cast hk.ne'), ncard_prod_inter_Zn]

/-- Lemma 2.2, l.182-188: `P ∈ Wᵖ`, `Q ∈ W^q` ⇒ `P × Q ∈ W^{p+q}` and `g_1(P×Q) = g_1(P) + g_1(Q)`. -/
theorem lem_2_2 (hEHR : EhrhartThm) (p q : ℕ) (P : Set (Pt p)) (Q : Set (Pt q)) (hP : InW (Zn p) P)
    (hQ : InW (Zn q) Q) :
    InW (Zn (p + q)) (prod P Q) ∧ g (Zn (p + q)) (prod P Q) 1 = g (Zn p) P 1 + g (Zn q) Q 1 := by
  classical
  have hmem : InW (Zn (p + q)) (prod P Q) := by
    obtain ⟨⟨V, hVZ, hPV⟩, hPs, hPi⟩ := hP
    obtain ⟨⟨V', hVZ', hQV⟩, hQs, hQi⟩ := hQ
    refine ⟨⟨(V ×ˢ V').image (splitL p q).symm, ?_, ?_⟩, ?_, ?_⟩
    · rw [Finset.coe_image, Finset.coe_product]
      rintro _ ⟨ab, ⟨h1, h2⟩, rfl⟩
      rw [Zn_prod_iff, LinearEquiv.apply_symm_apply]
      exact ⟨hVZ h1, hVZ' h2⟩
    · rw [Finset.coe_image, Finset.coe_product, prod_eq_image, hPV, hQV, ← convexHull_prod]
      exact LinearMap.image_convexHull (splitL p q).symm.toLinearMap _
    · ext x
      rw [Set.mem_neg, prod_eq_preimage, Set.mem_preimage, Set.mem_preimage, map_neg]
      simp only [Prod.fst_neg, Prod.snd_neg, Set.mem_prod]
      rw [← Set.mem_neg, ← Set.mem_neg, hPs, hQs]
    · rw [prod_interior]
      ext x
      rw [Set.mem_inter_iff, Zn_prod_iff, prod_eq_preimage, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, z1, z2⟩
        have e1 : (splitL p q x).1 = 0 := by
          have : (splitL p q x).1 ∈ interior P ∩ Zn p := ⟨h1, z1⟩
          rw [hPi] at this; exact this
        have e2 : (splitL p q x).2 = 0 := by
          have : (splitL p q x).2 ∈ interior Q ∩ Zn q := ⟨h2, z2⟩
          rw [hQi] at this; exact this
        have : splitL p q x = 0 := Prod.ext e1 e2
        exact (map_eq_zero_iff _ (splitL p q).injective).1 this
      · rintro rfl
        rw [map_zero]
        have h1 : (0 : Pt p) ∈ interior P ∩ Zn p := by rw [hPi]; rfl
        have h2 : (0 : Pt q) ∈ interior Q ∩ Zn q := by rw [hQi]; rfl
        exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩
  refine ⟨hmem, ?_⟩
  -- Ehrhart's theorem for P, Q and P × Q: the three polynomials agree with the counts at every k ≥ 0.
  have hE : ∀ (m : ℕ) (R : Set (Pt m)), InW (Zn m) R →
      ∀ k : ℕ, (latCount (Zn m) R k : ℝ) = (ehrhartPoly (Zn m) R).eval (k : ℝ) := by
    intro m R hR k
    have hR' : IsLatticePolytope (lat (1 : Matrix (Fin m) (Fin m) ℝ)) R := by rw [lat_one']; exact hR.1
    have := hEHR m 1 (by simp) R hR' ⟨0, (inW_full_dim m _ R hR).1⟩ k
    rwa [lat_one'] at this
  have hpoly : ehrhartPoly (Zn (p + q)) (prod P Q) = ehrhartPoly (Zn p) P * ehrhartPoly (Zn q) Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.range (fun k : ℕ => (k : ℝ)))
    · rintro _ ⟨k, rfl⟩
      simp only [Set.mem_setOf_eq, Polynomial.eval_mul]
      rw [← hE _ _ hmem k, ← hE _ _ hP k, ← hE _ _ hQ k, e4_prod_count]
      push_cast; ring
    · exact Set.infinite_range_of_injective Nat.cast_injective
  have hP0 : g (Zn p) P 0 = 1 := by
    rw [g_zero_eq, latCount_zero _ _ (zero_mem_Zn p) ⟨0, interior_subset (inW_full_dim p _ P hP).1⟩]; simp
  have hQ0 : g (Zn q) Q 0 = 1 := by
    rw [g_zero_eq, latCount_zero _ _ (zero_mem_Zn q) ⟨0, interior_subset (inW_full_dim q _ Q hQ).1⟩]; simp
  unfold g at hP0 hQ0 ⊢
  rw [hpoly, Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp only [Finset.Nat.antidiagonal_zero, Finset.map_singleton, Finset.sum_cons, Finset.sum_singleton]
  simp [hP0, hQ0]
  ring

end Wills.Sec2
