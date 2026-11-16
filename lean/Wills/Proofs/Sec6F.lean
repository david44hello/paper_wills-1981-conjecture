/-
Wills/Proofs/Sec6F.lean — Section 6 rows of "Wills' (1981) conjecture holds if and only if the dimension is at most 4": Computation 1 (hyperplanes,
spanning), finiteness of the input families, Computation 2 (d = 2), Computation 3 (permuted Γ_I, membership),
Computation 4 (frame lattice under GL_4(ℤ)).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import Wills.Defs.Basic
import Wills.Defs.Cases
import Wills.Defs.Examples
import Wills.Facts.Basic
import Wills.Checks.Computations
import Wills.Proofs.Interp
import Wills.Proofs.Algebra
import Wills.Proofs.Sec2
import Wills.Proofs.Thm13
import Wills.Proofs.Sec5

open MeasureTheory Pointwise

namespace Wills.S6F

/-! ### Computation 1: a hyperplane through `0` meets `{-1,0,1}⁴` in at most 27 points -/

/-- The integer vectors of `{-1,0,1}⁴` whose `j`-th coordinate is `0`. -/
def slab (j : Fin 4) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun i => if i = j then {0} else Finset.Icc (-1 : ℤ) 1

lemma slab_card (j : Fin 4) : (slab j).card = 27 := by
  rw [slab, Fintype.card_piFinset, Fin.prod_univ_four]
  fin_cases j <;> decide

/-- `{x ∈ {-1,0,1}⁴ : w·x = 0}` as the image of integer vectors. -/
lemma hyp_eq_image (w : Pt 4) :
    {x | x ∈ cubePts 4 ∧ w ⬝ᵥ x = 0} =
      ofInt '' {z : Fin 4 → ℤ | (∀ i, -1 ≤ z i ∧ z i ≤ 1) ∧ w ⬝ᵥ ofInt z = 0} := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, h⟩
    exact ⟨z, ⟨hz, h⟩, rfl⟩
  · rintro ⟨z, ⟨hz, h⟩, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, h⟩

lemma dot_ofInt_sub (w : Pt 4) (a b : Fin 4 → ℤ) :
    w ⬝ᵥ ofInt a - w ⬝ᵥ ofInt b = ∑ i, w i * ((a i : ℝ) - b i) := by
  simp only [dotProduct, ofInt, mul_sub, Finset.sum_sub_distrib]

/-- Computation 1, l.349: a hyperplane through `0` contains at most 27 points of `{-1,0,1}⁴`. -/
theorem hyperplane_le_27 (w : Pt 4) (hw : w ≠ 0) : {x | x ∈ cubePts 4 ∧ w ⬝ᵥ x = 0}.ncard ≤ 27 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
  rw [Pi.zero_apply] at hj
  rw [hyp_eq_image, Set.ncard_image_of_injective _ Sec2.ofInt_injective, ← slab_card j,
    ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun z => Function.update z j 0) ?_ ?_
  · rintro z ⟨hz, -⟩
    rw [Finset.mem_coe, slab, Fintype.mem_piFinset]
    intro i
    by_cases hij : i = j
    · subst hij; simp
    · rw [Function.update_of_ne hij, if_neg hij, Finset.mem_Icc]; exact hz i
  · rintro a ⟨-, ha⟩ b ⟨-, hb⟩ hab
    have hoff : ∀ i, i ≠ j → a i = b i := fun i hij => by
      have := congrFun hab i
      simpa [Function.update_of_ne hij] using this
    have hd := dot_ofInt_sub w a b
    rw [ha, hb, sub_zero, Finset.sum_eq_single j (fun i _ hij => by rw [hoff i hij, sub_self, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)] at hd
    have hjj : (a j : ℝ) = b j := by
      rcases mul_eq_zero.1 hd.symm with h | h
      · exact absurd h hj
      · linarith
    funext i
    by_cases hij : i = j
    · subst hij; exact_mod_cast hjj
    · exact hoff i hij

/-! ### Computation 1: the input sets span `ℝ⁴` -/

/-- A linear functional on `ℝ⁴` is `x ↦ w·x` with `w i = f eᵢ`. -/
lemma functional_eq_dot (f : Pt 4 →ₗ[ℝ] ℝ) (x : Pt 4) : f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- A set that does not span `ℝ⁴` lies in a hyperplane `w·x = 0`, `w ≠ 0`. -/
lemma exists_dot_zero_of_not_spans {S : Set (Pt 4)} (h : ¬ Spans S) :
    ∃ w : Pt 4, w ≠ 0 ∧ ∀ x ∈ S, w ⬝ᵥ x = 0 := by
  obtain ⟨f, hf, hle⟩ := (Submodule.span ℝ S).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 h)
  refine ⟨fun i => f (Pi.single i 1), ?_, fun x hx => ?_⟩
  · intro hw
    apply hf
    refine LinearMap.ext fun x => ?_
    rw [functional_eq_dot, hw, zero_dotProduct, LinearMap.zero_apply]
  · rw [← functional_eq_dot]
    exact LinearMap.mem_ker.1 (hle (Submodule.subset_span hx))

lemma hyp_finite (w : Pt 4) : {x | x ∈ cubePts 4 ∧ w ⬝ᵥ x = 0}.Finite :=
  (Sec5.cubePts_finite 4).subset fun _ hx => hx.1

/-- Computation 1, l.349: each input set spans `ℝ⁴`, so `conv S ∈ W⁴` by Lemma 2.1. -/
theorem comp1_mem (S : Set (Pt 4)) (hS : Comp1Input S) : Spans S ∧ InW (Zn 4) (convexHull ℝ S) := by
  obtain ⟨hcube, hsymm, -, hcard⟩ := hS
  have hspan : Spans S := by
    by_contra hns
    obtain ⟨w, hw, hdot⟩ := exists_dot_zero_of_not_spans hns
    have hsub : S ⊆ {x | x ∈ cubePts 4 ∧ w ⬝ᵥ x = 0} := fun x hx => ⟨hcube hx, hdot x hx⟩
    have := (Set.ncard_le_ncard hsub (hyp_finite w)).trans (hyperplane_le_27 w hw)
    omega
  refine ⟨hspan, Sec2.lem_2_1_sub 4 (by norm_num) (Zn 4) subset_rfl (Sec2.zero_mem_Zn 4) S
    (fun x hx => ⟨(Sec2.cubePts_subset 4 (hcube hx)).2, (Sec2.cubePts_subset 4 (hcube hx)).1⟩) hsymm hspan⟩

/-! ### l.151 (d): finitely many sets -/

/-- The points of `A⁻¹ ℤ⁴` in the cube are finitely many (if `det A = 0` then `A⁻¹ = 0`). -/
lemma inv_lat_cube_finite (A : Matrix (Fin 4) (Fin 4) ℝ) : (cube 4 ∩ lat A⁻¹).Finite := by
  by_cases hA : A.det = 0
  · have h0 : A⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit A (by rw [hA]; exact not_isUnit_zero)
    refine (Set.finite_singleton (0 : Pt 4)).subset ?_
    rintro _ ⟨-, z, rfl⟩
    show A⁻¹.mulVec (ofInt z) ∈ ({0} : Set (Pt 4))
    rw [h0, Matrix.zero_mulVec]
    exact Set.mem_singleton _
  · have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
    have hdet : A⁻¹.det ≠ 0 := by
      intro h
      have := Matrix.det_nonsing_inv_mul_det A hu
      rw [h, zero_mul] at this
      exact zero_ne_one this
    exact Sec2.lat_inter_finite A⁻¹ hdet (Sec2.cube_compact 4)

/-- l.151 (d): in each case only finitely many sets of lattice points remain. -/
theorem finitely_many_sets :
    {S | Comp1Input S}.Finite ∧ (∀ m, {S | Comp3Input m S}.Finite) ∧ ∀ j, {S | Comp5Input j S}.Finite := by
  refine ⟨(Sec5.cubePts_finite 4).finite_subsets.subset fun S hS => hS.1,
    fun m => (Sec5.cubePts_finite 4).finite_subsets.subset fun S hS => fun x hx => (hS.1 hx).2,
    fun j => (inv_lat_cube_finite (Matrix.transpose (toReal (frameRepH j)))).finite_subsets.subset
      fun S hS => fun x hx => ?_⟩
  exact ⟨(hS.1.1 hx).2, (hS.1.1 hx).1⟩

/-! ### Computation 2: `d = 2` -/

lemma card_le_four (I : Finset (Fin 4)) : I.card ≤ 4 := by
  simpa using Finset.card_le_univ I

/-- A set whose span contains every unit vector spans `ℝ⁴`. -/
lemma spans_of_units (T : Set (Pt 4)) (h : ∀ i : Fin 4, (Pi.single i 1 : Pt 4) ∈ Submodule.span ℝ T) :
    Spans T := by
  unfold Spans
  rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin 4)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  exact h i

/-- `I = {1, 2}` of the paper (coordinates `0, 1` in Lean). -/
def g01 : Finset (Fin 4) := {0, 1}

lemma mem_g01 (z : Fin 4 → ℤ) (hz : ∀ i, -1 ≤ z i ∧ z i ≤ 1) (he : Even (∑ i ∈ g01, z i)) :
    ofInt z ∈ gammaI g01 ∩ cubePts 4 := ⟨⟨z, rfl, he⟩, z, hz, rfl⟩

lemma e0_eq : (Pi.single (0 : Fin 4) (1 : ℝ) : Pt 4) =
    (1 / 2 : ℝ) • (ofInt ![1, 1, 0, 0] + ofInt ![1, -1, 0, 0]) := by
  funext k; fin_cases k <;> simp [ofInt] <;> norm_num

lemma e1_eq : (Pi.single (1 : Fin 4) (1 : ℝ) : Pt 4) =
    (1 / 2 : ℝ) • (ofInt ![1, 1, 0, 0] - ofInt ![1, -1, 0, 0]) := by
  funext k; fin_cases k <;> simp [ofInt] <;> norm_num

lemma e2_eq : (Pi.single (2 : Fin 4) (1 : ℝ) : Pt 4) = ofInt ![0, 0, 1, 0] := by
  funext k; fin_cases k <;> simp [ofInt]

lemma e3_eq : (Pi.single (3 : Fin 4) (1 : ℝ) : Pt 4) = ofInt ![0, 0, 0, 1] := by
  funext k; fin_cases k <;> simp [ofInt]

lemma spans_g01 : Spans (gammaI g01 ∩ cubePts 4) := by
  have ha : ofInt ![1, 1, 0, 0] ∈ gammaI g01 ∩ cubePts 4 := mem_g01 _ (by decide) (by decide)
  have hb : ofInt ![1, -1, 0, 0] ∈ gammaI g01 ∩ cubePts 4 := mem_g01 _ (by decide) (by decide)
  have hc : ofInt ![0, 0, 1, 0] ∈ gammaI g01 ∩ cubePts 4 := mem_g01 _ (by decide) (by decide)
  have hd : ofInt ![0, 0, 0, 1] ∈ gammaI g01 ∩ cubePts 4 := mem_g01 _ (by decide) (by decide)
  apply spans_of_units
  intro i
  fin_cases i
  · show (Pi.single (0 : Fin 4) (1 : ℝ) : Pt 4) ∈ _
    rw [e0_eq]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ha) (Submodule.subset_span hb))
  · show (Pi.single (1 : Fin 4) (1 : ℝ) : Pt 4) ∈ _
    rw [e1_eq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ha) (Submodule.subset_span hb))
  · show (Pi.single (2 : Fin 4) (1 : ℝ) : Pt 4) ∈ _
    rw [e2_eq]
    exact Submodule.subset_span hc
  · show (Pi.single (3 : Fin 4) (1 : ℝ) : Pt 4) ∈ _
    rw [e3_eq]
    exact Submodule.subset_span hd

/-- Computation 2, l.353 (and l.302): the maximum for `d = 2` is `45`. -/
theorem comp2_d2_max :
    (∀ B : Matrix (Fin 4) (Fin 4) ℤ, |B.det| = 2 → (subLat B ∩ cubePts 4).ncard ≤ 45) ∧
      ∃ B : Matrix (Fin 4) (Fin 4) ℤ, |B.det| = 2 ∧ Spans (subLat B ∩ cubePts 4) ∧
        (subLat B ∩ cubePts 4).ncard = 45 := by
  refine ⟨fun B hB => ?_, ?_⟩
  · obtain ⟨I, hI, hBI⟩ := Sec5.index2_eq_gammaI.1 B hB
    rw [hBI]
    obtain ⟨-, h1, h2, h3, h4⟩ := Sec5.gammaI_counts I hI
    have hpos := Finset.card_pos.2 hI
    have hle := card_le_four I
    rcases (by omega : I.card = 1 ∨ I.card = 2 ∨ I.card = 3 ∨ I.card = 4) with h | h | h | h
    · have := h1 h; omega
    · have := h2 h; omega
    · have := h3 h; omega
    · have := h4 h; omega
  · have hI : g01.Nonempty := ⟨0, by decide⟩
    obtain ⟨B, hB, hBI⟩ := Sec5.index2_eq_gammaI.2 g01 hI
    refine ⟨B, hB, ?_, ?_⟩
    · rw [hBI]; exact spans_g01
    · rw [hBI]; exact (Sec5.gammaI_counts g01 hI).2.2.1 (by decide)

/-! ### Computation 3: permutations of coordinates, and membership -/

lemma signedPerm_false (π : Equiv.Perm (Fin 4)) (x : Pt 4) :
    signedPerm (π, fun _ => false) x = fun i => x (π i) := by
  funext i; simp [signedPerm]

/-- Two subsets of `Fin 4` of the same size: a permutation carries one onto the other. -/
lemma exists_perm_image (I J : Finset (Fin 4)) (h : I.card = J.card) :
    ∃ π : Equiv.Perm (Fin 4), J.image π = I := by
  have hc : Fintype.card {x // x ∈ J} = Fintype.card {x // x ∈ I} := by
    rw [Fintype.card_coe, Fintype.card_coe, h]
  let e : {x // x ∈ J} ≃ {x // x ∈ I} := Fintype.equivOfCardEq hc
  refine ⟨e.extendSubtype, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact e.extendSubtype_mem x hx
  · rw [Finset.card_image_of_injective _ e.extendSubtype.injective, h]

/-- Computation 3, l.357: a permutation of coordinates carries `Γ_I` onto `Γ_J` when `|I| = |J|`. -/
theorem gammaI_perm (I J : Finset (Fin 4)) (h : I.card = J.card) :
    ∃ π : Equiv.Perm (Fin 4), signedPerm (π, fun _ => false) '' gammaI I = gammaI J := by
  obtain ⟨π, hπ⟩ := exists_perm_image I J h
  refine ⟨π, ?_⟩
  ext y
  simp only [Set.mem_image, signedPerm_false]
  constructor
  · rintro ⟨x, ⟨z, rfl, hz⟩, rfl⟩
    refine ⟨fun i => z (π i), rfl, ?_⟩
    rw [← hπ, Finset.sum_image π.injective.injOn] at hz
    exact hz
  · rintro ⟨u, rfl, hu⟩
    refine ⟨ofInt (fun k => u (π.symm k)), ⟨fun k => u (π.symm k), rfl, ?_⟩, ?_⟩
    · rw [← hπ, Finset.sum_image π.injective.injOn]
      simpa using hu
    · funext i; simp [ofInt]

lemma gammaI_subset_Zn (I : Finset (Fin 4)) : gammaI I ⊆ Zn 4 := by
  rintro _ ⟨z, rfl, -⟩
  exact ⟨z, rfl⟩

lemma zero_mem_gammaI (I : Finset (Fin 4)) : (0 : Pt 4) ∈ gammaI I :=
  ⟨0, ofInt_zero.symm, by simp⟩

/-- Computation 3, l.357: each input `conv S` lies in `W^4_{Γ_m}`. -/
theorem comp3_mem (m : ℕ) (S : Set (Pt 4)) (hS : Comp3Input m S) : InW (gammaM m) (convexHull ℝ S) := by
  obtain ⟨hsub, hsymm, -, hspan, -⟩ := hS
  exact Sec2.lem_2_1_sub 4 (by norm_num) (gammaM m) (gammaI_subset_Zn _) (zero_mem_gammaI _) S
    (fun x hx => ⟨(hsub hx).1, (Sec2.cubePts_subset 4 (hsub hx).2).1⟩) hsymm hspan

/-! ### Computation 4: the frame lattice does not change under `V ↦ UV`, `U ∈ GL_4(ℤ)` -/

lemma toReal_mul {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℤ) : toReal (U * V) = toReal U * toReal V := by
  ext i j
  simp [toReal, Matrix.mul_apply]

lemma toReal_one {n : ℕ} : toReal (1 : Matrix (Fin n) (Fin n) ℤ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [toReal, Matrix.one_apply, h]

lemma isUnit_det_of_GLZ {U : Matrix (Fin 4) (Fin 4) ℤ} (hU : IsGLZ U) : IsUnit U.det := by
  rcases hU with h | h <;> rw [h]
  · exact isUnit_one
  · exact isUnit_one.neg

lemma toReal_inv_GLZ {U : Matrix (Fin 4) (Fin 4) ℤ} (hU : IsGLZ U) : (toReal U)⁻¹ = toReal U⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [← toReal_mul, Matrix.nonsing_inv_mul U (isUnit_det_of_GLZ hU), toReal_one]

/-- Computation 4, l.361: for `U ∈ GL_4(ℤ)` the frame matrices `V` and `UV` give the same lattice `V⁻¹ℤ⁴`. -/
theorem frame_lat_GL (V U : Matrix (Fin 4) (Fin 4) ℤ) (hV : V.det ≠ 0) (hU : IsGLZ U) :
    lat (toReal (U * V))⁻¹ = lat (toReal V)⁻¹ := by
  have hu := isUnit_det_of_GLZ hU
  rw [toReal_mul, Matrix.mul_inv_rev, toReal_inv_GLZ hU]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨U⁻¹.mulVec z, ?_⟩
    show (toReal V)⁻¹.mulVec (ofInt (U⁻¹.mulVec z)) = ((toReal V)⁻¹ * toReal U⁻¹).mulVec (ofInt z)
    rw [← Matrix.mulVec_mulVec, Sec5.toReal_mulVec_ofInt]
  · rintro ⟨y, rfl⟩
    refine ⟨U.mulVec y, ?_⟩
    show ((toReal V)⁻¹ * toReal U⁻¹).mulVec (ofInt (U.mulVec y)) = (toReal V)⁻¹.mulVec (ofInt y)
    rw [← Matrix.mulVec_mulVec, Sec5.toReal_mulVec_ofInt, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul U hu,
      Matrix.one_mulVec]

end Wills.S6F
