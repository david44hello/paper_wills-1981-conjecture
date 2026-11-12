/-
Wills/Proofs/Rows280.lean — proofs of rows added for the paper's text versions 2.80-3.10 (Sections 5, 6 and 7): Case I
for the cube (Figure 3); the symmetry of the walk (l.332); the symmetry of the sandwich search (l.369); the six values
that fix the Ehrhart polynomial in Computation 5 (l.330); an include step of the sandwich search keeps the lower set
in the family (l.369); the dual of a frame lattice (l.326).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import Wills.Defs.Basic
import Wills.Defs.Cases
import Wills.Proofs.Sec5
import Wills.Proofs.Sec6E
import Wills.Proofs.Sandwich
import Wills.Proofs.Thm71
import Wills.Proofs.Thm12
import Wills.Facts.Basic
import Wills.Checks.Computations
import Wills.Proofs.Interp

open MeasureTheory Pointwise

namespace Wills.R280

/-! ### Signed permutations: inverse, images of sets -/

/-- The inverse `σ⁻¹ : y ↦ (ε_{π⁻¹ k} y_{π⁻¹ k})_k` of a signed permutation, again a signed permutation. -/
def spInv (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : Equiv.Perm (Fin 4) × (Fin 4 → Bool) :=
  (σ.1.symm, fun k => σ.2 (σ.1.symm k))

/-- `σ⁻¹ (σ x) = x`. -/
lemma sp_inv_apply (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (x : Pt 4) :
    signedPerm (spInv σ) (signedPerm σ x) = x := by
  funext k
  unfold signedPerm spInv
  dsimp only
  simp only [Equiv.apply_symm_apply]
  rw [← mul_assoc, S71.sign_mul_self, one_mul]

/-- `σ (σ⁻¹ y) = y`. -/
lemma sp_apply_inv (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (y : Pt 4) :
    signedPerm σ (signedPerm (spInv σ) y) = y := by
  funext i
  simp only [signedPerm, spInv, Equiv.symm_apply_apply]
  rw [← mul_assoc, S71.sign_mul_self, one_mul]

/-- `σ⁻¹ (σ A) = A`. -/
lemma sp_symm_image_image (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (A : Set (Pt 4)) :
    signedPerm (spInv σ) '' (signedPerm σ '' A) = A := by
  rw [Set.image_image]
  simp only [sp_inv_apply, Set.image_id']

/-- `σ (σ⁻¹ A) = A`. -/
lemma sp_image_symm_image (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (A : Set (Pt 4)) :
    signedPerm σ '' (signedPerm (spInv σ) '' A) = A := by
  rw [Set.image_image]
  simp only [sp_apply_inv, Set.image_id']

/-- If `σ` preserves `Λ`, so does `σ⁻¹`. -/
lemma preserves_spInv {Λ : Set (Pt 4)} {σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)} (hσ : Preserves Λ σ) :
    Preserves Λ (spInv σ) := by
  have hσ' : signedPerm σ '' Λ = Λ := hσ
  show signedPerm (spInv σ) '' Λ = Λ
  calc signedPerm (spInv σ) '' Λ = signedPerm (spInv σ) '' (signedPerm σ '' Λ) := by rw [hσ']
    _ = Λ := sp_symm_image_image σ Λ

lemma sp_injective (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : Function.Injective (signedPerm σ) :=
  fun x y h => by rw [← sp_inv_apply σ x, h, sp_inv_apply σ y]

lemma sp_neg (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (x : Pt 4) : signedPerm σ (-x) = -signedPerm σ x := by
  funext i
  simp [signedPerm]

lemma sp_zero (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) : signedPerm σ 0 = 0 := by
  funext i
  simp [signedPerm]

lemma image_inter_sp (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (A B : Set (Pt 4)) :
    signedPerm σ '' (A ∩ B) = signedPerm σ '' A ∩ signedPerm σ '' B :=
  Set.image_inter (sp_injective σ)

lemma conv_sp (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (A : Set (Pt 4)) :
    convexHull ℝ (signedPerm σ '' A) = signedPerm σ '' convexHull ℝ A := by
  rw [← S71.spEquiv_coe, S12.image_convexHull_linEquiv]

lemma interior_sp (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (A : Set (Pt 4)) :
    interior (signedPerm σ '' A) = signedPerm σ '' interior A := by
  have h := (S71.spEquiv σ).toContinuousLinearEquiv.toHomeomorph.image_interior A
  rw [ContinuousLinearEquiv.coe_toHomeomorph, LinearEquiv.coe_toContinuousLinearEquiv',
    S71.spEquiv_coe] at h
  exact h.symm

/-- `σ` maps symmetric sets to symmetric sets. -/
lemma neg_sp (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) {A : Set (Pt 4)} (h : -A = A) :
    -(signedPerm σ '' A) = signedPerm σ '' A := by
  rw [← S71.spEquiv_coe, ← S12.image_neg_linEquiv, h]

/-- `σ` (preserving `Λ`) maps `Λ`-saturated sets to `Λ`-saturated sets. -/
lemma saturated_sp {Λ : Set (Pt 4)} {σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)} (hσ : Preserves Λ σ)
    {A : Set (Pt 4)} (h : Saturated Λ A) : Saturated Λ (signedPerm σ '' A) := by
  have hσ' : signedPerm σ '' Λ = Λ := hσ
  have h' : convexHull ℝ A ∩ Λ = A := h
  show convexHull ℝ (signedPerm σ '' A) ∩ Λ = signedPerm σ '' A
  calc convexHull ℝ (signedPerm σ '' A) ∩ Λ = signedPerm σ '' convexHull ℝ A ∩ signedPerm σ '' Λ := by
        rw [conv_sp, hσ']
    _ = signedPerm σ '' (convexHull ℝ A ∩ Λ) := (image_inter_sp σ _ _).symm
    _ = signedPerm σ '' A := by rw [h']

/-- `σ` (preserving `Λ`) keeps `int(conv A) ∩ Λ = {0}`. -/
lemma interior_sp_eq {Λ : Set (Pt 4)} {σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)} (hσ : Preserves Λ σ)
    {A : Set (Pt 4)} (h : interior (convexHull ℝ A) ∩ Λ = {0}) :
    interior (convexHull ℝ (signedPerm σ '' A)) ∩ Λ = {0} := by
  have hσ' : signedPerm σ '' Λ = Λ := hσ
  calc interior (convexHull ℝ (signedPerm σ '' A)) ∩ Λ
        = signedPerm σ '' interior (convexHull ℝ A) ∩ signedPerm σ '' Λ := by rw [conv_sp, interior_sp, hσ']
    _ = signedPerm σ '' (interior (convexHull ℝ A) ∩ Λ) := (image_inter_sp σ _ _).symm
    _ = {0} := by rw [h, Set.image_singleton, sp_zero]

/-- The matrix with columns `σ s_j`: the rows of `colMat s` permuted by `π` and multiplied by the signs `ε_i`. -/
lemma colMat_sp (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (s : Fin 4 → Pt 4) :
    colMat (fun j => signedPerm σ (s j)) =
      Matrix.of (fun i j => (if σ.2 i then (-1 : ℝ) else 1) * ((colMat s).submatrix σ.1 id) i j) := by
  ext i j
  rfl

/-- `|det(σ s_1, …, σ s_4)| = |det(s_1, …, s_4)|`. -/
lemma abs_det_sp (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (s : Fin 4 → Pt 4) :
    |(colMat fun j => signedPerm σ (s j)).det| = |(colMat s).det| := by
  rw [colMat_sp, Matrix.det_mul_column, Matrix.det_permute, abs_mul, abs_mul, Finset.abs_prod]
  have h1 : ∀ i, |(if σ.2 i then (-1 : ℝ) else 1)| = 1 := fun i => by cases σ.2 i <;> simp
  simp only [h1, Finset.prod_const_one, one_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ.1) with h | h <;> simp [h]

lemma abs_sign_mul (b : Bool) (a : ℝ) : |(if b then (-1 : ℝ) else 1) * a| = |a| := by
  cases b <;> simp

/-- `σ (e_{π i}) = ε_i e_i`. -/
lemma sp_unitVec (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (i : Fin 4) :
    signedPerm σ (unitVec (σ.1 i)) = (if σ.2 i then (-1 : ℝ) else 1) • unitVec i := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [signedPerm, unitVec]
  · simp [signedPerm, unitVec, σ.1.injective.eq_iff, hji]

/-- A symmetric set containing every `e_j` has every `e_i` in its image under `σ`. -/
lemma unitVec_mem_sp (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) {S : Set (Pt 4)} (hsymm : -S = S)
    (hunit : ∀ i, unitVec i ∈ S) (i : Fin 4) : unitVec i ∈ signedPerm σ '' S := by
  cases hb : σ.2 i
  · refine ⟨unitVec (σ.1 i), hunit _, ?_⟩
    rw [sp_unitVec, hb]
    simp
  · refine ⟨-unitVec (σ.1 i), (S6E.neg_mem_symm hsymm).2 (hunit _), ?_⟩
    rw [sp_neg, sp_unitVec, hb]
    simp

/-! ### Signed permutations preserve the family `S(Λ)` -/

/-- A signed permutation that preserves `Λ` carries members of `S(Λ)` to members of `S(Λ)`. -/
lemma inA_signedPerm (Λ S : Set (Pt 4)) (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (hσ : Preserves Λ σ)
    (hS : InA Λ S) : InA Λ (signedPerm σ '' S) := by
  obtain ⟨hsub, hsymm, hunit, hdet, hsat, hint⟩ := hS
  have hσ' : signedPerm σ '' Λ = Λ := hσ
  refine ⟨?_, neg_sp σ hsymm, unitVec_mem_sp σ hsymm hunit, ?_, saturated_sp hσ hsat, interior_sp_eq hσ hint⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hσ']
      exact Set.mem_image_of_mem _ (hsub hx).1
    · show ∀ i, |signedPerm σ x i| ≤ 1
      intro i
      simp only [signedPerm]
      rw [abs_sign_mul]
      exact (hsub hx).2 (σ.1 i)
  · intro s hs
    choose t ht hts using hs
    have hst : s = fun j => signedPerm σ (t j) := funext fun j => (hts j).symm
    rw [hst, abs_det_sp]
    exact hdet t ht

/-- `σ (Q \ {v, -v}) = σQ \ {σv, -σv}`. -/
lemma image_diff_pair (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (Q : Set (Pt 4)) (v : Pt 4) :
    signedPerm σ '' (Q \ {v, -v}) = signedPerm σ '' Q \ {signedPerm σ v, -signedPerm σ v} := by
  rw [Set.image_sdiff (sp_injective σ), Set.image_pair, sp_neg]

/-- `σ` maps the vertices of `conv Q` onto those of `conv σQ`. -/
lemma extremePoints_sp (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (Q : Set (Pt 4)) :
    signedPerm σ '' Set.extremePoints ℝ (convexHull ℝ Q) =
      Set.extremePoints ℝ (convexHull ℝ (signedPerm σ '' Q)) := by
  rw [conv_sp, ← S71.spEquiv_coe]
  exact image_extremePoints (S71.spEquiv σ) _

/-! ### The rows -/

/-- Figure 3: `C_4` belongs to Case I (`M(C_4)` contains the basis `e_1, …, e_4`). -/
theorem cube4_case_I_proof : CaseI (cube 4) := by
  refine ⟨1, Or.inl Matrix.det_one, fun i => ⟨⟨_, rfl⟩, fun x hx => ?_⟩⟩
  have h : ofInt ((1 : Matrix (Fin 4) (Fin 4) ℤ) i) ⬝ᵥ x = x i := by
    simp [ofInt, dotProduct, Matrix.one_apply]
  rw [h]
  exact hx i

/-- l.332: a symmetry `σ` (a signed permutation preserving `Λ`) maps saturated symmetric sets to saturated
symmetric sets and the vertices of `conv Q` to those of `conv σQ`, so the sets obtained from `σQ` by deleting a pair
of opposite vertices are the images under `σ` of those obtained from `Q`. -/
theorem walk_symm_proof (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (Λ Q : Set (Pt 4)) (hσ : Preserves Λ σ) :
    (Saturated Λ Q → Saturated Λ (signedPerm σ '' Q)) ∧ (-Q = Q → -(signedPerm σ '' Q) = signedPerm σ '' Q) ∧
      signedPerm σ '' Set.extremePoints ℝ (convexHull ℝ Q) =
        Set.extremePoints ℝ (convexHull ℝ (signedPerm σ '' Q)) ∧
      {A | ∃ w ∈ Set.extremePoints ℝ (convexHull ℝ (signedPerm σ '' Q)), A = signedPerm σ '' Q \ {w, -w}} =
        {A | ∃ v ∈ Set.extremePoints ℝ (convexHull ℝ Q), A = signedPerm σ '' (Q \ {v, -v})} := by
  refine ⟨fun h => saturated_sp hσ h, fun h => neg_sp σ h, extremePoints_sp σ Q, ?_⟩
  ext A
  simp only [Set.mem_ofPred_eq]
  rw [← extremePoints_sp]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, (image_diff_pair σ Q v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨signedPerm σ v, ⟨v, hv, rfl⟩, image_diff_pair σ Q v⟩

/-- l.369: a signed permutation `σ` preserving `Λ` carries the sets between `S⁻` and `S⁺` (the saturated symmetric
sets, and the members of `S(Λ)`) onto the sets between `σS⁻` and `σS⁺`. -/
theorem sandwich_symm_proof (Λ Sm Sp : Set (Pt 4)) (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool))
    (hσ : Preserves Λ σ) :
    (fun S => signedPerm σ '' S) '' {S | Saturated Λ S ∧ -S = S ∧ Sm ⊆ S ∧ S ⊆ Sp} =
        {S | Saturated Λ S ∧ -S = S ∧ signedPerm σ '' Sm ⊆ S ∧ S ⊆ signedPerm σ '' Sp} ∧
      (fun S => signedPerm σ '' S) '' {S | InA Λ S ∧ Sm ⊆ S ∧ S ⊆ Sp} =
        {S | InA Λ S ∧ signedPerm σ '' Sm ⊆ S ∧ S ⊆ signedPerm σ '' Sp} := by
  have hσ' := preserves_spInv hσ
  have hm : ∀ S', signedPerm σ '' Sm ⊆ S' → Sm ⊆ signedPerm (spInv σ) '' S' := fun S' h =>
    (sp_symm_image_image σ Sm).symm.subset.trans (Set.image_mono h)
  have hp : ∀ S', S' ⊆ signedPerm σ '' Sp → signedPerm (spInv σ) '' S' ⊆ Sp := fun S' h =>
    (Set.image_mono h).trans (sp_symm_image_image σ Sp).subset
  constructor
  · ext S'
    constructor
    · rintro ⟨S, ⟨hsat, hsymm, hSm, hSp⟩, rfl⟩
      exact ⟨saturated_sp hσ hsat, neg_sp σ hsymm, Set.image_mono hSm, Set.image_mono hSp⟩
    · rintro ⟨hsat, hsymm, hSm, hSp⟩
      exact ⟨signedPerm (spInv σ) '' S', ⟨saturated_sp hσ' hsat, neg_sp _ hsymm, hm S' hSm, hp S' hSp⟩,
        sp_image_symm_image σ S'⟩
  · ext S'
    constructor
    · rintro ⟨S, ⟨hA, hSm, hSp⟩, rfl⟩
      exact ⟨inA_signedPerm Λ S σ hσ hA, Set.image_mono hSm, Set.image_mono hSp⟩
    · rintro ⟨hA, hSm, hSp⟩
      exact ⟨signedPerm (spInv σ) '' S', ⟨inA_signedPerm Λ S' _ hσ' hA, hm S' hSm, hp S' hSp⟩,
        sp_image_symm_image σ S'⟩

/-! ### l.330: the six values that fix the Ehrhart polynomial (Computation 5) -/

open Polynomial

/-- Kernel check over the 39 representatives: `frameRepH j` is lower triangular with nonzero diagonal. -/
lemma frameRepH_check : ∀ j : Fin 39,
    (∀ i k : Fin 4, k ≤ i ∨ Matrix.transpose (frameRepH j) k i = 0) ∧ ∀ i : Fin 4, frameRepH j i i ≠ 0 := by
  decide +kernel

/-- `det (frameRepH j) ≠ 0` (it is lower triangular with nonzero diagonal). -/
lemma frameRepH_det_ne_zero (j : Fin 39) : (frameRepH j).det ≠ 0 := by
  obtain ⟨htri, hdiag⟩ := frameRepH_check j
  rw [Matrix.det_of_isLowerTriangular (frameRepH j) (fun i k hik =>
    (htri i k).resolve_left (not_le.2 (OrderDual.toDual_lt_toDual.1 hik)))]
  exact Finset.prod_ne_zero_iff.2 fun i _ => hdiag i

/-- The matrix `B = ((frameRepH j)ᵀ)⁻¹` with `frameRep j = lat B` has `det B ≠ 0`. -/
lemma frameRep_mat_det_ne_zero (j : Fin 39) :
    ((Matrix.transpose (toReal (frameRepH j)))⁻¹).det ≠ 0 := by
  refine (Matrix.isUnit_nonsing_inv_det _ ?_).ne_zero
  rw [Matrix.det_transpose]
  exact isUnit_iff_ne_zero.2 (Sec5.toReal_det_ne_zero (frameRepH_det_ne_zero j))

/-- A real polynomial of degree at most `4` has degree `< 6`. -/
lemma degree_lt_six {p : ℝ[X]} (hp : p.natDegree ≤ 4) : p.degree < 6 :=
  lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le (Nat.le_succ_of_le hp))

/-- The six nodes `-2, …, 3` are distinct. -/
lemma card_six_nodes : ({-2, -1, 0, 1, 2, 3} : Finset ℝ).card = 6 := by
  norm_num [Finset.card_insert_of_notMem]

/-- The six values of `L_{P,Λ}` at `k = -2, …, 3` for `P` a lattice polytope of `Λ = lat B` with nonempty interior
(and `0 ∈ Λ`, `P` nonempty): `1` at `0`, the counts at `1, 2, 3`, the interior counts at `-1, -2` ((E2) with
`n = 4`); a polynomial of degree at most `4` with these six values is the Ehrhart polynomial. -/
lemma poly_six_values_gen (hE2 : EhrhartReciprocity) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0)
    (P : Set (Pt 4)) (hLP : IsLatticePolytope (lat B) P) (hint : (interior P).Nonempty) :
    (ehrhartPoly (lat B) P).eval 0 = 1 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 3 → (ehrhartPoly (lat B) P).eval (k : ℝ) = latCount (lat B) P k) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 2 → (ehrhartPoly (lat B) P).eval (-(k : ℝ)) = intCount (lat B) P k) ∧
      ∀ p : ℝ[X], p.natDegree ≤ 4 → p.eval 0 = 1 →
        (∀ k : ℕ, 1 ≤ k → k ≤ 3 → p.eval (k : ℝ) = latCount (lat B) P k) →
        (∀ k : ℕ, 1 ≤ k → k ≤ 2 → p.eval (-(k : ℝ)) = intCount (lat B) P k) →
        p = ehrhartPoly (lat B) P := by
  have hP : P.Nonempty := hint.mono interior_subset
  have h1 : (ehrhartPoly (lat B) P).eval 0 = 1 := by
    have h0 := ehrhartPoly_eval_node (lat B) P (Nat.zero_le 4)
    rw [latCount_zero _ _ (zero_mem_lat B) hP] at h0
    simpa using h0
  have h2 : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → (ehrhartPoly (lat B) P).eval (k : ℝ) = latCount (lat B) P k :=
    fun k _ hk => ehrhartPoly_eval_node (lat B) P (by omega)
  have h3 : ∀ k : ℕ, 1 ≤ k → k ≤ 2 → (ehrhartPoly (lat B) P).eval (-(k : ℝ)) = intCount (lat B) P k := by
    intro k hk1 _
    rw [hE2 4 B hB P hLP hint k hk1]
    norm_num
  refine ⟨h1, h2, h3, fun p hp hp0 hp123 hp12 => ?_⟩
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq (s := ({-2, -1, 0, 1, 2, 3} : Finset ℝ)) ?_ ?_ ?_
  · rw [card_six_nodes]; exact degree_lt_six hp
  · rw [card_six_nodes]; exact degree_lt_six (ehrhartPoly_natDegree_le (lat B) P)
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have ha := hp12 2 (by norm_num) (by norm_num)
      have hb := h3 2 (by norm_num) (by norm_num)
      push_cast at ha hb
      rw [ha, hb]
    · have ha := hp12 1 (by norm_num) (by norm_num)
      have hb := h3 1 (by norm_num) (by norm_num)
      push_cast at ha hb
      rw [ha, hb]
    · rw [hp0, h1]
    · have ha := hp123 1 (by norm_num) (by norm_num)
      have hb := h2 1 (by norm_num) (by norm_num)
      push_cast at ha hb
      rw [ha, hb]
    · have ha := hp123 2 (by norm_num) (by norm_num)
      have hb := h2 2 (by norm_num) (by norm_num)
      push_cast at ha hb
      rw [ha, hb]
    · have ha := hp123 3 (by norm_num) (by norm_num)
      have hb := h2 3 (by norm_num) (by norm_num)
      push_cast at ha hb
      rw [ha, hb]

/-- l.330, Computation 5: for each set `S` that Computation 5 lists, the numbers of lattice points of `k conv S`
(`k = 1, 2, 3`) and of the interior of `k conv S` (`k = 1, 2`) give the values of its Ehrhart polynomial with
respect to the frame lattice at `k = -2, …, 3` and so determine it. -/
theorem poly_six_values_proof (hE2 : EhrhartReciprocity) (j : Fin 39) (S : Set (Pt 4)) (hS : Comp5Input j S) :
    (ehrhartPoly (frameRep j) (convexHull ℝ S)).eval 0 = 1 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 3 →
        (ehrhartPoly (frameRep j) (convexHull ℝ S)).eval (k : ℝ) = latCount (frameRep j) (convexHull ℝ S) k) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 2 →
        (ehrhartPoly (frameRep j) (convexHull ℝ S)).eval (-(k : ℝ)) = intCount (frameRep j) (convexHull ℝ S) k) ∧
      ∀ p : ℝ[X], p.natDegree ≤ 4 → p.eval 0 = 1 →
        (∀ k : ℕ, 1 ≤ k → k ≤ 3 → p.eval (k : ℝ) = latCount (frameRep j) (convexHull ℝ S) k) →
        (∀ k : ℕ, 1 ≤ k → k ≤ 2 → p.eval (-(k : ℝ)) = intCount (frameRep j) (convexHull ℝ S) k) →
        p = ehrhartPoly (frameRep j) (convexHull ℝ S) := by
  obtain ⟨hA, hcard, -⟩ := hS
  obtain ⟨hsub, -, -, -, -, hint0⟩ := hA
  have hfin : S.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hLP : IsLatticePolytope (frameRep j) (convexHull ℝ S) :=
    ⟨hfin.toFinset, by rw [Set.Finite.coe_toFinset]; exact fun x hx => (hsub hx).1,
      by rw [Set.Finite.coe_toFinset]⟩
  have hint : (interior (convexHull ℝ S)).Nonempty := by
    have h0 : (0 : Pt 4) ∈ interior (convexHull ℝ S) ∩ frameRep j := by
      rw [hint0]; exact Set.mem_singleton 0
    exact ⟨0, h0.1⟩
  exact poly_six_values_gen hE2 _ (frameRep_mat_det_ne_zero j) (convexHull ℝ S) hLP hint

/-! ### The include step of the sandwich search (l.369) -/

/-- `conv X ∩ Λ` is `Λ`-saturated. -/
lemma saturated_conv_inter (Λ X : Set (Pt 4)) : Saturated Λ (convexHull ℝ X ∩ Λ) := by
  show convexHull ℝ (convexHull ℝ X ∩ Λ) ∩ Λ = convexHull ℝ X ∩ Λ
  apply Set.Subset.antisymm
  · exact Set.inter_subset_inter_left _ (convexHull_min Set.inter_subset_left (convex_convexHull ℝ X))
  · exact fun x hx => ⟨subset_convexHull ℝ _ hx, hx.2⟩

/-- A frame lattice is symmetric. -/
lemma frame_neg_eq {Λ : Set (Pt 4)} (hΛ : IsFrameLattice Λ) : -Λ = Λ := by
  ext x
  simp only [Set.mem_neg]
  exact ⟨fun h => by simpa using Sandwich.frame_neg_mem hΛ h, Sandwich.frame_neg_mem hΛ⟩

/-- The saturation of a symmetric set in a symmetric `Λ` is symmetric. -/
lemma neg_conv_inter {X Λ : Set (Pt 4)} (hX : -X = X) (hΛ : -Λ = Λ) :
    -(convexHull ℝ X ∩ Λ) = convexHull ℝ X ∩ Λ := by
  rw [Set.inter_neg, ← convexHull_neg, hX, hΛ]

/-- A symmetric set stays symmetric when a pair `±y` is added. -/
lemma symm_union_pair {S : Set (Pt 4)} (hS : -S = S) (y : Pt 4) : -(S ∪ {y, -y}) = S ∪ {y, -y} := by
  ext x
  simp only [Set.mem_neg, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, S6E.neg_mem_symm hS,
    neg_eq_iff_eq_neg, neg_neg]
  tauto

/-- If a set contains every `±e_i`, then `0` is an interior point of its convex hull. -/
lemma zero_mem_interior_conv {Y : Set (Pt 4)} (h : ∀ i, unitVec i ∈ Y) (h' : ∀ i, -unitVec i ∈ Y) :
    (0 : Pt 4) ∈ interior (convexHull ℝ Y) := by
  have hsub : Sandwich.crossPts ⊆ Y := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact h i
    · exact h' i
  have h0 : (0 : Pt 4) ∈ interior (convexHull ℝ Sandwich.crossPts) := by
    rw [Sec5.l1_closed_eq]
    exact Sandwich.zero_mem_interior_l1
  exact interior_mono (convexHull_mono hsub) h0

/-- `S ∪ {v, -v} ⊆ C_4` when `S ⊆ C_4` and `v ∈ C_4`. -/
lemma union_pair_sub_cube {S : Set (Pt 4)} (hS : S ⊆ cube 4) {v : Pt 4} (hv : v ∈ cube 4) :
    S ∪ {v, -v} ⊆ cube 4 := by
  have hvc : ∀ i, |v i| ≤ 1 := hv
  rintro x (hx | rfl | rfl)
  · exact hS hx
  · exact hv
  · intro i
    rw [Pi.neg_apply, abs_neg]
    exact hvc i

/-- l.369: an include step of the sandwich search that is kept (the new lower set lies in `S⁺ ⊆ Λ ∩ C_4`, satisfies
(ii), and has no nonzero point of `Λ` in the interior of its convex hull) keeps the lower set in the family. -/
theorem sandwich_include_member_proof (Λ Sm : Set (Pt 4)) (hΛ : IsFrameLattice Λ) (hSm : InA Λ Sm) (v : Pt 4)
    (hv : v ∈ Λ ∩ cube 4)
    (h2 : ∀ s : Fin 4 → Pt 4, (∀ i, s i ∈ convexHull ℝ (Sm ∪ {v, -v}) ∩ Λ) → |(colMat s).det| ≤ 1)
    (h3 : interior (convexHull ℝ (convexHull ℝ (Sm ∪ {v, -v}) ∩ Λ)) ∩ Λ ⊆ {0}) :
    InA Λ (convexHull ℝ (Sm ∪ {v, -v}) ∩ Λ) := by
  obtain ⟨hSsub, hSsymm, hSunit, -, -, -⟩ := hSm
  have hXcube : Sm ∪ {v, -v} ⊆ cube 4 :=
    union_pair_sub_cube (fun x hx => (hSsub hx).2) hv.2
  have hTs : -(convexHull ℝ (Sm ∪ {v, -v}) ∩ Λ) = convexHull ℝ (Sm ∪ {v, -v}) ∩ Λ :=
    neg_conv_inter (symm_union_pair hSsymm v) (frame_neg_eq hΛ)
  have hunit : ∀ i, unitVec i ∈ convexHull ℝ (Sm ∪ {v, -v}) ∩ Λ := fun i =>
    ⟨subset_convexHull ℝ _ (Or.inl (hSunit i)), Sandwich.frame_unit_mem hΛ i⟩
  refine ⟨fun x hx => ⟨hx.2, convexHull_min hXcube (Sec2.cube_convex 4) hx.1⟩, hTs, hunit, h2,
    saturated_conv_inter Λ _, ?_⟩
  apply Set.Subset.antisymm h3
  rw [Set.singleton_subset_iff]
  exact ⟨zero_mem_interior_conv hunit (fun i => (S6E.neg_mem_symm hTs).2 (hunit i)),
    Sandwich.frame_zero_mem hΛ⟩

/-! ### The dual of a frame lattice (l.326) -/

/-- `⟨Vᵀu, V⁻¹y⟩ = ⟨u, y⟩` for an invertible `V`. -/
lemma dot_transpose_inv (V : Matrix (Fin 4) (Fin 4) ℝ) (hV : V.det ≠ 0) (u y : Pt 4) :
    (V.transpose.mulVec u) ⬝ᵥ (V⁻¹.mulVec y) = u ⬝ᵥ y := by
  rw [Sec5.dot_transpose, Sec5.mulVec_inv_mulVec _ hV]

/-- l.326: `⟨u, Vs⟩ = ⟨Vᵀu, s⟩`, and `Vᵀ ℤ⁴` is the dual lattice of the frame lattice `Λ = V⁻¹ ℤ⁴`. -/
theorem frame_dual_proof (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    (∀ u s : Pt 4, u ⬝ᵥ (colMat v).mulVec s = ((colMat v).transpose.mulVec u) ⬝ᵥ s) ∧
      (fun u => (colMat v).transpose.mulVec u) '' Zn 4 = dualLat (frameLat v) := by
  have hV := Sec5.frame_det_ne_zero P hP v hv
  have hVt : (colMat v).transpose.det ≠ 0 := by rw [Matrix.det_transpose]; exact hV
  refine ⟨fun u s => (Sec5.dot_transpose (colMat v) u s).symm, ?_⟩
  ext w
  constructor
  · rintro ⟨u, ⟨z, rfl⟩, rfl⟩ x ⟨y, rfl⟩
    obtain ⟨m, hm⟩ := Sec5.dot_Zn (n := 4) ⟨z, rfl⟩ ⟨y, rfl⟩
    refine ⟨m, ?_⟩
    show ((colMat v).transpose.mulVec (ofInt z)) ⬝ᵥ ((colMat v)⁻¹.mulVec (ofInt y)) = m
    rw [dot_transpose_inv _ hV]
    exact hm
  · intro hw
    obtain ⟨u, rfl⟩ : ∃ u, (colMat v).transpose.mulVec u = w := ⟨_, Sec5.mulVec_inv_mulVec _ hVt w⟩
    have hint : ∀ i, ∃ m : ℤ, u i = m := fun i => by
      obtain ⟨m, hm⟩ := hw ((colMat v)⁻¹.mulVec (unitVec i))
        ⟨Pi.single i 1, by show (colMat v)⁻¹.mulVec (ofInt (Pi.single i 1)) = _; rw [Sec5.ofInt_single]⟩
      refine ⟨m, ?_⟩
      rw [dot_transpose_inv _ hV, unitVec, dotProduct_single, mul_one] at hm
      exact hm
    choose m hm using hint
    exact ⟨u, ⟨m, funext fun i => (hm i).symm⟩, rfl⟩

end Wills.R280
