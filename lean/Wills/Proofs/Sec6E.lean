/-
Wills/Proofs/Sec6E.lean — proofs for Section 6 of "Wills' (1981) conjecture holds if and only if the dimension is at most 4": Lemma 6.1, the vertex
walk, and the soundness rows of Computation 5 (M antitone, maximal members, sandwich split and pruning).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import Wills.Defs.Basic
import Wills.Defs.Cases
import Wills.Defs.Examples
import Wills.Facts.Basic
import Wills.Checks.Computations
import Wills.Proofs.Sec2

open MeasureTheory Pointwise

namespace Wills.S6E

/-! ### Symmetric sets -/

/-- For a symmetric set, `-x ∈ Q ↔ x ∈ Q`. -/
lemma neg_mem_symm {n : ℕ} {Q : Set (Pt n)} (hsymm : -Q = Q) {x : Pt n} : -x ∈ Q ↔ x ∈ Q := by
  rw [← Set.mem_neg, hsymm]

/-- Removing a pair `±v` from a symmetric set leaves a symmetric set. -/
lemma symm_sdiff_pair {n : ℕ} {Q : Set (Pt n)} (hsymm : -Q = Q) (v : Pt n) :
    -(Q \ {v, -v}) = Q \ {v, -v} := by
  ext x
  simp only [Set.mem_neg, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, neg_mem_symm hsymm,
    neg_eq_iff_eq_neg, neg_neg]
  tauto

/-! ### Lemma 6.1 -/

/-- Lemma 6.1 (i), l.337: if `v` is a vertex of `conv Q`, then `Q' = Q \ {v, -v}` is symmetric and saturated. -/
theorem lem_6_1_i (n : ℕ) (Λ Q : Set (Pt n)) (hQΛ : Q ⊆ Λ) (_hfin : Q.Finite) (hsymm : -Q = Q)
    (hsat : Saturated Λ Q) (v : Pt n) (hv : v ∈ Set.extremePoints ℝ (convexHull ℝ Q)) :
    -(Q \ {v, -v}) = Q \ {v, -v} ∧ Saturated Λ (Q \ {v, -v}) := by
  have hQ'symm := symm_sdiff_pair hsymm v
  refine ⟨hQ'symm, ?_⟩
  -- `v ∉ conv Q'`: `conv Q \ {v}` is convex (v is extreme) and contains `Q'`.
  have hvconv : v ∉ convexHull ℝ (Q \ {v, -v}) := by
    have hcd := ((convex_convexHull ℝ Q).mem_extremePoints_iff_convex_sdiff).1 hv
    have hsub : Q \ {v, -v} ⊆ convexHull ℝ Q \ {v} := by
      intro x hx
      refine ⟨subset_convexHull ℝ Q hx.1, ?_⟩
      intro hxv
      rw [Set.mem_singleton_iff] at hxv
      exact hx.2 (by rw [hxv]; exact Set.mem_insert _ _)
    intro hvc
    exact (convexHull_min hsub hcd.2 hvc).2 (Set.mem_singleton v)
  -- `-v ∉ conv Q'`, since `conv Q'` is symmetric.
  have hnvconv : -v ∉ convexHull ℝ (Q \ {v, -v}) := by
    intro h
    apply hvconv
    have h2 : v ∈ -convexHull ℝ (Q \ {v, -v}) := by rw [Set.mem_neg]; exact h
    rwa [← convexHull_neg, hQ'symm] at h2
  have hsat' : convexHull ℝ Q ∩ Λ = Q := hsat
  show convexHull ℝ (Q \ {v, -v}) ∩ Λ = Q \ {v, -v}
  apply Set.Subset.antisymm
  · rintro x ⟨hxc, hxΛ⟩
    have hxQ : x ∈ Q := hsat'.subset ⟨convexHull_mono Set.sdiff_subset hxc, hxΛ⟩
    refine ⟨hxQ, ?_⟩
    rintro (rfl | rfl)
    · exact hvconv hxc
    · exact hnvconv hxc
  · intro x hx
    exact ⟨subset_convexHull ℝ _ hx, hQΛ hx.1⟩

/-- Lemma 6.1 (ii), l.338: if `S ⊊ Q` is symmetric and saturated, then some vertex `v` of `conv Q` is not in `S`,
and `S ⊆ Q \ {v, -v}`. -/
theorem lem_6_1_ii (n : ℕ) (Λ Q : Set (Pt n)) (hQΛ : Q ⊆ Λ) (hfin : Q.Finite) (_hsymm : -Q = Q)
    (_hsat : Saturated Λ Q) (S : Set (Pt n)) (hSQ : S ⊂ Q) (hSsymm : -S = S) (hSsat : Saturated Λ S) :
    ∃ v ∈ Set.extremePoints ℝ (convexHull ℝ Q), v ∉ S ∧ S ⊆ Q \ {v, -v} := by
  have hSfin : S.Finite := hfin.subset hSQ.subset
  have hSsat' : convexHull ℝ S ∩ Λ = S := hSsat
  -- Krein-Milman: if every vertex of `conv Q` were in `conv S`, then `Q ⊆ conv S ∩ Λ = S`.
  have hex : ∃ v ∈ Set.extremePoints ℝ (convexHull ℝ Q), v ∉ convexHull ℝ S := by
    by_contra hcon
    push Not at hcon
    have hKM := closure_convexHull_extremePoints (hfin.isCompact_convexHull ℝ) (convex_convexHull ℝ Q)
    have hcl : closure (convexHull ℝ ((convexHull ℝ Q).extremePoints ℝ)) ⊆ convexHull ℝ S :=
      closure_minimal (convexHull_min (fun v hv => hcon v hv) (convex_convexHull ℝ S))
        (hSfin.isClosed_convexHull ℝ)
    rw [hKM] at hcl
    obtain ⟨x, hxQ, hxS⟩ := Set.exists_of_ssubset hSQ
    exact hxS (hSsat'.subset ⟨hcl (subset_convexHull ℝ Q hxQ), hQΛ hxQ⟩)
  obtain ⟨v, hvext, hvS⟩ := hex
  have hvS' : v ∉ S := fun h => hvS (subset_convexHull ℝ S h)
  refine ⟨v, hvext, hvS', ?_⟩
  intro x hx
  refine ⟨hSQ.subset hx, ?_⟩
  rintro (rfl | rfl)
  · exact hvS' hx
  · exact hvS' ((neg_mem_symm hSsymm).1 hx)

/-! ### The walk -/

/-- The walk of `walk_reach`, by strong induction on `#Q`. -/
lemma walk_aux (n : ℕ) (Λ S : Set (Pt n)) (hSsymm : -S = S) (hSsat : Saturated Λ S) (N : ℕ) :
    ∀ Q : Set (Pt n), Q.ncard = N → Q ⊆ Λ → Q.Finite → -Q = Q → Saturated Λ Q → S ⊆ Q →
      Relation.ReflTransGen (fun A A' : Set (Pt n) => S ⊆ A' ∧ -A' = A' ∧ Saturated Λ A' ∧
        ∃ v ∈ Set.extremePoints ℝ (convexHull ℝ A), A' = A \ {v, -v}) Q S := by
  refine Nat.strong_induction_on N ?_
  intro N ih Q hN hQΛ hfin hsymm hsat hSQ
  by_cases hEq : S = Q
  · subst hEq
    exact Relation.ReflTransGen.refl
  · have hss : S ⊂ Q := hSQ.ssubset_of_ne hEq
    obtain ⟨v, hvext, _, hSQ'⟩ := lem_6_1_ii n Λ Q hQΛ hfin hsymm hsat S hss hSsymm hSsat
    obtain ⟨hQ'symm, hQ'sat⟩ := lem_6_1_i n Λ Q hQΛ hfin hsymm hsat v hvext
    have hvQ : v ∈ Q := extremePoints_convexHull_subset hvext
    have hlt : (Q \ {v, -v}).ncard < N := by
      rw [← hN]
      refine Set.ncard_lt_ncard ?_ hfin
      rw [Set.ssubset_iff_of_subset Set.sdiff_subset]
      exact ⟨v, hvQ, fun h => h.2 (Set.mem_insert v _)⟩
    refine Relation.ReflTransGen.head ⟨hSQ', hQ'symm, hQ'sat, v, hvext, rfl⟩ ?_
    exact ih _ hlt (Q \ {v, -v}) rfl (Set.sdiff_subset.trans hQΛ) (hfin.subset Set.sdiff_subset) hQ'symm hQ'sat
      hSQ'

/-- l.332, l.346: every saturated symmetric `S ⊆ Q` is reached from `Q` by deleting pairs of opposite vertices
through saturated symmetric sets that contain `S` (so a search that stops at 31 points misses no set with at least
31 points). -/
theorem walk_reach (n : ℕ) (Λ Q : Set (Pt n)) (hQΛ : Q ⊆ Λ) (hfin : Q.Finite) (hsymm : -Q = Q)
    (hsat : Saturated Λ Q) (S : Set (Pt n)) (hSQ : S ⊆ Q) (hSsymm : -S = S) (hSsat : Saturated Λ S) :
    Relation.ReflTransGen (fun A A' : Set (Pt n) => S ⊆ A' ∧ -A' = A' ∧ Saturated Λ A' ∧
      ∃ v ∈ Set.extremePoints ℝ (convexHull ℝ A), A' = A \ {v, -v}) Q S :=
  walk_aux n Λ S hSsymm hSsat Q.ncard Q rfl hQΛ hfin hsymm hsat hSQ

/-! ### Computation 5: `M` and `r` -/

/-- Computation 5, l.367: `M` reverses inclusion, so a subset of a set `Q'` with `r(Q') = 4` also has `r = 4`. -/
theorem M_antitone (Λ Q Q' : Set (Pt 4)) (h : Q ⊆ Q') :
    MS Λ Q' ⊆ MS Λ Q ∧ rS Λ Q' ≤ rS Λ Q ∧ (rS Λ Q' = 4 → rS Λ Q = 4) := by
  have h1 : MS Λ Q' ⊆ MS Λ Q := fun w hw => ⟨hw.1, fun s hs => hw.2 s (h hs)⟩
  have h2 : rS Λ Q' ≤ rS Λ Q := by
    unfold rS
    exact Submodule.finrank_mono (Submodule.span_mono h1)
  have h3 : rS Λ Q ≤ 4 := by
    unfold rS
    calc Module.finrank ℝ (Submodule.span ℝ (MS Λ Q)) ≤ Module.finrank ℝ (Pt 4) := Submodule.finrank_le _
      _ = 4 := Module.finrank_fin_fun ℝ
  exact ⟨h1, h2, fun h4 => by omega⟩

/-! ### Computation 5: maximal members -/

/-- The points of `lat A⁻¹` in a compact set are finitely many (if `det A = 0`, then `A⁻¹ = 0` and `lat 0 = {0}`). -/
lemma lat_inv_inter_finite {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {K : Set (Pt n)} (hK : IsCompact K) :
    (K ∩ lat A⁻¹).Finite := by
  by_cases hA : IsUnit A.det
  · have hinv : (A⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det_iff.2 hA).ne_zero
    exact Sec2.lat_inter_finite A⁻¹ hinv hK
  · rw [Matrix.nonsing_inv_apply_not_isUnit A hA]
    refine (Set.finite_singleton (0 : Pt n)).subset ?_
    rintro x ⟨_, z, rfl⟩
    simp

/-- Each representative frame lattice meets the cube `C_4` in finitely many points. -/
lemma frameRep_inter_finite (j : Fin 39) : (frameRep j ∩ cube 4).Finite := by
  rw [Set.inter_comm]
  exact lat_inv_inter_finite _ (Sec2.cube_compact 4)

/-- Computation 5, l.367: every `S ∈ A(Λ)` with `r(S) ≤ 3` lies in a maximal member `Q` of `A(Λ)` with `r(Q) ≤ 3`,
and `r(Q) ≤ r(S)`. -/
theorem comp5_maximal (j : Fin 39) (S : Set (Pt 4)) (hS : InA (frameRep j) S) (hr : rS (frameRep j) S ≤ 3) :
    ∃ Q, InA (frameRep j) Q ∧ S ⊆ Q ∧ rS (frameRep j) Q ≤ rS (frameRep j) S ∧
      ∀ Q', InA (frameRep j) Q' → rS (frameRep j) Q' ≤ 3 → Q ⊆ Q' → Q' = Q := by
  let F : Set (Set (Pt 4)) := {Q | InA (frameRep j) Q ∧ S ⊆ Q ∧ rS (frameRep j) Q ≤ 3}
  have hFfin : F.Finite :=
    (frameRep_inter_finite j).finite_subsets.subset (fun Q hQ => hQ.1.1)
  have hSF : S ∈ F := ⟨hS, subset_rfl, hr⟩
  obtain ⟨Q, hQF, hmax⟩ := hFfin.exists_maximal ⟨S, hSF⟩
  refine ⟨Q, hQF.1, hQF.2.1, (M_antitone (frameRep j) S Q hQF.2.1).2.1, ?_⟩
  intro Q' hQ'A hQ'r hQQ'
  exact le_antisymm (hmax ⟨hQ'A, hQF.2.1.trans hQQ', hQ'r⟩ hQQ') hQQ'

/-! ### Computation 5: the sandwich search -/

/-- Computation 5, l.369: every saturated symmetric set between `S⁻` and `S⁺` lies in exactly one branch: it
avoids `±v` and lies in `S⁺ \ {±v}`, or it contains `±v` and `conv(S⁻ ∪ {±v}) ∩ Λ`.
(The hypothesis `v ∈ Λ` is not needed for this direction; it is kept, unused, to match the row.) -/
theorem sandwich_split (Λ Sm Sp S : Set (Pt 4)) (v : Pt 4) (hSm : Sm ⊆ S) (hSp : S ⊆ Sp) (hsat : Saturated Λ S)
    (hsymm : -S = S) (_hv : v ∈ Λ) :
    (v ∉ S ∧ S ⊆ Sp \ {v, -v}) ∨ (v ∈ S ∧ convexHull ℝ (Sm ∪ {v, -v}) ∩ Λ ⊆ S) := by
  by_cases hvS : v ∈ S
  · right
    refine ⟨hvS, ?_⟩
    have hnv : -v ∈ S := (neg_mem_symm hsymm).2 hvS
    have hsub : Sm ∪ {v, -v} ⊆ S :=
      Set.union_subset hSm (Set.insert_subset hvS (Set.singleton_subset_iff.2 hnv))
    have hsat' : convexHull ℝ S ∩ Λ = S := hsat
    calc convexHull ℝ (Sm ∪ {v, -v}) ∩ Λ ⊆ convexHull ℝ S ∩ Λ :=
          Set.inter_subset_inter_left _ (convexHull_mono hsub)
      _ = S := hsat'
  · left
    refine ⟨hvS, fun x hx => ⟨hSp hx, ?_⟩⟩
    rintro (rfl | rfl)
    · exact hvS hx
    · exact hvS ((neg_mem_symm hsymm).1 hx)

/-- Computation 5, l.369: the pruning of the sandwich search is sound: no `S ∈ A(Λ)` contains a set `T` that violates
(ii) or has a nonzero point of `Λ` in the interior of its convex hull; a point `x` that breaks (ii) together with
`T` is in no `S ∈ A(Λ)` containing `T`; and a set `S ⊆ S⁺` has `#S < 31` if `#S⁺ < 31` and `r(S) = 4` if
`r(S⁺) = 4`. -/
theorem sandwich_prune (Λ T S Sp : Set (Pt 4)) (hS : InA Λ S) (hTS : T ⊆ S) :
    (∀ s : Fin 4 → Pt 4, (∀ i, s i ∈ T) → |(colMat s).det| ≤ 1) ∧
      interior (convexHull ℝ T) ∩ Λ ⊆ {0} ∧
      (∀ x, ∀ s : Fin 4 → Pt 4, (∀ i, s i ∈ insert x T) → 1 < |(colMat s).det| → x ∉ S) ∧
      (S ⊆ Sp → Sp.Finite → Sp.ncard < 31 → S.ncard < 31) ∧ (S ⊆ Sp → rS Λ Sp = 4 → rS Λ S = 4) := by
  obtain ⟨_, _, _, hdet, _, hint⟩ := hS
  refine ⟨fun s hs => hdet s (fun i => hTS (hs i)), ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hint]
    exact ⟨interior_mono (convexHull_mono hTS) hx.1, hx.2⟩
  · intro x s hs hlt hxS
    have hsS : ∀ i, s i ∈ S := by
      intro i
      rcases hs i with h | h
      · rw [h]; exact hxS
      · exact hTS h
    linarith [hdet s hsS]
  · intro hsub hfin hlt
    exact lt_of_le_of_lt (Set.ncard_le_ncard hsub hfin) hlt
  · intro hsub h4
    exact (M_antitone Λ S Sp hsub).2.2 h4

end Wills.S6E
