/-
Wills/Proofs/CountW.lean — The lattice-point counts of `W` (Theorem 1.3, l.218-220), from the kernel-checked
certificates: `G(W) = 117`, `#(2W ∩ ℤ⁵) = 1815`, `int(2W) ∩ ℤ⁵ = {-1,0,1}⁵` and `#(int(2W) ∩ ℤ⁵) = 243`.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.CountSound
import Wills.Proofs.Sec2

open MeasureTheory Pointwise

namespace Wills.Count

/-! ### Kernel checks -/

set_option maxRecDepth 100000 in
lemma facetsValid_true : facetsValid = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma cert1All_true : cert1All = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma cert3All_true : cert3All = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma insideL1_length : (insideL 1).length = 117 := by decide +kernel

set_option maxRecDepth 100000 in
lemma boxL1_length : (boxL 1).length = 243 := by decide +kernel

set_option maxRecDepth 100000 in
lemma boxL1_chain : (boxL 1).IsChain (· < ·) := by decide +kernel

set_option maxRecDepth 100000 in
lemma boxL2_chain : (boxL 2).IsChain (· < ·) := by decide +kernel

lemma wHalf_bounds : ∀ p ∈ wHalf, ∀ i, -1 ≤ p i ∧ p i ≤ 1 := by decide +kernel

/-! ### Lists -/

lemma nodup_of_chain {L : List (List ℤ)} (h : L.IsChain (· < ·)) : L.Nodup := by
  have hp := List.isChain_iff_pairwise.1 h
  exact hp.imp (fun {a b} hab heq => by subst heq; exact List.lt_irrefl a hab)

lemma forall_zip {α β : Type} {L : List α} {C : List β} {ok : α → β → Bool} (hlen : L.length = C.length)
    (h : (L.zip C).all (fun q => ok q.1 q.2) = true) : ∀ z ∈ L, ∃ c, ok z c = true := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  refine ⟨C[i]'(hlen ▸ hi), ?_⟩
  have hmem : (L[i], C[i]'(hlen ▸ hi)) ∈ L.zip C := by
    have hi' : i < (L.zip C).length := by simp [hi, ← hlen]
    have := List.getElem_mem hi'
    simpa [List.getElem_zip] using this
  exact List.all_eq_true.1 h _ hmem

lemma ncard_toPt_image (L : List (List ℤ)) (hL : ∀ z ∈ L, z.length = 5) (hnd : L.Nodup) :
    (toPt '' {z | z ∈ L}).ncard = L.length := by
  have himg := Set.InjOn.ncard_image (f := toPt) (s := {z : List ℤ | z ∈ L})
    (toPt_injOn.mono fun z hz => hL z hz)
  rw [himg]
  rw [show {z | z ∈ L} = (↑L.toFinset : Set (List ℤ)) by ext; simp, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

lemma mem_insideL {k : ℕ} {z : List ℤ} : z ∈ insideL k ↔
    z ∈ boxL k ∧ ∀ f ∈ WData.facets, dotL f.1 z ≤ k * f.2 := by
  simp [insideL, List.mem_filter, List.all_eq_true]

/-! ### `W` and the cube -/

lemma wPts_sub_cube : wPts ⊆ cube 5 := by
  rintro x ⟨p, hp, rfl | rfl⟩ <;> intro i <;> have h := wHalf_bounds p hp i
  · simp only [ofInt]
    rw [abs_le]
    constructor <;> exact_mod_cast (by omega : _)
  · simp only [ofInt, Pi.neg_apply, abs_neg]
    rw [abs_le]
    constructor <;> exact_mod_cast (by omega : _)

lemma W_sub_cube : W ⊆ cube 5 := convexHull_min wPts_sub_cube (Sec2.cube_convex 5)

/-! ### Lattice points of `kW` -/

lemma facet_length {f : List ℤ × ℤ} (hf : f ∈ WData.facets) : f.1.length = 5 := by
  have hall := List.all_eq_true.1 facetsValid_true f hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hall
  exact hall.1

lemma smulW_inter_eq (k : ℕ) (hcert : ∀ z ∈ insideL k, toPt z ∈ (k : ℝ) • W) :
    (k : ℝ) • W ∩ Zn 5 = toPt '' {z | z ∈ insideL k} := by
  ext x
  constructor
  · rintro ⟨hx, p, rfl⟩
    have hbox : ∀ i, -(k : ℤ) ≤ p i ∧ p i ≤ k := by
      intro i
      have hc : ofInt p ∈ (k : ℝ) • cube 5 := Set.smul_set_mono W_sub_cube hx
      rw [Sec2.smul_cube (Nat.cast_nonneg k)] at hc
      have := abs_le.1 (hc i)
      simp only [ofInt] at this
      exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
    refine ⟨List.ofFn p, mem_insideL.2 ⟨ofFn_mem_boxL hbox, fun f hf => ?_⟩, toPt_ofFn p⟩
    have h := facet_le_on_smul facetsValid_true hf k hx
    rw [← toPt_ofFn, ← dotL_cast _ _ (facet_length hf) (by simp)] at h
    exact_mod_cast h
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hcert z hz, toPt_mem_Zn z⟩

lemma insideL_nodup1 : (insideL 1).Nodup := (nodup_of_chain boxL1_chain).filter _

lemma insideL_nodup2 : (insideL 2).Nodup := (nodup_of_chain boxL2_chain).filter _

lemma insideL_length5 {k : ℕ} {z : List ℤ} (hz : z ∈ insideL k) : z.length = 5 :=
  mem_boxL_length (mem_insideL.1 hz).1

lemma insideL1_in_W : ∀ z ∈ insideL 1, toPt z ∈ W := by
  have hall : (insideL 1).length = WData.cert1.length ∧
      ((insideL 1).zip WData.cert1).all (fun q => cert1Ok q.1 q.2) = true := by
    have := cert1All_true
    simp only [cert1All, Bool.and_eq_true, beq_iff_eq] at this
    exact this
  intro z hz
  obtain ⟨c, hc⟩ := forall_zip hall.1 hall.2 z hz
  exact (cert1Ok_sound hc).2

/-- `G(W) = 117` (l.218). -/
theorem w_G_proof : G (Zn 5) W = 117 := by
  have h := smulW_inter_eq 1 (fun z hz => by rw [Nat.cast_one, one_smul]; exact insideL1_in_W z hz)
  rw [Nat.cast_one, one_smul] at h
  unfold G
  rw [h, ncard_toPt_image _ (fun z hz => insideL_length5 hz) insideL_nodup1, insideL1_length]

end Wills.Count
