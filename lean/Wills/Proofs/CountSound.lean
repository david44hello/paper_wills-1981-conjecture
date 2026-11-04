/-
Wills/Proofs/CountSound.lean — Soundness of the kernel checks of Wills/Proofs/CountData.lean: integer lists as points
of `ℝ⁵`, facet inequalities on `W`, convex-combination certificates, the box, and counting.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.CountData

open MeasureTheory Pointwise

namespace Wills.Count

/-- The point of `ℝ⁵` with the coordinates of an integer list. -/
def toPt (l : List ℤ) : Pt 5 := fun i => ((l.getD i.val 0 : ℤ) : ℝ)

/-- The real dot product of an integer list with a point of `ℝ⁵`. -/
def rdot (u : List ℤ) (x : Pt 5) : ℝ := ∑ i : Fin 5, ((u.getD i.val 0 : ℤ) : ℝ) * x i

lemma toPt_ofFn (p : Fin 5 → ℤ) : toPt (List.ofFn p) = ofInt p := by
  funext i
  fin_cases i <;> simp [toPt, ofInt]

lemma length_eq_five {l : List ℤ} (h : l.length = 5) : ∃ a b c d e, l = [a, b, c, d, e] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, l⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, e, rfl⟩

lemma dotL_cast (u x : List ℤ) (hu : u.length = 5) (hx : x.length = 5) :
    ((dotL u x : ℤ) : ℝ) = rdot u (toPt x) := by
  obtain ⟨a, b, c, d, e, rfl⟩ := length_eq_five hu
  obtain ⟨p, q, r, s, t, rfl⟩ := length_eq_five hx
  simp [dotL, rdot, toPt, Fin.sum_univ_five]
  ring

lemma rdot_isLinear (u : List ℤ) : IsLinearMap ℝ (rdot u) := by
  constructor
  · intro x y
    simp only [rdot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  · intro c x
    simp only [rdot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

lemma toPt_add (a b : List ℤ) (ha : a.length = 5) (hb : b.length = 5) :
    toPt (List.zipWith (· + ·) a b) = toPt a + toPt b := by
  obtain ⟨a0, a1, a2, a3, a4, rfl⟩ := length_eq_five ha
  obtain ⟨b0, b1, b2, b3, b4, rfl⟩ := length_eq_five hb
  funext i
  fin_cases i <;> simp [toPt]

lemma toPt_scale (n : ℤ) (a : List ℤ) (ha : a.length = 5) :
    toPt (a.map (fun c => n * c)) = (n : ℝ) • toPt a := by
  obtain ⟨a0, a1, a2, a3, a4, rfl⟩ := length_eq_five ha
  funext i
  fin_cases i <;> simp [toPt]

lemma toPt_mem_Zn (l : List ℤ) : toPt l ∈ Zn 5 := ⟨fun i => l.getD i.val 0, rfl⟩

lemma toPt_injOn : Set.InjOn toPt {l : List ℤ | l.length = 5} := by
  intro a ha b hb h
  obtain ⟨a0, a1, a2, a3, a4, rfl⟩ := length_eq_five ha
  obtain ⟨b0, b1, b2, b3, b4, rfl⟩ := length_eq_five hb
  have e := fun i => congrFun h i
  have h0 := e 0; have h1 := e 1; have h2 := e 2; have h3 := e 3; have h4 := e 4
  simp [toPt] at h0 h1 h2 h3 h4
  simp [h0, h1, h2, h3, h4]

/-! ### Vertices of `W` -/

lemma mem_wVertsL_length {v : List ℤ} (hv : v ∈ wVertsL) : v.length = 5 := by
  simp only [wVertsL, List.mem_append, List.mem_map] at hv
  rcases hv with ⟨p, _, rfl⟩ | ⟨p, _, rfl⟩ <;> simp

lemma toPt_mem_wPts {v : List ℤ} (hv : v ∈ wVertsL) : toPt v ∈ wPts := by
  simp only [wVertsL, List.mem_append, List.mem_map] at hv
  rcases hv with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact ⟨p, hp, Or.inl (toPt_ofFn p)⟩
  · refine ⟨p, hp, Or.inr ?_⟩
    rw [toPt_ofFn]
    funext i
    simp [ofInt]

lemma wPts_eq : wPts = toPt '' {v | v ∈ wVertsL} := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl | rfl⟩
    · exact ⟨List.ofFn p, List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩), toPt_ofFn p⟩
    · refine ⟨List.ofFn (-p), List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩), ?_⟩
      rw [toPt_ofFn]
      funext i
      simp [ofInt]
  · rintro ⟨v, hv, rfl⟩
    exact toPt_mem_wPts hv

lemma W_convex : Convex ℝ W := convex_convexHull ℝ _

lemma W_nonempty : W.Nonempty := by
  refine ⟨ofInt wHalf.head!, subset_convexHull ℝ _ ⟨wHalf.head!, ?_, Or.inl rfl⟩⟩
  simp [wHalf]

/-! ### Facets -/

lemma facet_le_on_W (hv : facetsValid = true) {f : List ℤ × ℤ} (hf : f ∈ WData.facets) {x : Pt 5}
    (hx : x ∈ W) : rdot f.1 x ≤ f.2 := by
  have hall := List.all_eq_true.1 hv f hf
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hall
  obtain ⟨hlen, hverts⟩ := hall
  have hsub : wPts ⊆ {y | rdot f.1 y ≤ f.2} := by
    rw [wPts_eq]
    rintro _ ⟨v, hv', rfl⟩
    have := hverts v hv'
    show rdot f.1 (toPt v) ≤ f.2
    rw [← dotL_cast _ _ hlen (mem_wVertsL_length hv')]
    exact_mod_cast this
  exact convexHull_min hsub (convex_halfSpace_le (rdot_isLinear f.1) _) hx

lemma facet_le_on_smul (hv : facetsValid = true) {f : List ℤ × ℤ} (hf : f ∈ WData.facets) (k : ℕ)
    {x : Pt 5} (hx : x ∈ (k : ℝ) • W) : rdot f.1 x ≤ k * f.2 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [(rdot_isLinear f.1).map_smul]
  exact mul_le_mul_of_nonneg_left (facet_le_on_W hv hf hy) (Nat.cast_nonneg k)

/-! ### Convex-combination certificates -/

lemma combo_sound (pairs : List (ℕ × ℕ)) (hidx : ∀ p ∈ pairs, p.1 < 50) :
    (combo pairs).length = 5 ∧ toPt (combo pairs) ∈ (((pairs.map Prod.snd).sum : ℕ) : ℝ) • W := by
  induction pairs with
  | nil =>
    refine ⟨rfl, ?_⟩
    simp only [List.map_nil, List.sum_nil, Nat.cast_zero, Set.zero_smul_set W_nonempty]
    show toPt [0, 0, 0, 0, 0] ∈ (0 : Set (Pt 5))
    rw [Set.mem_zero]
    funext i
    fin_cases i <;> simp [toPt]
  | cons p ps ih =>
    obtain ⟨hlen, hmem⟩ := ih (fun q hq => hidx q (List.mem_cons_of_mem _ hq))
    have hp : p.1 < wVertsL.length := by
      have := hidx p List.mem_cons_self
      simpa [wVertsL, wHalf] using this
    have hvmem : wVertsL.getD p.1 [] ∈ wVertsL := by
      rw [List.getD_eq_getElem _ _ hp]
      exact List.getElem_mem hp
    have hvlen := mem_wVertsL_length hvmem
    have hslen : ((wVertsL.getD p.1 []).map (fun c => (p.2 : ℤ) * c)).length = 5 := by
      rw [List.length_map, hvlen]
    have hcombo : combo (p :: ps) =
        List.zipWith (· + ·) (combo ps) ((wVertsL.getD p.1 []).map (fun c => (p.2 : ℤ) * c)) := rfl
    refine ⟨by rw [hcombo, List.length_zipWith, hlen, hslen]; rfl, ?_⟩
    rw [hcombo, toPt_add _ _ hlen hslen, toPt_scale _ _ hvlen]
    have hv : toPt (wVertsL.getD p.1 []) ∈ W := subset_convexHull ℝ _ (toPt_mem_wPts hvmem)
    have : ((((p :: ps).map Prod.snd).sum : ℕ) : ℝ) = (((ps.map Prod.snd).sum : ℕ) : ℝ) + (p.2 : ℝ) := by
      simp [add_comm]
    rw [this, W_convex.add_smul (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact Set.add_mem_add hmem (Set.smul_mem_smul_set (by exact_mod_cast hv))

lemma cert1Ok_sound {z : List ℤ} {c : List (ℕ × ℕ) × ℕ} (h : cert1Ok z c = true) :
    z.length = 5 ∧ toPt z ∈ W := by
  simp only [cert1Ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hN, hsum⟩, hidx⟩, hlen⟩, hz⟩ := h
  refine ⟨hlen, ?_⟩
  obtain ⟨_, hmem⟩ := combo_sound c.1 hidx
  rw [hsum, ← hz, toPt_scale _ _ hlen] at hmem
  have hN' : ((c.2 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show ((c.2 : ℤ) : ℝ) = ((c.2 : ℕ) : ℝ) by simp] at hmem hN'
  exact (Set.smul_mem_smul_set_iff₀ hN' _ _).1 hmem

/-! ### The box -/

lemma mem_rng {k : ℕ} {a : ℤ} : a ∈ rng k ↔ -(k : ℤ) ≤ a ∧ a ≤ k := by
  unfold rng
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi
    omega
  · intro h
    exact ⟨(a + k).toNat, List.mem_range.2 (by omega), by omega⟩

lemma ofFn_mem_boxL {k : ℕ} {p : Fin 5 → ℤ} (hp : ∀ i, -(k : ℤ) ≤ p i ∧ p i ≤ k) :
    List.ofFn p ∈ boxL k := by
  simp only [boxL, List.mem_flatMap, List.mem_map]
  refine ⟨p 0, mem_rng.2 (hp 0), p 1, mem_rng.2 (hp 1), p 2, mem_rng.2 (hp 2), p 3, mem_rng.2 (hp 3), p 4,
    mem_rng.2 (hp 4), ?_⟩
  simp [List.ofFn_succ]

lemma mem_boxL_length {k : ℕ} {z : List ℤ} (hz : z ∈ boxL k) : z.length = 5 := by
  simp only [boxL, List.mem_flatMap, List.mem_map] at hz
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := hz
  rfl

end Wills.Count
