/-
Wills/Proofs/Count4.lean — lattice-point counts of a polytope in `ℝ⁴` given by a list of integer vertices, from
kernel-checked certificates: facet inequalities, coordinate bounds, convex-combination certificates for the lattice
points of `kP`, and interior certificates (a small cube around each interior lattice point of `kP` lies in `kP`).
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.CountW
import Wills.Proofs.Sec2

open MeasureTheory Pointwise

namespace Wills.Count4

open Wills.Count (dotL rng mem_rng forall_zip nodup_of_chain)

/-! ### Integer lists as points of `ℝ⁴` -/

/-- The point of `ℝ⁴` with the coordinates of an integer list. -/
def toPt4 (l : List ℤ) : Pt 4 := fun i => ((l.getD i.val 0 : ℤ) : ℝ)

/-- The real dot product of an integer list with a point of `ℝ⁴`. -/
def rdot4 (u : List ℤ) (x : Pt 4) : ℝ := ∑ i : Fin 4, ((u.getD i.val 0 : ℤ) : ℝ) * x i

lemma toPt4_ofFn (p : Fin 4 → ℤ) : toPt4 (List.ofFn p) = ofInt p := by
  funext i
  fin_cases i <;> simp [toPt4, ofInt]

lemma length_eq_four {l : List ℤ} (h : l.length = 4) : ∃ a b c d, l = [a, b, c, d] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a, b, c, d, rfl⟩

lemma dotL_cast4 (u x : List ℤ) (hu : u.length = 4) (hx : x.length = 4) :
    ((dotL u x : ℤ) : ℝ) = rdot4 u (toPt4 x) := by
  obtain ⟨a, b, c, d, rfl⟩ := length_eq_four hu
  obtain ⟨p, q, r, s, rfl⟩ := length_eq_four hx
  simp [dotL, rdot4, toPt4, Fin.sum_univ_four]
  ring

lemma rdot4_isLinear (u : List ℤ) : IsLinearMap ℝ (rdot4 u) := by
  constructor
  · intro x y
    simp only [rdot4, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  · intro c x
    simp only [rdot4, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

lemma toPt4_add (a b : List ℤ) (ha : a.length = 4) (hb : b.length = 4) :
    toPt4 (List.zipWith (· + ·) a b) = toPt4 a + toPt4 b := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := length_eq_four ha
  obtain ⟨b0, b1, b2, b3, rfl⟩ := length_eq_four hb
  funext i
  fin_cases i <;> simp [toPt4]

lemma toPt4_scale (n : ℤ) (a : List ℤ) (ha : a.length = 4) :
    toPt4 (a.map (fun c => n * c)) = (n : ℝ) • toPt4 a := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := length_eq_four ha
  funext i
  fin_cases i <;> simp [toPt4]

lemma toPt4_mem_Zn (l : List ℤ) : toPt4 l ∈ Zn 4 := ⟨fun i => l.getD i.val 0, rfl⟩

lemma toPt4_injOn : Set.InjOn toPt4 {l : List ℤ | l.length = 4} := by
  intro a ha b hb h
  obtain ⟨a0, a1, a2, a3, rfl⟩ := length_eq_four ha
  obtain ⟨b0, b1, b2, b3, rfl⟩ := length_eq_four hb
  have e := fun i => congrFun h i
  have h0 := e 0; have h1 := e 1; have h2 := e 2; have h3 := e 3
  simp [toPt4] at h0 h1 h2 h3
  simp [h0, h1, h2, h3]

lemma ncard_toPt4_image (L : List (List ℤ)) (hL : ∀ z ∈ L, z.length = 4) (hnd : L.Nodup) :
    (toPt4 '' {z | z ∈ L}).ncard = L.length := by
  have himg := Set.InjOn.ncard_image (f := toPt4) (s := {z : List ℤ | z ∈ L})
    (toPt4_injOn.mono fun z hz => hL z hz)
  rw [himg]
  rw [show {z | z ∈ L} = (↑L.toFinset : Set (List ℤ)) by ext; simp, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

/-! ### The polytope of a vertex list; boxes and facet filters -/

/-- The polytope `conv V` of a list `V` of integer vertices. -/
def polyL (V : List (List ℤ)) : Set (Pt 4) := convexHull ℝ (toPt4 '' {v | v ∈ V})

/-- The box `∏_i {-k B_i, …, k B_i}` in lexicographic order. -/
def box4 (B : List ℕ) (k : ℕ) : List (List ℤ) :=
  (rng (k * B.getD 0 0)).flatMap fun a => (rng (k * B.getD 1 0)).flatMap fun b =>
    (rng (k * B.getD 2 0)).flatMap fun c => (rng (k * B.getD 3 0)).map fun d => [a, b, c, d]

/-- The points of the box that satisfy every facet inequality `⟨u, z⟩ ≤ k b` of `kP`. -/
def insideF (F : List (List ℤ × ℤ)) (B : List ℕ) (k : ℕ) : List (List ℤ) :=
  (box4 B k).filter fun z => F.all fun f => decide (dotL f.1 z ≤ k * f.2)

/-- The points of the box that satisfy every facet inequality of `kP` strictly. -/
def strictF (F : List (List ℤ × ℤ)) (B : List ℕ) (k : ℕ) : List (List ℤ) :=
  (box4 B k).filter fun z => F.all fun f => decide (dotL f.1 z < k * f.2)

/-- The data are consistent: every vertex has length 4 and `|v_i| ≤ B_i`; every facet normal `u` has length 4,
`⟨u, u⟩ > 0`, and `⟨u, v⟩ ≤ b` at every vertex `v`. -/
def dataValid (V : List (List ℤ)) (F : List (List ℤ × ℤ)) (B : List ℕ) : Bool :=
  V.all (fun v => v.length == 4 && (List.finRange 4).all fun i => decide (|v.getD i.val 0| ≤ (B.getD i.val 0 : ℤ))) &&
    F.all (fun f => f.1.length == 4 && decide (0 < dotL f.1 f.1) && V.all fun v => decide (dotL f.1 v ≤ f.2))

lemma dataValid_vert {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    {v : List ℤ} (h : v ∈ V) : v.length = 4 ∧ ∀ i : Fin 4, |v.getD i.val 0| ≤ (B.getD i.val 0 : ℤ) := by
  unfold dataValid at hv
  simp only [Bool.and_eq_true] at hv
  have h1 := List.all_eq_true.1 hv.1 v h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h1
  exact ⟨h1.1, fun i => h1.2 i (List.mem_finRange i)⟩

lemma dataValid_facet {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    {f : List ℤ × ℤ} (h : f ∈ F) : f.1.length = 4 ∧ 0 < dotL f.1 f.1 ∧ ∀ v ∈ V, dotL f.1 v ≤ f.2 := by
  unfold dataValid at hv
  simp only [Bool.and_eq_true] at hv
  have h1 := List.all_eq_true.1 hv.2 f h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h1
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

lemma mem_polyL_vert {V : List (List ℤ)} {v : List ℤ} (hv : v ∈ V) : toPt4 v ∈ polyL V :=
  subset_convexHull ℝ _ ⟨v, hv, rfl⟩

lemma polyL_convex (V : List (List ℤ)) : Convex ℝ (polyL V) := convex_convexHull ℝ _

lemma facet_le_on_poly {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    {f : List ℤ × ℤ} (hf : f ∈ F) {x : Pt 4} (hx : x ∈ polyL V) : rdot4 f.1 x ≤ f.2 := by
  obtain ⟨hlen, _, hverts⟩ := dataValid_facet hv hf
  have hsub : toPt4 '' {v | v ∈ V} ⊆ {y | rdot4 f.1 y ≤ f.2} := by
    rintro _ ⟨v, hv', rfl⟩
    have h := hverts v hv'
    show rdot4 f.1 (toPt4 v) ≤ f.2
    rw [← dotL_cast4 _ _ hlen (dataValid_vert hv hv').1]
    exact_mod_cast h
  exact convexHull_min hsub (convex_halfSpace_le (rdot4_isLinear f.1) _) hx

lemma facet_le_on_smul {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    {f : List ℤ × ℤ} (hf : f ∈ F) (k : ℕ) {x : Pt 4} (hx : x ∈ (k : ℝ) • polyL V) :
    rdot4 f.1 x ≤ k * f.2 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [(rdot4_isLinear f.1).map_smul]
  exact mul_le_mul_of_nonneg_left (facet_le_on_poly hv hf hy) (Nat.cast_nonneg k)

lemma polyL_bound {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    {x : Pt 4} (hx : x ∈ polyL V) (i : Fin 4) : |x i| ≤ (B.getD i.val 0 : ℝ) := by
  have hsub : toPt4 '' {v | v ∈ V} ⊆
      (fun y : Pt 4 => y i) ⁻¹' Set.Icc (-(B.getD i.val 0 : ℝ)) (B.getD i.val 0 : ℝ) := by
    rintro _ ⟨v, hv', rfl⟩
    have h := (dataValid_vert hv hv').2 i
    have h' : |((v.getD i.val 0 : ℤ) : ℝ)| ≤ ((B.getD i.val 0 : ℕ) : ℝ) := by exact_mod_cast h
    exact abs_le.1 h'
  have hlin : IsLinearMap ℝ (fun y : Pt 4 => y i) := (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i).isLinear
  exact abs_le.2 (convexHull_min hsub ((convex_Icc _ _).is_linear_preimage hlin) hx)

lemma smul_bound {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    {k : ℕ} {x : Pt 4} (hx : x ∈ (k : ℝ) • polyL V) (i : Fin 4) : |x i| ≤ (k : ℝ) * (B.getD i.val 0 : ℝ) := by
  obtain ⟨y, hy, rfl⟩ := hx
  show |(k : ℝ) * y i| ≤ _
  rw [abs_mul, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left (polyL_bound hv hy i) (Nat.cast_nonneg k)

lemma mem_box4 {B : List ℕ} {k : ℕ} {p : Fin 4 → ℤ}
    (hp : ∀ i : Fin 4, -((k * B.getD i.val 0 : ℕ) : ℤ) ≤ p i ∧ p i ≤ ((k * B.getD i.val 0 : ℕ) : ℤ)) :
    List.ofFn p ∈ box4 B k := by
  simp only [box4, List.mem_flatMap, List.mem_map]
  refine ⟨p 0, mem_rng.2 (hp 0), p 1, mem_rng.2 (hp 1), p 2, mem_rng.2 (hp 2), p 3, mem_rng.2 (hp 3), ?_⟩
  simp [List.ofFn_succ]

lemma mem_box4_length {B : List ℕ} {k : ℕ} {z : List ℤ} (hz : z ∈ box4 B k) : z.length = 4 := by
  simp only [box4, List.mem_flatMap, List.mem_map] at hz
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hz
  rfl

lemma box_of_mem {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    {k : ℕ} {p : Fin 4 → ℤ} (hx : ofInt p ∈ (k : ℝ) • polyL V) :
    ∀ i : Fin 4, -((k * B.getD i.val 0 : ℕ) : ℤ) ≤ p i ∧ p i ≤ ((k * B.getD i.val 0 : ℕ) : ℤ) := by
  intro i
  have h := smul_bound hv hx i
  have h' : |(p i : ℝ)| ≤ ((k * B.getD i.val 0 : ℕ) : ℝ) := by
    push_cast
    simpa [ofInt] using h
  have h'' : |p i| ≤ ((k * B.getD i.val 0 : ℕ) : ℤ) := by exact_mod_cast h'
  exact abs_le.1 h''

lemma mem_insideF {F : List (List ℤ × ℤ)} {B : List ℕ} {k : ℕ} {z : List ℤ} :
    z ∈ insideF F B k ↔ z ∈ box4 B k ∧ ∀ f ∈ F, dotL f.1 z ≤ k * f.2 := by
  simp [insideF, List.mem_filter, List.all_eq_true]

lemma mem_strictF {F : List (List ℤ × ℤ)} {B : List ℕ} {k : ℕ} {z : List ℤ} :
    z ∈ strictF F B k ↔ z ∈ box4 B k ∧ ∀ f ∈ F, dotL f.1 z < k * f.2 := by
  simp [strictF, List.mem_filter, List.all_eq_true]

/-! ### Convex-combination certificates -/

/-- `Σ n_j v_j` over a list of pairs `(j, n_j)`. -/
def combo4 (V : List (List ℤ)) (pairs : List (ℕ × ℕ)) : List ℤ :=
  pairs.foldr (fun p acc => List.zipWith (· + ·) acc ((V.getD p.1 []).map (fun c => (p.2 : ℤ) * c)))
    [0, 0, 0, 0]

/-- A certificate that `z ∈ kP`: `N > 0`, the weights sum to `k N`, every index is a vertex, `N z = Σ n_j v_j`. -/
def certOk (V : List (List ℤ)) (k : ℕ) (z : List ℤ) (c : List (ℕ × ℕ) × ℕ) : Bool :=
  decide (0 < c.2) && (c.1.map Prod.snd).sum == k * c.2 && c.1.all (fun p => decide (p.1 < V.length)) &&
    z.length == 4 && z.map (fun a => (c.2 : ℤ) * a) == combo4 V c.1

lemma polyL_nonempty {V : List (List ℤ)} (hne : V ≠ []) : (polyL V).Nonempty := by
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil V hne
  exact ⟨toPt4 v, mem_polyL_vert hv⟩

lemma combo4_sound {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    (hne : V ≠ []) (pairs : List (ℕ × ℕ)) (hidx : ∀ p ∈ pairs, p.1 < V.length) :
    (combo4 V pairs).length = 4 ∧ toPt4 (combo4 V pairs) ∈ (((pairs.map Prod.snd).sum : ℕ) : ℝ) • polyL V := by
  induction pairs with
  | nil =>
    refine ⟨rfl, ?_⟩
    simp only [List.map_nil, List.sum_nil, Nat.cast_zero, Set.zero_smul_set (polyL_nonempty hne)]
    show toPt4 [0, 0, 0, 0] ∈ (0 : Set (Pt 4))
    rw [Set.mem_zero]
    funext i
    fin_cases i <;> simp [toPt4]
  | cons p ps ih =>
    obtain ⟨hlen, hmem⟩ := ih (fun q hq => hidx q (List.mem_cons_of_mem _ hq))
    have hp : p.1 < V.length := hidx p List.mem_cons_self
    have hvmem : V.getD p.1 [] ∈ V := by
      rw [List.getD_eq_getElem _ _ hp]
      exact List.getElem_mem hp
    have hvlen := (dataValid_vert hv hvmem).1
    have hslen : ((V.getD p.1 []).map (fun c => (p.2 : ℤ) * c)).length = 4 := by
      rw [List.length_map, hvlen]
    have hcombo : combo4 V (p :: ps) =
        List.zipWith (· + ·) (combo4 V ps) ((V.getD p.1 []).map (fun c => (p.2 : ℤ) * c)) := rfl
    refine ⟨by rw [hcombo, List.length_zipWith, hlen, hslen]; rfl, ?_⟩
    rw [hcombo, toPt4_add _ _ hlen hslen, toPt4_scale _ _ hvlen]
    have hvP : toPt4 (V.getD p.1 []) ∈ polyL V := mem_polyL_vert hvmem
    have : ((((p :: ps).map Prod.snd).sum : ℕ) : ℝ) = (((ps.map Prod.snd).sum : ℕ) : ℝ) + (p.2 : ℝ) := by
      simp [add_comm]
    rw [this, (polyL_convex V).add_smul (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact Set.add_mem_add hmem (Set.smul_mem_smul_set (by exact_mod_cast hvP))

lemma certOk_sound {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    (hne : V ≠ []) {k : ℕ} {z : List ℤ} {c : List (ℕ × ℕ) × ℕ} (h : certOk V k z c = true) :
    z.length = 4 ∧ toPt4 z ∈ (k : ℝ) • polyL V := by
  simp only [certOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hN, hsum⟩, hidx⟩, hlen⟩, hz⟩ := h
  refine ⟨hlen, ?_⟩
  obtain ⟨_, hmem⟩ := combo4_sound hv hne c.1 hidx
  rw [hsum, ← hz, toPt4_scale _ _ hlen] at hmem
  have hN' : ((c.2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show ((c.2 : ℤ) : ℝ) = ((c.2 : ℕ) : ℝ) by simp,
    show ((k * c.2 : ℕ) : ℝ) = ((c.2 : ℕ) : ℝ) * (k : ℝ) by push_cast; ring, mul_smul] at hmem
  exact (Set.smul_mem_smul_set_iff₀ hN' _ _).1 hmem

/-- All membership certificates for the lattice points of `kP`, in box order. -/
def memAll (V : List (List ℤ)) (F : List (List ℤ × ℤ)) (B : List ℕ) (k : ℕ) (C : List (List (ℕ × ℕ) × ℕ)) :
    Bool :=
  (insideF F B k).length == C.length && ((insideF F B k).zip C).all fun q => certOk V k q.1 q.2

lemma smul_inter_eq {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    (k : ℕ) (hcert : ∀ z ∈ insideF F B k, toPt4 z ∈ (k : ℝ) • polyL V) :
    (k : ℝ) • polyL V ∩ Zn 4 = toPt4 '' {z | z ∈ insideF F B k} := by
  ext x
  constructor
  · rintro ⟨hx, p, rfl⟩
    refine ⟨List.ofFn p, mem_insideF.2 ⟨mem_box4 (box_of_mem hv hx), fun f hf => ?_⟩, toPt4_ofFn p⟩
    have h := facet_le_on_smul hv hf k hx
    rw [← toPt4_ofFn, ← dotL_cast4 _ _ (dataValid_facet hv hf).1 (by simp)] at h
    exact_mod_cast h
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hcert z hz, toPt4_mem_Zn z⟩

/-- The count `L_P(k) = #(kP ∩ ℤ⁴)` from the certificates. -/
theorem latCount_eq {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    (hne : V ≠ []) (k : ℕ) (C : List (List (ℕ × ℕ) × ℕ)) (hmem : memAll V F B k C = true)
    (hchain : (box4 B k).IsChain (· < ·)) : latCount (Zn 4) (polyL V) k = C.length := by
  unfold memAll at hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at hmem
  have hall := forall_zip (ok := fun z c => certOk V k z c) hmem.1 hmem.2
  have h := smul_inter_eq hv k (fun z hz => by
    obtain ⟨c, hc⟩ := hall z hz
    exact (certOk_sound hv hne hc).2)
  unfold latCount
  rw [h, ncard_toPt4_image _ (fun z hz => mem_box4_length (mem_insideF.1 hz).1)
    ((nodup_of_chain hchain).filter _), hmem.1]

/-! ### Interior points -/

/-- If `x ∈ int S` and `⟨u, y⟩ ≤ c` on `S` with `u ≠ 0`, then `⟨u, x⟩ < c`. -/
lemma strict_of_interior {S : Set (Pt 4)} {f : List ℤ} (hf : f.length = 4) (hpos : 0 < dotL f f) {c : ℝ}
    (hle : ∀ y ∈ S, rdot4 f y ≤ c) {x : Pt 4} (hx : x ∈ interior S) : rdot4 f x < c := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  have hw : 0 < rdot4 f (toPt4 f) := by
    rw [← dotL_cast4 f f hf hf]
    exact_mod_cast hpos
  set t := ε / (2 * (‖toPt4 f‖ + 1)) with ht
  have hden : 0 < 2 * (‖toPt4 f‖ + 1) := by positivity
  have htpos : 0 < t := div_pos hε hden
  have hmem : x + t • toPt4 f ∈ S := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le, ht,
      div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [norm_nonneg (toPt4 f)]
  have h := hle _ hmem
  rw [(rdot4_isLinear f).map_add, (rdot4_isLinear f).map_smul, smul_eq_mul] at h
  nlinarith

/-- If `S` is convex and contains `x + δ c` for every corner `c ∈ {±1}⁴`, then `x ∈ int S`. -/
lemma mem_interior_of_corners {S : Set (Pt 4)} (hS : Convex ℝ S) {x : Pt 4} {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ c ∈ Sec2.corners 4, x + δ • c ∈ S) : x ∈ interior S := by
  have hpre : Convex ℝ {w : Pt 4 | x + δ • w ∈ S} := by
    intro a ha b hb s t hs ht hst
    have h := hS ha hb hs ht hst
    have e : x + δ • (s • a + t • b) = s • (x + δ • a) + t • (x + δ • b) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-x i) * hst
    show x + δ • (s • a + t • b) ∈ S
    rw [e]
    exact h
  have hcube : cube 4 ⊆ {w : Pt 4 | x + δ • w ∈ S} := by
    rw [Sec2.cube_eq_convexHull_corners 4]
    exact convexHull_min hc hpre
  have hball : Metric.ball x δ ⊆ S := by
    intro y hy
    have hw : δ⁻¹ • (y - x) ∈ cube 4 := by
      intro i
      rw [Metric.mem_ball, dist_pi_lt_iff hδ] at hy
      have hi := hy i
      rw [Real.dist_eq] at hi
      show |δ⁻¹ * (y i - x i)| ≤ 1
      rw [abs_mul, abs_inv, abs_of_pos hδ, inv_mul_le_iff₀ hδ]
      linarith
    have h : x + δ • (δ⁻¹ • (y - x)) ∈ S := hcube hw
    have e : x + δ • (δ⁻¹ • (y - x)) = y := by
      rw [smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
      abel
    rw [e] at h
    exact h
  exact mem_interior.2 ⟨Metric.ball x δ, hball, Metric.isOpen_ball, Metric.mem_ball_self hδ⟩

/-- The 16 corners of `{-1,1}⁴` as lists (box order). -/
def corners4 : List (List ℤ) := (box4 [1, 1, 1, 1] 1).filter fun z => z.all fun a => a != 0

lemma corner_mem (c : Pt 4) (hc : c ∈ Sec2.corners 4) : ∃ cl ∈ corners4, toPt4 cl = c := by
  let p : Fin 4 → ℤ := fun i => if c i = 1 then 1 else -1
  have hp : ∀ i, ((p i : ℤ) : ℝ) = c i := by
    intro i
    rcases hc i with h | h
    · simp [p, h]
    · have h' : c i ≠ 1 := by rw [h]; norm_num
      simp only [p, if_neg h', h]
      norm_num
  refine ⟨List.ofFn p, ?_, ?_⟩
  · rw [corners4, List.mem_filter]
    refine ⟨mem_box4 (fun i => ?_), ?_⟩
    · fin_cases i <;> (simp only [p]; split_ifs <;> decide)
    · rw [List.all_eq_true]
      intro a ha
      rw [List.mem_ofFn] at ha
      obtain ⟨i, rfl⟩ := ha
      simp only [p]
      split_ifs <;> decide
  · rw [toPt4_ofFn]
    funext i
    exact hp i

/-- `d z + c`. -/
def shift (d : ℕ) (z c : List ℤ) : List ℤ := List.zipWith (fun a b => (d : ℤ) * a + b) z c

lemma toPt4_shift (d : ℕ) (z c : List ℤ) (hz : z.length = 4) (hc : c.length = 4) :
    toPt4 (shift d z c) = (d : ℝ) • toPt4 z + toPt4 c := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := length_eq_four hz
  obtain ⟨b0, b1, b2, b3, rfl⟩ := length_eq_four hc
  funext i
  fin_cases i <;> simp [shift, toPt4]

/-- Interior certificates of one point `z`: for each corner `c`, a certificate that `d z + c ∈ (d k) P`. -/
def intOk (V : List (List ℤ)) (k d : ℕ) (z : List ℤ) (cs : List (List (ℕ × ℕ) × ℕ)) : Bool :=
  corners4.length == cs.length && (corners4.zip cs).all fun q => certOk V (d * k) (shift d z q.1) q.2

/-- All interior certificates for the points of `strictF`, in box order. -/
def intAll (V : List (List ℤ)) (F : List (List ℤ × ℤ)) (B : List ℕ) (k d : ℕ)
    (C : List (List (List (ℕ × ℕ) × ℕ))) : Bool :=
  (strictF F B k).length == C.length && ((strictF F B k).zip C).all fun q => intOk V k d q.1 q.2

lemma intOk_sound {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    (hne : V ≠ []) {k d : ℕ} (hd : 0 < d) {z : List ℤ} (hz : z.length = 4) {cs : List (List (ℕ × ℕ) × ℕ)}
    (h : intOk V k d z cs = true) : toPt4 z ∈ interior ((k : ℝ) • polyL V) := by
  unfold intOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hall := forall_zip (ok := fun cl c => certOk V (d * k) (shift d z cl) c) h.1 h.2
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  refine mem_interior_of_corners ((polyL_convex V).smul _) (δ := (d : ℝ)⁻¹) (by positivity) ?_
  intro c hc
  obtain ⟨cl, hcl, rfl⟩ := corner_mem c hc
  obtain ⟨cert, hcert⟩ := hall cl hcl
  obtain ⟨_, hmem⟩ := certOk_sound hv hne hcert
  have hcllen : cl.length = 4 := mem_box4_length (List.mem_filter.1 hcl).1
  rw [toPt4_shift d z cl hz hcllen] at hmem
  have e : (d : ℝ) • toPt4 z + toPt4 cl = (d : ℝ) • (toPt4 z + (d : ℝ)⁻¹ • toPt4 cl) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hd', one_smul]
  rw [e, show ((d * k : ℕ) : ℝ) = (d : ℝ) * (k : ℝ) by push_cast; ring, mul_smul] at hmem
  exact (Set.smul_mem_smul_set_iff₀ hd' _ _).1 hmem

lemma interior_inter_eq {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    (hne : V ≠ []) (k d : ℕ) (hd : 0 < d) (C : List (List (List (ℕ × ℕ) × ℕ)))
    (hint : intAll V F B k d C = true) :
    interior ((k : ℝ) • polyL V) ∩ Zn 4 = toPt4 '' {z | z ∈ strictF F B k} := by
  unfold intAll at hint
  simp only [Bool.and_eq_true, beq_iff_eq] at hint
  have hall := forall_zip (ok := fun z cs => intOk V k d z cs) hint.1 hint.2
  ext x
  constructor
  · rintro ⟨hx, p, rfl⟩
    refine ⟨List.ofFn p, mem_strictF.2 ⟨mem_box4 (box_of_mem hv (interior_subset hx)), fun f hf => ?_⟩,
      toPt4_ofFn p⟩
    obtain ⟨hlen, hpos, _⟩ := dataValid_facet hv hf
    have h := strict_of_interior hlen hpos (fun y hy => facet_le_on_smul hv hf k hy) hx
    rw [← toPt4_ofFn, ← dotL_cast4 _ _ hlen (by simp)] at h
    exact_mod_cast h
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨cs, hcs⟩ := hall z hz
    exact ⟨intOk_sound hv hne hd (mem_box4_length (mem_strictF.1 hz).1) hcs, toPt4_mem_Zn z⟩

/-- The count `#(int(kP) ∩ ℤ⁴)` from the certificates. -/
theorem intCount_eq {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    (hne : V ≠ []) (k d : ℕ) (hd : 0 < d) (C : List (List (List (ℕ × ℕ) × ℕ)))
    (hint : intAll V F B k d C = true) (hchain : (box4 B k).IsChain (· < ·)) :
    intCount (Zn 4) (polyL V) k = C.length := by
  have hlen : (strictF F B k).length = C.length := by
    unfold intAll at hint
    simp only [Bool.and_eq_true, beq_iff_eq] at hint
    exact hint.1
  unfold intCount
  rw [interior_inter_eq hv hne k d hd C hint, ncard_toPt4_image _ (fun z hz => mem_box4_length
    (mem_strictF.1 hz).1) ((nodup_of_chain hchain).filter _), hlen]

/-! ### Membership in `W⁴` -/

lemma isLatticePolytope_polyL (V : List (List ℤ)) : IsLatticePolytope (Zn 4) (polyL V) := by
  classical
  refine ⟨(V.map toPt4).toFinset, ?_, ?_⟩
  · intro x hx
    simp only [List.coe_toFinset, List.mem_map, Set.mem_ofPred_eq] at hx
    obtain ⟨v, _, rfl⟩ := hx
    exact toPt4_mem_Zn v
  · unfold polyL
    congr 1
    ext x
    simp

/-- Every vertex `v` has its negative `-v` in the list. -/
def negClosed (V : List (List ℤ)) : Bool := V.all fun v => V.contains (v.map Neg.neg)

lemma toPt4_neg (v : List ℤ) (hv : v.length = 4) : toPt4 (v.map Neg.neg) = -toPt4 v := by
  obtain ⟨a, b, c, d, rfl⟩ := length_eq_four hv
  funext i
  fin_cases i <;> simp [toPt4]

lemma neg_polyL {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    (hneg : negClosed V = true) : -polyL V = polyL V := by
  have hsub : -(toPt4 '' {v | v ∈ V}) ⊆ toPt4 '' {v | v ∈ V} := by
    intro x hx
    obtain ⟨v, hv', hvx⟩ := hx
    have hmem : v.map Neg.neg ∈ V := by
      have := List.all_eq_true.1 hneg v hv'
      simpa using this
    refine ⟨v.map Neg.neg, hmem, ?_⟩
    rw [toPt4_neg v (dataValid_vert hv hv').1, hvx, neg_neg]
  have heq : -(toPt4 '' {v | v ∈ V}) = toPt4 '' {v | v ∈ V} := by
    refine le_antisymm hsub ?_
    intro x hx
    have : -x ∈ -(toPt4 '' {v | v ∈ V}) := by simpa using hx
    have h2 := hsub this
    simpa using h2
  unfold polyL
  rw [← convexHull_neg, heq]

/-- `0` is the only interior lattice point of `P` (when the only strict point of the box is `0`). -/
lemma interior_eq_zero {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    (hne : V ≠ []) (d : ℕ) (hd : 0 < d) (C : List (List (List (ℕ × ℕ) × ℕ))) (hint : intAll V F B 1 d C = true)
    (h0 : strictF F B 1 = [[0, 0, 0, 0]]) : interior (polyL V) ∩ Zn 4 = {0} := by
  have h := interior_inter_eq hv hne 1 d hd C hint
  rw [Nat.cast_one, one_smul, h0] at h
  rw [h]
  have hz : toPt4 [0, 0, 0, 0] = 0 := by
    funext i
    fin_cases i <;> simp [toPt4]
  ext x
  simp [hz]

theorem inW_polyL {V : List (List ℤ)} {F : List (List ℤ × ℤ)} {B : List ℕ} (hv : dataValid V F B = true)
    (hne : V ≠ []) (hneg : negClosed V = true) (d : ℕ) (hd : 0 < d) (C : List (List (List (ℕ × ℕ) × ℕ)))
    (hint : intAll V F B 1 d C = true) (h0 : strictF F B 1 = [[0, 0, 0, 0]]) : InW (Zn 4) (polyL V) :=
  ⟨isLatticePolytope_polyL V, neg_polyL hv hneg, interior_eq_zero hv hne d hd C hint h0⟩

end Wills.Count4
