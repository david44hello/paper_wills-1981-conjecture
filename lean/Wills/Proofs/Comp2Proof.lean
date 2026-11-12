/-
Wills/Proofs/Comp2Proof.lean — a Lean proof of `Comp2`, the result of Computation 2 (l.353; NOT its count 40,406):
every sublattice `B ℤ⁴` of index `d ≥ 3` has at most 27 points in `{-1,0,1}⁴`; `d = 2` gives at most 45, attained.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Proofs.Sec6F

open MeasureTheory Pointwise

namespace Wills.C2P

open Wills.Sec5

/-- The 81 integer points of `{-1,0,1}⁴`. -/
def cubeFin : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-1 : ℤ) 1

lemma mem_cubeFin (x : Fin 4 → ℤ) : x ∈ cubeFin ↔ ∀ i, -1 ≤ x i ∧ x i ≤ 1 := by
  simp [cubeFin, Fintype.mem_piFinset]

open scoped Classical in
/-- `subLat B ∩ {-1,0,1}⁴` as the image of a finset of integer vectors. -/
lemma subLat_cube_eq (B : Matrix (Fin 4) (Fin 4) ℤ) :
    subLat B ∩ cubePts 4 = ofInt '' ↑(cubeFin.filter (fun x => x ∈ rangeB B)) := by
  ext y
  constructor
  · rintro ⟨hyB, z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    rw [Finset.coe_filter, Set.mem_setOf_eq, mem_cubeFin]
    exact ⟨hz, (ofInt_mem_subLat B z).1 hyB⟩
  · rintro ⟨z, hz, rfl⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_cubeFin] at hz
    exact ⟨(ofInt_mem_subLat B z).2 hz.2, z, hz.1, rfl⟩

open scoped Classical in
lemma ncard_subLat_cube (B : Matrix (Fin 4) (Fin 4) ℤ) :
    (subLat B ∩ cubePts 4).ncard = (cubeFin.filter (fun x => x ∈ rangeB B)).card := by
  rw [subLat_cube_eq, Set.ncard_image_of_injective _ Sec2.ofInt_injective, Set.ncard_coe_finset]

/-! ### (a) an odd prime divides the index -/

/-- Kernel check: for each coordinate `j`, `{-1,0,1}⁴` has 27 points with `x_j = 0`. -/
lemma card_slice : ∀ j : Fin 4, (cubeFin.filter (fun x => x j = 0)).card = 27 := by
  decide +kernel

/-- If `p ≥ 3` is prime and `v ≠ 0` over `ZMod p`, at most 27 points of `{-1,0,1}⁴` satisfy `Σ v_i x_i = 0`. -/
lemma card_le_27_of_prime (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) (v : Fin 4 → ZMod p) (hv : v ≠ 0) :
    (cubeFin.filter (fun x => ∑ i, v i * (x i : ZMod p) = 0)).card ≤ 27 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  rw [← card_slice j]
  refine Finset.card_le_card_of_injOn (fun x => Function.update x j 0) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_cubeFin] at hx ⊢
    refine ⟨fun i => ?_, by simp⟩
    by_cases hij : i = j
    · subst hij; simp
    · rw [Function.update_of_ne hij]; exact hx.1 i
  · intro x hx x' hx' hxx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_cubeFin] at hx hx'
    have hoff : ∀ i, i ≠ j → x i = x' i := fun i hij => by
      have := congrFun hxx i
      simpa [Function.update_of_ne hij] using this
    have hsum : v j * ((x j : ZMod p) - (x' j : ZMod p)) = 0 := by
      have h := sub_eq_zero.2 (hx.2.trans hx'.2.symm)
      rw [← Finset.sum_sub_distrib] at h
      rw [Finset.sum_eq_single j (fun i _ hij => by rw [hoff i hij, sub_self])
        (fun h' => absurd (Finset.mem_univ j) h')] at h
      rw [mul_sub]; exact h
    have hdiff : ((x j - x' j : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_sub]
      exact (mul_eq_zero.1 hsum).resolve_left (by simpa using hj)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hdiff
    have hj1 := hx.1 j
    have hj2 := hx'.1 j
    have heq : x j = x' j := by
      obtain ⟨c, hc⟩ := hdiff
      have hp : (3 : ℤ) ≤ p := by exact_mod_cast hp3
      rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · nlinarith
      · rw [hc0, mul_zero] at hc; omega
      · nlinarith
    funext i
    by_cases hij : i = j
    · subst hij; exact heq
    · exact hoff i hij

/-- A prime `p ∣ det B`: some `v ≠ 0` over `ZMod p` with `Σ v_i y_i = 0` for every `y` in the lattice `B ℤ⁴`. -/
lemma exists_kernel_mod (B : Matrix (Fin 4) (Fin 4) ℤ) (p : ℕ) [Fact p.Prime] (hp : (p : ℤ) ∣ B.det) :
    ∃ v : Fin 4 → ZMod p, v ≠ 0 ∧ ∀ y ∈ rangeB B, ∑ i, v i * (y i : ZMod p) = 0 := by
  set Bp := (Int.castRingHom (ZMod p)).mapMatrix B
  have hdet : Bp.det = 0 := by
    rw [← RingHom.map_det, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hp
  obtain ⟨v, hv, hvB⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  refine ⟨v, hv, fun y hy => ?_⟩
  obtain ⟨z, rfl⟩ := (mem_rangeB B y).1 hy
  have hcast : (fun i => ((B.mulVec z) i : ZMod p)) = Bp.mulVec (fun i => (z i : ZMod p)) := by
    funext i
    simp [Bp, Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply]
  have : ∑ i, v i * ((B.mulVec z) i : ZMod p) = v ⬝ᵥ (fun i => ((B.mulVec z) i : ZMod p)) := rfl
  rw [this, hcast, Matrix.dotProduct_mulVec, hvB, zero_dotProduct]

/-! ### (b) the index is a power of 2, at least 4 -/

lemma zmod2_eq_one (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  revert a
  decide

/-- `2 ∣ det B`: the lattice `B ℤ⁴` lies in some `Γ_I = {y : Σ_{i ∈ I} y_i even}`, `I` nonempty. -/
lemma exists_gammaI_of_two_dvd (B : Matrix (Fin 4) (Fin 4) ℤ) (h2 : (2 : ℤ) ∣ B.det) :
    ∃ I : Finset (Fin 4), I.Nonempty ∧ ∀ y ∈ rangeB B, Even (∑ i ∈ I, y i) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv, hker⟩ := exists_kernel_mod B 2 (by exact_mod_cast h2)
  refine ⟨Finset.univ.filter (fun i => v i ≠ 0), ?_, fun y hy => ?_⟩
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    exact ⟨j, by simpa using hj⟩
  · have h := hker y hy
    have hv1 : ∀ i, v i ≠ 0 → v i = 1 := fun i hi => zmod2_eq_one _ hi
    have hsum : ∑ i, v i * (y i : ZMod 2) = ((∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), y i : ℤ) : ZMod 2) := by
      rw [Int.cast_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : v i = 0
      · simp [hi]
      · simp [hi, hv1 i hi]
    rw [hsum, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact even_iff_two_dvd.2 (by exact_mod_cast h)

/-- A lattice inside `Γ_I` factors through `matI I`: `B = matI I * B'`. -/
lemma factor_matI (B : Matrix (Fin 4) (Fin 4) ℤ) (I : Finset (Fin 4)) (hI : I.Nonempty)
    (hB : ∀ y ∈ rangeB B, Even (∑ i ∈ I, y i)) : ∃ B' : Matrix (Fin 4) (Fin 4) ℤ, B = matI I * B' := by
  have hcol : ∀ k : Fin 4, ∃ w : Fin 4 → ℤ, (matI I).mulVec w = B.mulVec (Pi.single k 1) := fun k => by
    have hy : B.mulVec (Pi.single k 1) ∈ rangeB B := (mem_rangeB B _).2 ⟨_, rfl⟩
    have hg : ofInt (B.mulVec (Pi.single k 1)) ∈ subLat (matI I) := by
      rw [(gammaI_eq_subLat I hI).2, ofInt_mem_gammaI]
      exact hB _ hy
    exact (mem_rangeB _ _).1 ((ofInt_mem_subLat _ _).1 hg)
  choose w hw using hcol
  refine ⟨Matrix.of fun i k => w k i, ?_⟩
  ext i k
  have h : B i k = (matI I).mulVec (w k) i := by
    rw [hw k]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Matrix.mul_apply, h]
  rfl

/-- `2 (matI I)⁻¹`, in closed form: row `i₀` is `e_{i₀} - Σ_{j ∈ I, j ≠ i₀} e_j`, the other rows are `2 e_k`. -/
def adjF (I : Finset (Fin 4)) (i j : Fin 4) : ℤ :=
  if i = i0 I then (if j = i0 I then 1 else if j ∈ I then -1 else 0) else (if i = j then 2 else 0)

/-- Kernel check over the 15 nonempty `I`: `adjF I * matI I = 2`. -/
lemma adj_check : ∀ I : Finset (Fin 4), I.Nonempty → Matrix.of (adjF I) * matI I = 2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide +kernel

/-- The test for `x ∈ matI I · Γ_J`: `adjF I · x = 2w` with `w` integral and `Σ_{j ∈ J} w_j` even. -/
def inMG (I J : Finset (Fin 4)) (x : Fin 4 → ℤ) : Prop :=
  (∀ k, (Matrix.of (adjF I)).mulVec x k % 2 = 0) ∧ (∑ j ∈ J, (Matrix.of (adjF I)).mulVec x j / 2) % 2 = 0

instance (I J : Finset (Fin 4)) (x : Fin 4 → ℤ) : Decidable (inMG I J x) := by
  unfold inMG; infer_instance

/-- Kernel check over the 225 pairs: every index-4 lattice `matI I · Γ_J` has at most 27 points in `{-1,0,1}⁴`. -/
lemma card_inMG : ∀ I J : Finset (Fin 4), I.Nonempty → J.Nonempty → (cubeFin.filter (inMG I J)).card ≤ 27 := by
  decide +kernel

lemma inMG_of (I J : Finset (Fin 4)) (hI : I.Nonempty) (w : Fin 4 → ℤ) (hw : Even (∑ j ∈ J, w j)) :
    inMG I J ((matI I).mulVec w) := by
  have h2 : ∀ k, (Matrix.of (adjF I)).mulVec ((matI I).mulVec w) k = w k + w k := fun k => by
    rw [Matrix.mulVec_mulVec, adj_check I hI]
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, two_mul]
  rw [inMG]
  simp only [h2]
  refine ⟨fun k => by omega, ?_⟩
  have : ∀ j, (w j + w j) / 2 = w j := fun j => by omega
  simp only [this]
  exact Int.even_iff.1 hw

open scoped Classical in
/-- Index `2^a`, `a ≥ 2` (here: `4 ∣ det B`): at most 27 points in `{-1,0,1}⁴`. -/
lemma card_le_27_of_four_dvd (B : Matrix (Fin 4) (Fin 4) ℤ) (h4 : (4 : ℤ) ∣ B.det) :
    (cubeFin.filter (fun x => x ∈ rangeB B)).card ≤ 27 := by
  obtain ⟨I, hI, hBI⟩ := exists_gammaI_of_two_dvd B (dvd_trans ⟨2, by norm_num⟩ h4)
  obtain ⟨B', rfl⟩ := factor_matI B I hI hBI
  have h2' : (2 : ℤ) ∣ B'.det := by
    rw [Matrix.det_mul, matI_det I hI] at h4
    obtain ⟨c, hc⟩ := h4
    exact ⟨c, by linarith⟩
  obtain ⟨J, hJ, hB'J⟩ := exists_gammaI_of_two_dvd B' h2'
  refine (Finset.card_le_card ?_).trans (card_inMG I J hI hJ)
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  obtain ⟨z, rfl⟩ := (mem_rangeB _ x).1 hx.2
  rw [← Matrix.mulVec_mulVec]
  exact inMG_of I J hI _ (hB'J _ ((mem_rangeB B' _).2 ⟨z, rfl⟩))

/-! ### Assembly -/

open scoped Classical in
/-- Index `d ≥ 3`: at most 27 points of `{-1,0,1}⁴` (Computation 2's bound for `d ≥ 3`). -/
lemma card_le_27 (B : Matrix (Fin 4) (Fin 4) ℤ) (h3 : 3 ≤ |B.det|) :
    (cubeFin.filter (fun x => x ∈ rangeB B)).card ≤ 27 := by
  set n := B.det.natAbs with hn
  have hn3 : 3 ≤ n := by
    have : ((n : ℕ) : ℤ) = |B.det| := Int.natCast_natAbs B.det
    omega
  have hdvd : ∀ m : ℕ, m ∣ n → (m : ℤ) ∣ B.det := fun m hm => Int.natCast_dvd.2 hm
  by_cases hodd : ∃ p, p.Prime ∧ p ∣ n ∧ p ≠ 2
  · obtain ⟨p, hp, hpn, hp2⟩ := hodd
    haveI := Fact.mk hp
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    obtain ⟨v, hv, hker⟩ := exists_kernel_mod B p (hdvd p hpn)
    refine (Finset.card_le_card ?_).trans (card_le_27_of_prime p hp3 v hv)
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hker x hx.2⟩
  · push Not at hodd
    have hpow : ∀ m : ℕ, m ∣ n → 2 ≤ m → 2 ∣ m := fun m hm hm2 => by
      have hmin := Nat.minFac_prime (show m ≠ 1 by omega)
      have h := hodd _ hmin (dvd_trans (Nat.minFac_dvd m) hm)
      rw [← h]; exact Nat.minFac_dvd m
    obtain ⟨m, hm⟩ := hpow n dvd_rfl (by omega)
    obtain ⟨k, hk⟩ := hpow m ⟨2, by omega⟩ (by omega)
    exact card_le_27_of_four_dvd B (hdvd 4 ⟨k, by omega⟩)

/-- Computation 2's result (`Comp2`), proved: index `d = 2` gives at most 45 points (attained), `d ≥ 3` at most 27. -/
theorem comp2_proof : Comp2 := by
  refine ⟨fun B hd2 hd16 _ => ?_, S6F.comp2_d2_max.2⟩
  split_ifs with h
  · exact S6F.comp2_d2_max.1 B h
  · rw [ncard_subLat_cube]
    exact card_le_27 B (by omega)

end Wills.C2P
