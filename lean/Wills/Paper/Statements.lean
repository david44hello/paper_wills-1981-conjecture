/-
Wills/Paper/Statements.lean — one Lean theorem (row) per claim of "Wills' (1981) conjecture is fully resolved".
Pointers "l.N" are lines of the paper's TeX source, version 3.20 (md5 47e41917; lines 1-404 as in versions 1.50 to
2.30; Corollary 7.2 and Remark 7.3 at l.406-416); Figure 3 is the file fig_maxg1.tex (md5 a9f75b6d), its caption on
line 32. Rows fig3_bound_gt, fig3_lt_eight and comp5_maximal are RETIRED: their sentences were printed in earlier
versions of the paper (last: text version 2.30 for the two Figure 3 rows, 2.80 for comp5_maximal) and are not printed
in this version; they are kept, not counted. A row is proved iff its body is a proof term. A fact from Wills/Facts/ or
a computation from Wills/Checks/ that a proof uses is an explicit hypothesis of the row (binders hEHR, hE1, hE2, hE3,
hTRI, hTILE, hVolW, hC1, hC3, hC4, hC5; Computation 2's result is proved: comp2_result). A row whose claim is about
(E3)'s facet data takes hE3 even when its proof does not use it (then named _hE3, Lean's mark of an unused
hypothesis). The status of every row, as Lean reports it, is in AUDIT.md; CLAIM_MAP.tsv maps the printed claims to
rows; AUDIT_NOTES.md explains the modelling choices.
Author: Dave Goel.
Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Wills.Defs.Basic
import Wills.Defs.Cases
import Wills.Defs.Examples
import Wills.Facts.Basic
import Wills.Checks.Computations
import Wills.Proofs.Sec2
import Wills.Proofs.Rows1
import Wills.Proofs.Sec5
import Wills.Proofs.Rows7
import Wills.Proofs.Iso
import Wills.Proofs.Sec6E
import Wills.Proofs.Sec6F
import Wills.Proofs.Thm12
import Wills.Proofs.Thm71
import Wills.Proofs.WFacets
import Wills.Proofs.Sec7Hyp
import Wills.Proofs.Fig3
import Wills.Proofs.Sandwich
import Wills.Proofs.Dim3
import Wills.Proofs.Comp2Proof
import Wills.Proofs.Rows280
import Wills.Proofs.Cell24Eq

open MeasureTheory Pointwise

namespace Wills

/-! ## Section 1 and Section 2: Ehrhart coefficients, the cube, Minkowski's theorem -/

/-- `ℤⁿ` is the lattice of the identity matrix (so the facts, stated for `lat B`, apply to `ℤⁿ` with `B = 1`,
`det 1 = 1`). -/
theorem lat_one (n : ℕ) : lat (1 : Matrix (Fin n) (Fin n) ℝ) = Zn n :=
  Rows1.lat_one n

/-- (E1), first half, l.56, l.161: `g_0(P) = 1`. -/
theorem g0_eq_one (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (P : Set (Pt n))
    (hP : IsLatticePolytope (lat B) P) (hint : (interior P).Nonempty) : g (lat B) P 0 = 1 :=
  Rows1.g0_eq_one n B hB P hP hint

/-- l.58: Minkowski's first theorem — a convex body `K` symmetric about the origin with no lattice point other than
`0` in its interior has volume at most `2ⁿ`. -/
theorem minkowski_first (n : ℕ) (K : Set (Pt n)) (hconv : Convex ℝ K) (hcpt : IsCompact K)
    (hsymm : ∀ x ∈ K, -x ∈ K) (hlat : interior K ∩ Zn n ⊆ {0}) : volume K ≤ 2 ^ n :=
  Sec2.minkowski_first n K hconv hcpt hsymm hlat

/-- l.58: the volume of the cube `C_n` is `2ⁿ`. -/
theorem cube_vol (n : ℕ) : volume (cube n) = 2 ^ n :=
  Sec2.cube_vol n

/-- l.58: the cube `C_n` belongs to `Oⁿ`. -/
theorem cube_mem (n : ℕ) : InW (Zn n) (cube n) :=
  Sec2.cube_mem n

/-- l.58: `L_{C_n}(k) = (2k+1)ⁿ`. -/
theorem cube_count (n k : ℕ) : latCount (Zn n) (cube n) k = (2 * k + 1) ^ n :=
  Sec2.cube_count n k

/-- l.58: `g_i(C_n) = 2^i binom(n,i)`. -/
theorem cube_g (n i : ℕ) : g (Zn n) (cube n) i = (2 : ℝ) ^ i * (Nat.choose n i : ℝ) :=
  Sec2.cube_g n i

/-- l.222: `g_1(C_m) = 2m`. -/
theorem cube_g1 (m : ℕ) : g (Zn m) (cube m) 1 = 2 * m :=
  Sec2.cube_g1 m

/-- l.67: for `i = 0` there is equality: `g_0(P) = g_0(C_n)` for `P ∈ Oⁿ`. -/
theorem conj_i0 (n : ℕ) (P : Set (Pt n)) (hP : InW (Zn n) P) : g (Zn n) P 0 = g (Zn n) (cube n) 0 :=
  Sec2.conj_i0 n P hP

/-- l.67: for `i = n` the inequality is Minkowski's theorem: `g_n(P) ≤ 2ⁿ = 2ⁿ binom(n,n)` for `P ∈ Oⁿ`. -/
theorem conj_in (hE1 : EhrhartLeading) (n : ℕ) (P : Set (Pt n)) (hP : InW (Zn n) P) :
    g (Zn n) P n ≤ (2 : ℝ) ^ n * (Nat.choose n n : ℝ) :=
  Rows1.conj_in hE1 n P hP

/-- l.67: the case `i = n-1`: `g_{n-1}(P) ≤ 2^{n-1} binom(n,n-1)` for `P ∈ Oⁿ` (`n ≥ 1`: l.158). -/
theorem conj_in1 (hE3 : FacetFormula) (n : ℕ) (hn : 1 ≤ n) (P : Set (Pt n))
    (hP : InW (Zn n) P) : g (Zn n) P (n - 1) ≤ (2 : ℝ) ^ (n - 1) * (Nat.choose n (n - 1) : ℝ) :=
  Rows1.conj_in1 hE3 n hn P hP

/-- l.67: hence the conjecture holds for `n ≤ 2` (`n ≥ 1`: l.158). -/
theorem conj_le_two (hE1 : EhrhartLeading) (hE3 : FacetFormula) (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ 2) :
    WillsConj n :=
  Rows1.conj_le_two hE1 hE3 n hn1 hn2

/-- Proof of Corollary 1.4, l.110 (and l.67): Wills' theorem for `n = 3` ([Wil81, Theorem (i), (ii)]), `g_i(P) ≤ 2^i
binom(3,i)` for every `P ∈ O³`. The paper cites it; here it is proved from (E1), (E2), (E3). -/
theorem wills_dim3 (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) : WillsConj 3 :=
  Dim3.wills_dim3_proof hE1 hE2 hE3

/-- l.158: isomorphic pairs have the same lattice-point counts, `φ(kP) ∩ Λ' = φ(kP ∩ Λ)`, so
`L_{P',Λ'} = L_{P,Λ}`; also for the interiors. -/
theorem iso_count (n : ℕ) (P Λ P' Λ' : Set (Pt n)) (h : IsoPair P Λ P' Λ') (k : ℕ) :
    latCount Λ' P' k = latCount Λ P k ∧ intCount Λ' P' k = intCount Λ P k :=
  S2D.iso_count n P Λ P' Λ' h k

/-- l.158: isomorphic pairs have the same Ehrhart coefficients. -/
theorem iso_g (n : ℕ) (P Λ P' Λ' : Set (Pt n)) (h : IsoPair P Λ P' Λ') (i : ℕ) : g Λ' P' i = g Λ P i :=
  S2D.iso_g n P Λ P' Λ' h i

/-- l.158: a linear isomorphism of `ℝⁿ` that carries `ℤⁿ` onto `ℤⁿ` is given by a matrix in `GL_n(ℤ)`. -/
theorem iso_Zn_GL (n : ℕ) (φ : Pt n ≃ₗ[ℝ] Pt n) (h : φ '' Zn n = Zn n) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, IsGLZ U ∧ ∀ x, φ x = (toReal U).mulVec x :=
  S2D.iso_Zn_GL n φ h

/-- (E4), l.164: `L_{P×Q} = L_P L_Q`, since `k(P×Q) ∩ ℤ^{p+q} = (kP ∩ ℤᵖ) × (kQ ∩ ℤ^q)`. -/
theorem e4_prod_count (p q : ℕ) (P : Set (Pt p)) (Q : Set (Pt q)) (k : ℕ) :
    latCount (Zn (p + q)) (prod P Q) k = latCount (Zn p) P k * latCount (Zn q) Q k :=
  Sec2.e4_prod_count p q P Q k

/-- l.170: a polytope in `O^n_Λ` has dimension `n`, because `0` is an interior point. -/
theorem inW_full_dim (n : ℕ) (Λ P : Set (Pt n)) (hP : InW Λ P) :
    (0 : Pt n) ∈ interior P ∧ affineSpan ℝ P = ⊤ :=
  Sec2.inW_full_dim n Λ P hP

/-- l.170, l.151: `G(P)` is odd (the lattice points other than `0` come in pairs `±x`). -/
theorem G_odd (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (P : Set (Pt n)) (hP : InW (lat B) P) :
    Odd (G (lat B) P) :=
  Sec2.G_odd n B hB P hP

/-- Lemma 2.1, l.172-178: if `Y ⊆ {-1,0,1}ⁿ`, `Y = -Y`, and `conv Y` has dimension `n`, then `conv Y ∈ Oⁿ`. -/
theorem lem_2_1 (n : ℕ) (Y : Set (Pt n)) (hY : Y ⊆ cubePts n) (hsymm : -Y = Y)
    (hdim : affineSpan ℝ (convexHull ℝ Y) = ⊤) : InW (Zn n) (convexHull ℝ Y) :=
  Sec2.lem_2_1 n Y hY hsymm hdim

/-- l.180: the same for a sublattice `Γ ⊆ ℤⁿ` (here: any `Γ ⊆ ℤⁿ` containing `0`): if `S ⊆ Γ ∩ C_n` is symmetric
and spans `ℝⁿ`, then `conv S ∈ O^n_Γ` (`n ≥ 1`: l.158). -/
theorem lem_2_1_sub (n : ℕ) (hn : 1 ≤ n) (Γ : Set (Pt n)) (hΓ : Γ ⊆ Zn n) (h0 : (0 : Pt n) ∈ Γ) (S : Set (Pt n))
    (hS : S ⊆ Γ ∩ cube n) (hsymm : -S = S) (hspan : Spans S) : InW Γ (convexHull ℝ S) :=
  Sec2.lem_2_1_sub n hn Γ hΓ h0 S hS hsymm hspan

/-- Lemma 2.2, l.182-188, proof: `int(P×Q) = int P × int Q`. -/
theorem prod_interior (p q : ℕ) (P : Set (Pt p)) (Q : Set (Pt q)) :
    interior (prod P Q) = prod (interior P) (interior Q) :=
  Sec2.prod_interior p q P Q

/-- Lemma 2.2, l.182-188: `P ∈ Oᵖ`, `Q ∈ O^q` ⇒ `P × Q ∈ O^{p+q}` and `g_1(P×Q) = g_1(P) + g_1(Q)`. -/
theorem lem_2_2 (hEHR : EhrhartThm) (p q : ℕ) (P : Set (Pt p)) (Q : Set (Pt q)) (hP : InW (Zn p) P)
    (hQ : InW (Zn q) Q) :
    InW (Zn (p + q)) (prod P Q) ∧ g (Zn (p + q)) (prod P Q) 1 = g (Zn p) P 1 + g (Zn q) Q 1 :=
  Sec2.lem_2_2 hEHR p q P Q hP hQ

/-! ## Section 3: the counterexample in dimension five (Theorem 1.3) -/

/-- Proposition 3.1, l.200-213 (and l.143): for `P ∈ O⁵`,
`g_1(P) = (4(G(P)+1) + 24 vol(P) - A(P))/6` with `A(P) = ½(#(2P ∩ ℤ⁵) + #(int(2P) ∩ ℤ⁵))`. -/
theorem prop_3_1 (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (P : Set (Pt 5))
    (hP : InW (Zn 5) P) :
    g (Zn 5) P 1 = (4 * ((G (Zn 5) P : ℝ) + 1) + 24 * (volume P).toReal -
      (1 / 2) * ((latCount (Zn 5) P 2 : ℝ) + (intCount (Zn 5) P 2 : ℝ))) / 6 :=
  Rows1.prop_3_1 hE1 hE2 P hP

/-- l.216: the 50 points of Table 2 lie in `{-1,0,1}⁵`. -/
theorem w_pts_cube : wPts ⊆ cubePts 5 :=
  Rows1.w_pts_cube

/-- l.216: the 50 points form a symmetric set. -/
theorem w_symm : -wPts = wPts :=
  Rows1.w_symm

/-- l.216: the 50 points span `ℝ⁵`. -/
theorem w_span : Spans wPts :=
  Rows1.w_span

/-- Theorem 1.3, l.98, l.216: `W ∈ O⁵`. -/
theorem thm_1_3_mem : InW (Zn 5) W :=
  Rows1.thm_1_3_mem

/-- Table 2 caption, l.196 (and abstract, Table 1 l.78): the 50 points `±p` are distinct and all 50 are vertices of `W`. -/
theorem tab2_vertices : wPts.ncard = 50 ∧ Set.extremePoints ℝ W = wPts :=
  Rows1.tab2_vertices

/-- Table 2 caption, l.196: `W` has (at least) 92 facets — 92 hyperplanes `{⟨u_j, x⟩ = b_j}`, each with `W` on one
side and not inside it, and containing 5 affinely independent vertices of `W`, no two cutting out the same face.
(That these are all the facets is not formalized: no faces of polytopes in Lean's library.) -/
theorem W_facets : ∃ (u : Fin 92 → Pt 5) (b : Fin 92 → ℝ),
    (∀ j, ∀ x ∈ W, u j ⬝ᵥ x ≤ b j) ∧ (∀ j, ∃ x ∈ W, u j ⬝ᵥ x < b j) ∧
    (∀ j, ∃ p : Fin 5 → Pt 5, (∀ i, p i ∈ wPts ∧ u j ⬝ᵥ p i = b j) ∧ AffineIndependent ℝ p) ∧
    Function.Injective (fun j => {x ∈ W | u j ⬝ᵥ x = b j}) :=
  WFacets.W_facets

/-- l.218: `G(W) = 117`. -/
theorem w_G : G (Zn 5) W = 117 :=
  Rows1.w_G

/-- l.218: `#(2W ∩ ℤ⁵) = 1815`. -/
theorem w_L2 : latCount (Zn 5) W 2 = 1815 :=
  Rows1.w_L2

/-- l.218: `#(int(2W) ∩ ℤ⁵) = 243`. -/
theorem w_int2 : intCount (Zn 5) W 2 = 243 :=
  Rows1.w_int2

/-- l.220: `A(W) = 1029`. -/
theorem w_A : (1 / 2 : ℝ) * ((latCount (Zn 5) W 2 : ℝ) + (intCount (Zn 5) W 2 : ℝ)) = 1029 :=
  Rows1.w_A

/-- Text versions up to 2.30, l.220 (no longer printed since 2.40; SUPPORT of the claim at l.220): `int(2W) ⊂ (-2,2)⁵`, so the lattice points of `int(2W)` lie in `{-1,0,1}⁵`, and `int(2W)` contains all
of them. -/
theorem w_int2_all : interior ((2 : ℝ) • W) ∩ Zn 5 = cubePts 5 :=
  Rows1.w_int2_all

/-- Theorem 1.3, l.99-101: the Ehrhart polynomial of `W` is
`1 + 101/10 k + 127/12 k² + 139/6 k³ + 557/12 k⁴ + 386/15 k⁵`, and `L_W(k)` is its value at every `k ≥ 0`. -/
theorem thm_1_3_poly (hEHR : EhrhartThm) (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hVolW : VolW) :
    ehrhartPoly (Zn 5) W = polyW ∧ ∀ k : ℕ, (latCount (Zn 5) W k : ℝ) = polyW.eval (k : ℝ) :=
  Rows1.thm_1_3_poly hEHR hE1 hE2 hVolW

/-- Theorem 1.3, l.102 (and l.220, abstract, Table 1 l.78): `g_1(W) = 101/10 > 10 = g_1(C_5)`. -/
theorem thm_1_3_g1 (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hVolW : VolW) :
    g (Zn 5) W 1 = 101 / 10 ∧ (101 / 10 : ℝ) > 10 ∧ g (Zn 5) (cube 5) 1 = 10 :=
  Rows1.thm_1_3_g1 hE1 hE2 hVolW

/-- l.220: the polynomial is determined by its values at `k = 0, …, n` (degree at most `n`). -/
theorem interp_unique (n : ℕ) (p q : Polynomial ℝ) (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (h : ∀ k ≤ n, p.eval (k : ℝ) = q.eval (k : ℝ)) : p = q :=
  Rows1.interp_unique n p q hp hq h

/-- l.220: `L_W(0) = 1`, `L_W(1..5) = 117, 1815, 10765, 39927, 112639`, and `L_W(6) = 265705` (the value
`L_W(6)` is no longer printed since text version 2.70; the row keeps it). -/
theorem w_L3456 (hEHR : EhrhartThm) (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hVolW : VolW) :
    latCount (Zn 5) W 0 = 1 ∧ latCount (Zn 5) W 1 = 117 ∧ latCount (Zn 5) W 2 = 1815 ∧
      latCount (Zn 5) W 3 = 10765 ∧ latCount (Zn 5) W 4 = 39927 ∧ latCount (Zn 5) W 5 = 112639 ∧
      latCount (Zn 5) W 6 = 265705 :=
  Rows1.w_L3456 hEHR hE1 hE2 hVolW

/-- Theorem 1.3, l.102, l.222 (and abstract, Table 1 l.78, l.143): for every `n = 5 + m ≥ 6`, `W × C_{n-5} ∈ Oⁿ`
and `g_1(W × C_{n-5}) = 101/10 + 2(n-5) = 2n + 1/10 > 2n = g_1(C_n)`. -/
theorem thm_1_3_prod (hEHR : EhrhartThm) (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hVolW : VolW) (m : ℕ)
    (hm : 1 ≤ m) :
    InW (Zn (5 + m)) (prod W (cube m)) ∧
      g (Zn (5 + m)) (prod W (cube m)) 1 = 101 / 10 + 2 * m ∧
      (101 / 10 + 2 * m : ℝ) = 2 * ((5 + m : ℕ) : ℝ) + 1 / 10 ∧
      2 * ((5 + m : ℕ) : ℝ) + 1 / 10 > 2 * ((5 + m : ℕ) : ℝ) ∧
      g (Zn (5 + m)) (cube (5 + m)) 1 = 2 * ((5 + m : ℕ) : ℝ) :=
  Rows1.thm_1_3_prod hEHR hE1 hE2 hVolW m hm

/-! ## Section 4: dimension four, the key inequality and few lattice points -/

/-- Lemma 4.1, l.231-237: for `P ∈ O^4_Λ`, `g_1 + g_3 = g_2 + g_4 = (G-1)/2`. -/
theorem lem_4_1 (hE2 : EhrhartReciprocity) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4))
    (hP : InW (lat B) P) :
    g (lat B) P 1 + g (lat B) P 3 = ((G (lat B) P : ℝ) - 1) / 2 ∧
      g (lat B) P 2 + g (lat B) P 4 = ((G (lat B) P : ℝ) - 1) / 2 :=
  Rows1.lem_4_1 hE2 B hB P hP

/-- l.145: since `P ∈ O⁴` has exactly one interior lattice point, `L_P(-1) = 1`. -/
theorem recip_m1_dim4 (hE2 : EhrhartReciprocity) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0)
    (P : Set (Pt 4)) (hP : InW (lat B) P) : (ehrhartPoly (lat B) P).eval (-1) = 1 :=
  Rows1.recip_m1_dim4 hE2 B hB P hP

/-- Proposition 4.2, l.240, l.248: `g_4 = vol(P)/det Λ ≤ 16` (Minkowski's theorem in the coordinates of a basis of
`Λ`). -/
theorem prop_4_2_g4 (hE1 : EhrhartLeading) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4))
    (hP : InW (lat B) P) : g (lat B) P 4 = (volume P).toReal / |B.det| ∧ g (lat B) P 4 ≤ 16 :=
  Rows1.prop_4_2_g4 hE1 B hB P hP

/-- Proposition 4.2, l.240, l.248: `g_3 ≤ 2 g_4 ≤ 32`. -/
theorem prop_4_2_g3 (hE1 : EhrhartLeading) (hE3 : FacetFormula) (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P) :
    g (lat B) P 3 ≤ 2 * g (lat B) P 4 ∧ 2 * g (lat B) P 4 ≤ 32 :=
  Rows1.prop_4_2_g3 hE1 hE3 B hB P hP

/-- Proposition 4.2, l.241-243 (and l.145-148): `g_1 ≤ 8 ⇔ G ≤ σ + 17`, for the lattice surface area
`σ = Σ_F relvol(F)` given by (E3)'s facet data. -/
theorem prop_4_2_iff (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) (B : Matrix (Fin 4) (Fin 4) ℝ)
    (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P) :
    (∃ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b) ∧
      ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b →
        (g (lat B) P 1 ≤ 8 ↔ (G (lat B) P : ℝ) ≤ ∑ j, relvol j + 17) :=
  Rows1.prop_4_2_iff hE2 hE3 B hB P hP

/-- Proposition 4.2, l.244 (and l.149): if `g_1 ≤ 8` then `g_2 ≤ g_4 + 8 ≤ 24`. -/
theorem prop_4_2_g2 (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P)
    (h1 : g (lat B) P 1 ≤ 8) : g (lat B) P 2 ≤ g (lat B) P 4 + 8 ∧ g (lat B) P 4 + 8 ≤ 24 :=
  Rows1.prop_4_2_g2 hE1 hE2 hE3 B hB P hP h1

/-- l.251: Theorem 1.2 is equivalent to the key inequality `G ≤ σ + 17` on `O⁴` (σ from (E3)'s facet data). -/
theorem key_equiv (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) :
    (∀ P : Set (Pt 4), InW (Zn 4) P → g (Zn 4) P 1 ≤ 8 ∧ g (Zn 4) P 2 ≤ 24) ↔
      ∀ P : Set (Pt 4), InW (Zn 4) P → ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ),
        IsFacetData 1 P m relvol b → (G (Zn 4) P : ℝ) ≤ ∑ j, relvol j + 17 :=
  Rows1.key_equiv hE1 hE2 hE3

/-- l.251-254, inequality (star): the key inequality reads `Σ_F NVol(F) ≥ 6G - 102`, `NVol(F) = 3! relvol(F)`. -/
theorem star_iff (hE3 : FacetFormula) (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4))
    (hP : InW (lat B) P) :
    (∃ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b) ∧
      ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b →
        ((G (lat B) P : ℝ) ≤ ∑ j, relvol j + 17 ↔ ∑ j, 6 * relvol j ≥ 6 * (G (lat B) P : ℝ) - 102) :=
  Rows1.star_iff hE3 B hB P hP

/-- Lemma 4.3 proof, l.262, the arithmetic: a 3-sphere f-vector with `f_1 ≥ 4f_0 - 10` and the Dehn-Sommerville
relations has `f_3 = f_1 - f_0 ≥ 3f_0 - 10`; and `3G - 13 > 6G - 102` for `G ≤ 29`. -/
theorem lem_4_3_arith (f : Fin 4 → ℕ) (hW : (f 1 : ℤ) ≥ 4 * (f 0 : ℤ) - 10)
    (hDS1 : (f 0 : ℤ) - f 1 + f 2 - f 3 = 0) (hDS2 : 2 * f 2 = 4 * f 3) :
    (f 3 : ℤ) = f 1 - f 0 ∧ (f 3 : ℤ) ≥ 3 * (f 0 : ℤ) - 10 ∧ ∀ Gc : ℤ, Gc ≤ 29 → 3 * Gc - 13 > 6 * Gc - 102 :=
  Rows1.lem_4_3_arith f hW hDS1 hDS2

/-- Lemma 4.3, l.257-259 (and l.149): if `P ∈ O^4_Λ` and `G ≤ 29`, then (star) holds with strict inequality;
hence `g_1 < 8`. -/
theorem lem_4_3 (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) (hTRI : BoundaryTriangulation)
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P)
    (hG : G (lat B) P ≤ 29) :
    ((∃ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b) ∧
      ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b →
        ∑ j, 6 * relvol j > 6 * (G (lat B) P : ℝ) - 102) ∧ g (lat B) P 1 < 8 :=
  Rows1.lem_4_3 hE2 hE3 hTRI B hB P hP hG

/-- Remark 4.4, l.266: the lower bound theorem's bound `3G - 13` proves (star) (`> 6G - 102`) exactly when `G ≤ 29`. -/
theorem rem_4_4_only (Gc : ℤ) : 3 * Gc - 13 > 6 * Gc - 102 ↔ Gc ≤ 29 :=
  Rows1.rem_4_4_only Gc

/-! ## Section 5: three cases -/

/-- l.275: `M(P)` is finite (`P` contains a ball around `0`). -/
theorem M_finite (P : Set (Pt 4)) (hP : InW (Zn 4) P) : (MP P).Finite :=
  Sec5.M_finite P hP

/-- l.275: `M(P)` is symmetric. -/
theorem M_symm (P : Set (Pt 4)) (u : Pt 4) (hu : u ∈ MP P) : -u ∈ MP P :=
  Sec5.M_symm P u hu

/-- l.275: `⟨u, x⟩ ∈ {-1, 0, 1}` for `u ∈ M(P)` and `x ∈ P ∩ ℤ⁴`. -/
theorem M_values (P : Set (Pt 4)) (u : Pt 4) (hu : u ∈ MP P) (x : Pt 4) (hx : x ∈ P ∩ Zn 4) :
    u ⬝ᵥ x = -1 ∨ u ⬝ᵥ x = 0 ∨ u ⬝ᵥ x = 1 :=
  Sec5.M_values P u hu x hx

/-- The case split (l.275, Figure 2 l.277-288, l.373): every `P ∈ O⁴` is in Case I, Case II (`r(P) = 4`, no basis)
or Case III (`r(P) ≤ 3`). -/
theorem thm_1_2_case_split (P : Set (Pt 4)) (hP : InW (Zn 4) P) :
    CaseI P ∨ (rP P = 4 ∧ ¬ CaseI P) ∨ rP P ≤ 3 :=
  Sec5.thm_1_2_case_split P hP

/-- Case I, l.291 (and l.151 (a), Figure 2): if the rows of `U ∈ GL_4(ℤ)` lie in `M(P)`, then `UP ⊂ C_4`,
`UP = conv S` for `S = UP ∩ ℤ⁴ ⊂ {-1,0,1}⁴`, `S` is symmetric and saturated, and `P` is unimodularly equivalent to
`UP`. -/
theorem case_I (P : Set (Pt 4)) (hP : InW (Zn 4) P) (U : Matrix (Fin 4) (Fin 4) ℤ) (hU : IsGLZ U)
    (hrows : ∀ i, ofInt (U i) ∈ MP P) :
    ((fun x => (toReal U).mulVec x) '' P) ⊆ cube 4 ∧
      (fun x => (toReal U).mulVec x) '' P = convexHull ℝ (((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4) ∧
      ((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4 ⊆ cubePts 4 ∧
      -(((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4) = ((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4 ∧
      Saturated (Zn 4) (((fun x => (toReal U).mulVec x) '' P) ∩ Zn 4) ∧
      UnimodEquiv P ((fun x => (toReal U).mulVec x) '' P) :=
  Sec5.case_I P hP U hU hrows

/-- Case II, l.294: if the rows of `U` lie in `M(P)` and are linearly independent but `M(P)` contains no basis, then
`d = |det U| ≥ 2`. -/
theorem case_II_d_ge_2 (P : Set (Pt 4)) (hP : InW (Zn 4) P) (hno : ¬ CaseI P) (U : Matrix (Fin 4) (Fin 4) ℤ)
    (hrows : ∀ i, ofInt (U i) ∈ MP P) (hdet : U.det ≠ 0) : 2 ≤ |U.det| :=
  Sec5.case_II_d_ge_2 P hP hno U hrows hdet

/-- Case II, l.294-296: `x ↦ Ux` carries `ℤ⁴` onto `Γ = U ℤ⁴` and `P` into `C_4`; `(P, ℤ⁴) ≅ (UP, Γ)`,
`UP ∈ O^4_Γ`, `L_{UP,Γ} = L_P`, `UP = conv S` for the `Γ`-saturated symmetric `S = UP ∩ Γ ⊂ Γ ∩ {-1,0,1}⁴`, and
`G(P) ≤ #(Γ ∩ {-1,0,1}⁴)`. -/
theorem case_II_transfer (P : Set (Pt 4)) (hP : InW (Zn 4) P) (U : Matrix (Fin 4) (Fin 4) ℤ)
    (hrows : ∀ i, ofInt (U i) ∈ MP P) (hdet : U.det ≠ 0) :
    IsoPair P (Zn 4) ((fun x => (toReal U).mulVec x) '' P) (subLat U) ∧
      InW (subLat U) ((fun x => (toReal U).mulVec x) '' P) ∧
      ((fun x => (toReal U).mulVec x) '' P) ⊆ cube 4 ∧
      (∀ k, latCount (subLat U) ((fun x => (toReal U).mulVec x) '' P) k = latCount (Zn 4) P k) ∧
      (fun x => (toReal U).mulVec x) '' P =
        convexHull ℝ (((fun x => (toReal U).mulVec x) '' P) ∩ subLat U) ∧
      Saturated (subLat U) (((fun x => (toReal U).mulVec x) '' P) ∩ subLat U) ∧
      -(((fun x => (toReal U).mulVec x) '' P) ∩ subLat U) = ((fun x => (toReal U).mulVec x) '' P) ∩ subLat U ∧
      ((fun x => (toReal U).mulVec x) '' P) ∩ subLat U ⊆ subLat U ∩ cubePts 4 ∧
      G (Zn 4) P ≤ (subLat U ∩ cubePts 4).ncard :=
  Sec5.case_II_transfer P hP U hrows hdet

/-- Hadamard's inequality for `{-1,0,1}` matrices of size 4 (used at l.298): `|det| ≤ 16`. -/
theorem det_cube_le_16 (M : Matrix (Fin 4) (Fin 4) ℤ) (hM : ∀ i j, |M i j| ≤ 1) : |M.det| ≤ 16 :=
  Sec5.det_cube_le_16 M hM

/-- Case II, l.298: `d ≤ 16`. -/
theorem case_II_d_le_16 (P : Set (Pt 4)) (hP : InW (Zn 4) P) (U : Matrix (Fin 4) (Fin 4) ℤ)
    (hrows : ∀ i, ofInt (U i) ∈ MP P) (hdet : U.det ≠ 0) : |U.det| ≤ 16 :=
  Sec5.case_II_d_le_16 P hP U hrows hdet

/-- Case II, l.300: the sublattices of `ℤ⁴` of index 2 are exactly the `Γ_I`, `I` nonempty. -/
theorem index2_eq_gammaI :
    (∀ B : Matrix (Fin 4) (Fin 4) ℤ, |B.det| = 2 → ∃ I : Finset (Fin 4), I.Nonempty ∧ subLat B = gammaI I) ∧
      ∀ I : Finset (Fin 4), I.Nonempty → ∃ B : Matrix (Fin 4) (Fin 4) ℤ, |B.det| = 2 ∧ subLat B = gammaI I :=
  Sec5.index2_eq_gammaI

/-- Case II, l.300: a point of `{-1,0,1}⁴` lies in `Γ_I` exactly when an even number of its coordinates in `I` are
nonzero. -/
theorem gammaI_mem_iff (I : Finset (Fin 4)) (z : Fin 4 → ℤ) (hz : ∀ i, -1 ≤ z i ∧ z i ≤ 1) :
    ofInt z ∈ gammaI I ↔ Even (I.filter (fun i => z i ≠ 0)).card :=
  Sec5.gammaI_mem_iff I z hz

/-- Case II, l.302: `#(Γ_I ∩ {-1,0,1}⁴) = 3^{4-m} (3^m + (-1)^m)/2 = 27, 45, 39, 41` for `m = |I| = 1, 2, 3, 4`. -/
theorem gammaI_counts (I : Finset (Fin 4)) (hI : I.Nonempty) :
    2 * ((gammaI I ∩ cubePts 4).ncard : ℤ) = 3 ^ (4 - I.card) * (3 ^ I.card + (-1) ^ I.card) ∧
      (I.card = 1 → (gammaI I ∩ cubePts 4).ncard = 27) ∧ (I.card = 2 → (gammaI I ∩ cubePts 4).ncard = 45) ∧
      (I.card = 3 → (gammaI I ∩ cubePts 4).ncard = 39) ∧ (I.card = 4 → (gammaI I ∩ cubePts 4).ncard = 41) :=
  Sec5.gammaI_counts I hI

/-- Case II, l.304 (and l.151 (b), Figure 2): since `27 < 31`, in Case II `d = 2` and `Γ = Γ_I` with
`|I| ∈ {2, 3, 4}` (using Computation 2). -/
theorem case_II_index2 (P : Set (Pt 4)) (hP : InW (Zn 4) P) (hG : 31 ≤ G (Zn 4) P)
    (U : Matrix (Fin 4) (Fin 4) ℤ) (hrows : ∀ i, ofInt (U i) ∈ MP P) (hdet : U.det ≠ 0) (hno : ¬ CaseI P) :
    |U.det| = 2 ∧ ∃ I : Finset (Fin 4), 2 ≤ I.card ∧ subLat U = gammaI I :=
  Sec5.case_II_index2 C2P.comp2_proof P hP hG U hrows hdet hno

/-- Case III, l.307: `P ∈ O⁴` has a frame, and `D ≥ 1` since `P` spans `ℝ⁴`. -/
theorem frame_D_pos (P : Set (Pt 4)) (hP : InW (Zn 4) P) :
    (∃ v, IsFrame P v) ∧ ∀ v, IsFrame P v → 1 ≤ |(colMat v).det| :=
  Sec5.frame_D_pos P hP

/-- Case III, l.307: `x ↦ V⁻¹x` carries `ℤ⁴` onto `Λ = V⁻¹ℤ⁴ ⊇ ℤ⁴`, of index `D` over `ℤ⁴`. -/
theorem frame_lattice (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    Zn 4 ⊆ frameLat v ∧ (fun x => ((colMat v)⁻¹).mulVec x) '' Zn 4 = frameLat v ∧
      (indexOver (frameLat v) : ℝ) = |(colMat v).det| :=
  Sec5.frame_lattice P hP v hv

/-- Lemma 5.1 (i), l.312: `S ⊂ Λ ∩ C_4`, `S = -S`, and `S` contains the unit vectors `±e_i`. -/
theorem lem_5_1_i (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    frameSet P v ⊆ frameLat v ∩ cube 4 ∧ -(frameSet P v) = frameSet P v ∧
      ∀ i, unitVec i ∈ frameSet P v ∧ -unitVec i ∈ frameSet P v :=
  Sec5.lem_5_1_i P hP v hv

/-- Lemma 5.1 (ii), l.313: `|det(s_1, …, s_4)| ≤ 1` for all `s_i ∈ S`. -/
theorem lem_5_1_ii (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v)
    (s : Fin 4 → Pt 4) (hs : ∀ i, s i ∈ frameSet P v) : |(colMat s).det| ≤ 1 :=
  Sec5.lem_5_1_ii P hP v hv s hs

/-- Lemma 5.1 (iii), l.314: `conv S ∩ Λ = S` and `int(conv S) ∩ Λ = {0}`. -/
theorem lem_5_1_iii (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    Saturated (frameLat v) (frameSet P v) ∧ interior (convexHull ℝ (frameSet P v)) ∩ frameLat v = {0} :=
  Sec5.lem_5_1_iii P hP v hv

/-- Lemma 5.1 (iv), l.315: `Λ` contains no point `c ≠ 0` with `|c_1| + ⋯ + |c_4| < 1`. -/
theorem lem_5_1_iv (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    NoShortL1 (frameLat v) :=
  Sec5.lem_5_1_iv P hP v hv

/-- Lemma 5.1 (v) proof, l.323: the cross-polytope `conv{±v_i}` has volume `(2⁴/4!) D`. -/
theorem crosspoly_vol (v : Fin 4 → Pt 4) :
    volume (convexHull ℝ (Set.range v ∪ Set.range (fun i => -v i))) =
      ENNReal.ofReal ((2 : ℝ) ^ 4 / 24 * |(colMat v).det|) :=
  Sec5.crosspoly_vol v

/-- Lemma 5.1 (v) proof, l.323: `D ≤ 24`; if `D = 24` then `P = conv{±v_i}` and `vol P = 16`. -/
theorem frame_D_le_24 (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    |(colMat v).det| ≤ 24 ∧ (|(colMat v).det| = 24 →
      P = convexHull ℝ (Set.range v ∪ Set.range (fun i => -v i)) ∧ volume P = 16) :=
  Sec5.frame_D_le_24 P hP v hv

/-- Lemma 5.1 (v) proof, l.323: if `P ∈ O⁴` has volume 16, the translates `½P + z`, `z ∈ ℤ⁴`, tile `ℝ⁴` (disjoint
interiors and total density 1). -/
theorem half_translates_tile (P : Set (Pt 4)) (hP : InW (Zn 4) P) (hvol : volume P = 16) :
    TilesByZ4 ((1 / 2 : ℝ) • P) :=
  Sec5.half_translates_tile P hP hvol

/-- Lemma 5.1 (v), l.316: `D ≤ 23`. -/
theorem lem_5_1_v (hTILE : CrossPolytopeNoTiling) (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4)
    (hv : IsFrame P v) : |(colMat v).det| ≤ 23 :=
  Sec5.lem_5_1_v hTILE P hP v hv

/-- l.326: a lattice of index `D` over `ℤ⁴` lies in `(1/D)ℤ⁴`, so the set of frame lattices is finite. -/
theorem frameLat_finite :
    (∀ V : Matrix (Fin 4) (Fin 4) ℤ, V.det ≠ 0 →
        lat (toReal V)⁻¹ ⊆ (1 / (|V.det| : ℝ)) • Zn 4) ∧ {Λ | IsFrameLattice Λ}.Finite :=
  Sec5.frameLat_finite

/-- l.326: the signed permutations act on the frame lattices. -/
theorem signedPerm_frameLat (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (Λ : Set (Pt 4))
    (hΛ : IsFrameLattice Λ) : IsFrameLattice (signedPerm σ '' Λ) :=
  Sec5.signedPerm_frameLat σ Λ hΛ

/-- l.326, the reasons of the transfer: `⟨u, Vs⟩ = ⟨Vᵀu, s⟩`, and `Vᵀℤ⁴ = Λ*`, the dual lattice of the frame lattice
`Λ = V⁻¹ℤ⁴` (here `V = colMat v`). -/
theorem frame_dual (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    (∀ u s : Pt 4, u ⬝ᵥ (colMat v).mulVec s = ((colMat v).transpose.mulVec u) ⬝ᵥ s) ∧
      (fun u => (colMat v).transpose.mulVec u) '' Zn 4 = dualLat (frameLat v) :=
  R280.frame_dual_proof P hP v hv

/-- l.326: `u ∈ M(P)` iff `Vᵀu ∈ M(S)`, so `r(P) = r(S)`. -/
theorem frame_M_transfer (P : Set (Pt 4)) (hP : InW (Zn 4) P) (v : Fin 4 → Pt 4) (hv : IsFrame P v) :
    (∀ u, u ∈ MP P ↔ (Matrix.transpose (colMat v)).mulVec u ∈ MS (frameLat v) (frameSet P v)) ∧
      rP P = rS (frameLat v) (frameSet P v) :=
  Sec5.frame_M_transfer P hP v hv

/-- l.326 (and l.151 (c), Figure 2): in Case III, `(P, ℤ⁴) ≅ (conv S, Λ)` for one of the 39 representatives `Λ`
and a set `S ∈ S(Λ)` (Lean: `InA`) with `#S ≥ 31` and `r(S) ≤ 3`; in particular `L_{conv S, Λ} = L_P` (using Computation 4). -/
theorem case_III_transfer (hTILE : CrossPolytopeNoTiling) (hC4 : Comp4) (P : Set (Pt 4)) (hP : InW (Zn 4) P)
    (hG : 31 ≤ G (Zn 4) P) (hr : rP P ≤ 3) :
    ∃ j S, Comp5Input j S ∧ IsoPair P (Zn 4) (convexHull ℝ S) (frameRep j) ∧
      ∀ k, latCount (frameRep j) (convexHull ℝ S) k = latCount (Zn 4) P k :=
  Sec5.case_III_transfer hTILE hC4 P hP hG hr

/-! ## Section 6: the computations -/

/-- Lemma 6.1 (i), l.337: if `v` is a vertex of `conv Q`, then `Q' = Q \ {v, -v}` is symmetric and saturated. -/
theorem lem_6_1_i (n : ℕ) (Λ Q : Set (Pt n)) (hQΛ : Q ⊆ Λ) (hfin : Q.Finite) (hsymm : -Q = Q)
    (hsat : Saturated Λ Q) (v : Pt n) (hv : v ∈ Set.extremePoints ℝ (convexHull ℝ Q)) :
    -(Q \ {v, -v}) = Q \ {v, -v} ∧ Saturated Λ (Q \ {v, -v}) :=
  S6E.lem_6_1_i n Λ Q hQΛ hfin hsymm hsat v hv

/-- Lemma 6.1 (ii), l.338: if `S ⊊ Q` is symmetric and saturated, then some vertex `v` of `conv Q` is not in `S`,
and `S ⊆ Q \ {v, -v}`. -/
theorem lem_6_1_ii (n : ℕ) (Λ Q : Set (Pt n)) (hQΛ : Q ⊆ Λ) (hfin : Q.Finite) (hsymm : -Q = Q)
    (hsat : Saturated Λ Q) (S : Set (Pt n)) (hSQ : S ⊂ Q) (hSsymm : -S = S) (hSsat : Saturated Λ S) :
    ∃ v ∈ Set.extremePoints ℝ (convexHull ℝ Q), v ∉ S ∧ S ⊆ Q \ {v, -v} :=
  S6E.lem_6_1_ii n Λ Q hQΛ hfin hsymm hsat S hSQ hSsymm hSsat

/-- l.332, l.346: "such a walk reaches every saturated symmetric subset of the full set": every saturated symmetric
`S ⊆ Q` is reached from `Q` by deleting pairs of opposite vertices
through saturated symmetric sets that contain `S` (so a search that stops at 31 points misses no set with at least
31 points). -/
theorem walk_reach (n : ℕ) (Λ Q : Set (Pt n)) (hQΛ : Q ⊆ Λ) (hfin : Q.Finite) (hsymm : -Q = Q)
    (hsat : Saturated Λ Q) (S : Set (Pt n)) (hSQ : S ⊆ Q) (hSsymm : -S = S) (hSsat : Saturated Λ S) :
    Relation.ReflTransGen (fun A A' : Set (Pt n) => S ⊆ A' ∧ -A' = A' ∧ Saturated Λ A' ∧
      ∃ v ∈ Set.extremePoints ℝ (convexHull ℝ A), A' = A \ {v, -v}) Q S :=
  S6E.walk_reach n Λ Q hQΛ hfin hsymm hsat S hSQ hSsymm hSsat

/-- l.332: "This loses no class": a symmetry `σ` (a signed permutation that preserves the lattice `Λ`) maps saturated
symmetric sets to saturated symmetric sets and the vertices of `conv Q` to those of `conv σQ`, so the sets obtained
from `σQ` by deleting a pair of opposite vertices are the images under `σ` of those obtained from `Q`. -/
theorem walk_symm (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (Λ Q : Set (Pt 4)) (hσ : Preserves Λ σ) :
    (Saturated Λ Q → Saturated Λ (signedPerm σ '' Q)) ∧ (-Q = Q → -(signedPerm σ '' Q) = signedPerm σ '' Q) ∧
      signedPerm σ '' Set.extremePoints ℝ (convexHull ℝ Q) =
        Set.extremePoints ℝ (convexHull ℝ (signedPerm σ '' Q)) ∧
      {A | ∃ w ∈ Set.extremePoints ℝ (convexHull ℝ (signedPerm σ '' Q)), A = signedPerm σ '' Q \ {w, -w}} =
        {A | ∃ v ∈ Set.extremePoints ℝ (convexHull ℝ Q), A = signedPerm σ '' (Q \ {v, -v})} :=
  R280.walk_symm_proof σ Λ Q hσ

/-- Computation 1, l.349: a hyperplane through `0` contains at most 27 points of `{-1,0,1}⁴`. -/
theorem hyperplane_le_27 (w : Pt 4) (hw : w ≠ 0) : {x | x ∈ cubePts 4 ∧ w ⬝ᵥ x = 0}.ncard ≤ 27 :=
  S6F.hyperplane_le_27 w hw

/-- Computation 1, l.349: each input set spans `ℝ⁴`, so `conv S ∈ O⁴` by Lemma 2.1. -/
theorem comp1_mem (S : Set (Pt 4)) (hS : Comp1Input S) : Spans S ∧ InW (Zn 4) (convexHull ℝ S) :=
  S6F.comp1_mem S hS

/-- l.151 (d): in each case only finitely many sets of lattice points remain. -/
theorem finitely_many_sets :
    {S | Comp1Input S}.Finite ∧ (∀ m, {S | Comp3Input m S}.Finite) ∧ ∀ j, {S | Comp5Input j S}.Finite :=
  S6F.finitely_many_sets

/-- Computation 2, l.353 (and l.302): the maximum for `d = 2` is `45`. -/
theorem comp2_d2_max :
    (∀ B : Matrix (Fin 4) (Fin 4) ℤ, |B.det| = 2 → (subLat B ∩ cubePts 4).ncard ≤ 45) ∧
      ∃ B : Matrix (Fin 4) (Fin 4) ℤ, |B.det| = 2 ∧ Spans (subLat B ∩ cubePts 4) ∧
        (subLat B ∩ cubePts 4).ncard = 45 :=
  S6F.comp2_d2_max

/-- Computation 2, l.353 (used at l.304), its result: for every sublattice `B ℤ⁴` of index `d`, `2 ≤ d ≤ 16`, whose points
in `{-1,0,1}⁴` span `ℝ⁴`, the number of these points is at most `45` if `d = 2` and at most `27` if `d ≥ 3`, and `45`
is attained. Proved (the count of the 40,406 sublattices stays a computer check). -/
theorem comp2_result : Comp2 :=
  C2P.comp2_proof

/-- Computation 3, l.357: a permutation of coordinates carries `Γ_I` onto `Γ_J` when `|I| = |J|`. -/
theorem gammaI_perm (I J : Finset (Fin 4)) (h : I.card = J.card) :
    ∃ π : Equiv.Perm (Fin 4), signedPerm (π, fun _ => false) '' gammaI I = gammaI J :=
  S6F.gammaI_perm I J h

/-- Computation 3, l.357: each input `conv S` lies in `O^4_{Γ_m}`. -/
theorem comp3_mem (m : ℕ) (S : Set (Pt 4)) (hS : Comp3Input m S) : InW (gammaM m) (convexHull ℝ S) :=
  S6F.comp3_mem m S hS

/-- Computation 4, l.361: for `U ∈ GL_4(ℤ)` the frame matrices `V` and `UV` give the same lattice `V⁻¹ℤ⁴`. -/
theorem frame_lat_GL (V U : Matrix (Fin 4) (Fin 4) ℤ) (hV : V.det ≠ 0) (hU : IsGLZ U) :
    lat (toReal (U * V))⁻¹ = lat (toReal V)⁻¹ :=
  S6F.frame_lat_GL V U hV hU

/-- Computation 5, l.369: `M` reverses inclusion, so a subset of a set `Q'` with `r(Q') = 4` also has `r = 4`. -/
theorem M_antitone (Λ Q Q' : Set (Pt 4)) (h : Q ⊆ Q') :
    MS Λ Q' ⊆ MS Λ Q ∧ rS Λ Q' ≤ rS Λ Q ∧ (rS Λ Q' = 4 → rS Λ Q = 4) :=
  S6E.M_antitone Λ Q Q' h

/-- RETIRED (Computation 5's walk; printed in earlier versions of the paper, last: text version 2.80; not printed in
this version): every `S ∈ S(Λ)` with `r(S) ≤ 3` lies in a maximal member `Q` of `S(Λ)` with `r(Q) ≤ 3`,
and `r(Q) ≤ r(S)`. -/
theorem comp5_maximal (j : Fin 39) (S : Set (Pt 4)) (hS : InA (frameRep j) S) (hr : rS (frameRep j) S ≤ 3) :
    ∃ Q, InA (frameRep j) Q ∧ S ⊆ Q ∧ rS (frameRep j) Q ≤ rS (frameRep j) S ∧
      ∀ Q', InA (frameRep j) Q' → rS (frameRep j) Q' ≤ 3 → Q ⊆ Q' → Q' = Q :=
  S6E.comp5_maximal j S hS hr

/-- Computation 5, l.369: every saturated symmetric set between `S⁻` and `S⁺` lies in exactly one branch: it
avoids `±v` and lies in `S⁺ \ {±v}`, or it contains `±v` and `conv(S⁻ ∪ {±v}) ∩ Λ`. -/
theorem sandwich_split (Λ Sm Sp S : Set (Pt 4)) (v : Pt 4) (hSm : Sm ⊆ S) (hSp : S ⊆ Sp) (hsat : Saturated Λ S)
    (hsymm : -S = S) (hv : v ∈ Λ) :
    (v ∉ S ∧ S ⊆ Sp \ {v, -v}) ∨ (v ∈ S ∧ convexHull ℝ (Sm ∪ {v, -v}) ∩ Λ ⊆ S) :=
  S6E.sandwich_split Λ Sm Sp S v hSm hSp hsat hsymm hv

/-- Computation 5, l.369: the pruning of the sandwich search is sound ("A pair `±y` in `S⁺` for which `S⁻ ∪ {±y}`
violates (ii) is removed from `S⁺`, since no member contains it together with `S⁻`"): no `S ∈ S(Λ)` contains a set `T` that violates
(ii) or has a nonzero point of `Λ` in the interior of its convex hull; a point `x` that breaks (ii) together with
`T` is in no `S ∈ S(Λ)` containing `T`; and a set `S ⊆ S⁺` has `#S < 31` if `#S⁺ < 31` and `r(S) = 4` if
`r(S⁺) = 4`. -/
theorem sandwich_prune (Λ T S Sp : Set (Pt 4)) (hS : InA Λ S) (hTS : T ⊆ S) :
    (∀ s : Fin 4 → Pt 4, (∀ i, s i ∈ T) → |(colMat s).det| ≤ 1) ∧
      interior (convexHull ℝ T) ∩ Λ ⊆ {0} ∧
      (∀ x, ∀ s : Fin 4 → Pt 4, (∀ i, s i ∈ insert x T) → 1 < |(colMat s).det| → x ∉ S) ∧
      (S ⊆ Sp → Sp.Finite → Sp.ncard < 31 → S.ncard < 31) ∧ (S ⊆ Sp → rS Λ Sp = 4 → rS Λ S = 4) :=
  S6E.sandwich_prune Λ T S Sp hS hTS

/-- Computation 5, l.367: the two start sets of the sandwich search. For a frame
lattice `Λ`, the set `S⁻ = conv{±e_1, …, ±e_4} ∩ Λ` is in `S(Λ)` and lies in every member of `S(Λ)`, and every member
of `S(Λ)` lies in
the upper set `S⁺ = Λ ∩ C_4`. -/
theorem sandwich_start (Λ : Set (Pt 4)) (hΛ : IsFrameLattice Λ) :
    InA Λ (convexHull ℝ (Set.range unitVec ∪ Set.range (fun i => -unitVec i)) ∩ Λ) ∧
      convexHull ℝ (Set.range unitVec ∪ Set.range (fun i => -unitVec i)) ∩ Λ ⊆ Λ ∩ cube 4 ∧
      ∀ S : Set (Pt 4), InA Λ S →
        convexHull ℝ (Set.range unitVec ∪ Set.range (fun i => -unitVec i)) ∩ Λ ⊆ S ∧ S ⊆ Λ ∩ cube 4 :=
  Sandwich.sandwich_start_proof Λ hΛ

/-- Computation 5, l.369: "Each include step keeps" `S⁻` in the family `S(Λ)` (printed `A(Λ)`), "so these sets are
members": if `S⁻ ∈ S(Λ)` and the pair `±v` is taken from `S⁺ ⊆ Λ ∩ C_4`, and the new lower set `conv(S⁻ ∪ {±v}) ∩ Λ`
satisfies (ii) and has no nonzero point of `Λ` in the interior of its convex hull, then the new lower set is in
`S(Λ)`. With `sandwich_start`, the lower sets of the search are members. -/
theorem sandwich_include_member (Λ Sm : Set (Pt 4)) (hΛ : IsFrameLattice Λ) (hSm : InA Λ Sm) (v : Pt 4)
    (hv : v ∈ Λ ∩ cube 4)
    (h2 : ∀ s : Fin 4 → Pt 4, (∀ i, s i ∈ convexHull ℝ (Sm ∪ {v, -v}) ∩ Λ) → |(colMat s).det| ≤ 1)
    (h3 : interior (convexHull ℝ (convexHull ℝ (Sm ∪ {v, -v}) ∩ Λ)) ∩ Λ ⊆ {0}) :
    InA Λ (convexHull ℝ (Sm ∪ {v, -v}) ∩ Λ) :=
  R280.sandwich_include_member_proof Λ Sm hΛ hSm v hv h2 h3

/-- Computation 5, l.369: a pair `(S⁻, S⁺)` that a signed permutation `σ` preserving `Λ` "carries onto a pair met
earlier in the search is discarded, since the permutation carries the sets between the two pairs onto each other":
`σ` carries the saturated symmetric sets, and the members of `S(Λ)`, between `S⁻` and `S⁺` onto those between `σS⁻`
and `σS⁺`. -/
theorem sandwich_symm (Λ Sm Sp : Set (Pt 4)) (σ : Equiv.Perm (Fin 4) × (Fin 4 → Bool)) (hσ : Preserves Λ σ) :
    (fun S => signedPerm σ '' S) '' {S | Saturated Λ S ∧ -S = S ∧ Sm ⊆ S ∧ S ⊆ Sp} =
        {S | Saturated Λ S ∧ -S = S ∧ signedPerm σ '' Sm ⊆ S ∧ S ⊆ signedPerm σ '' Sp} ∧
      (fun S => signedPerm σ '' S) '' {S | InA Λ S ∧ Sm ⊆ S ∧ S ⊆ Sp} =
        {S | InA Λ S ∧ signedPerm σ '' Sm ⊆ S ∧ S ⊆ signedPerm σ '' Sp} :=
  R280.sandwich_symm_proof Λ Sm Sp σ hσ

/-- l.330, Computation 5: for each set `S` that Computation 5 lists, the numbers of lattice points of `k conv S`
(`k = 1, 2, 3`) and of the interior of `k conv S` (`k = 1, 2`) "give its values at `k = -2, …, 3` by (E1) and (E2)
and so determine it": with respect to the frame lattice, the polynomial is `1` at `0`, `L(k)` at `k = 1, 2, 3`, and
`#(int(k conv S) ∩ Λ)` at `-k` for `k = 1, 2` ((E2) with `n = 4`; the value at `0` holds by counting, without (E1));
a polynomial of degree at most `4` with these six values is the Ehrhart polynomial. -/
theorem poly_six_values (hE2 : EhrhartReciprocity) (j : Fin 39) (S : Set (Pt 4)) (hS : Comp5Input j S) :
    (ehrhartPoly (frameRep j) (convexHull ℝ S)).eval 0 = 1 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 3 →
        (ehrhartPoly (frameRep j) (convexHull ℝ S)).eval (k : ℝ) = latCount (frameRep j) (convexHull ℝ S) k) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 2 →
        (ehrhartPoly (frameRep j) (convexHull ℝ S)).eval (-(k : ℝ)) = intCount (frameRep j) (convexHull ℝ S) k) ∧
      ∀ p : Polynomial ℝ, p.natDegree ≤ 4 → p.eval 0 = 1 →
        (∀ k : ℕ, 1 ≤ k → k ≤ 3 → p.eval (k : ℝ) = latCount (frameRep j) (convexHull ℝ S) k) →
        (∀ k : ℕ, 1 ≤ k → k ≤ 2 → p.eval (-(k : ℝ)) = intCount (frameRep j) (convexHull ℝ S) k) →
        p = ehrhartPoly (frameRep j) (convexHull ℝ S) :=
  R280.poly_six_values_proof hE2 j S hS

/-! ## Theorem 1.2 and Corollary 1.4 -/

/-- Theorem 1.2, l.93-95, proof l.372-374 (and abstract, Table 1 l.76-77): every `P ∈ O⁴` has `g_1(P) ≤ 8` and
`g_2(P) ≤ 24`. -/
theorem thm_1_2 (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (hTRI : BoundaryTriangulation) (hTILE : CrossPolytopeNoTiling) (hC1 : Comp1) (hC3 : Comp3)
    (hC4 : Comp4) (hC5 : Comp5) (P : Set (Pt 4)) (hP : InW (Zn 4) P) :
    g (Zn 4) P 1 ≤ 8 ∧ g (Zn 4) P 2 ≤ 24 :=
  S12.thm_1_2_of hE1 hE2 hE3 hTRI hC1 C2P.comp2_proof hC3 hC5
    (fun P hP hG hr => Sec5.case_III_transfer hTILE hC4 P hP hG hr) P hP

/-- Abstract l.47, proof of Corollary 1.4 l.110, Figure 1's caption l.140: Conjecture 1.1 holds for `n = 4`
(Theorem 1.2 states the two bounds only, since text version 2.40). -/
theorem conj_n4 (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (hTRI : BoundaryTriangulation) (hTILE : CrossPolytopeNoTiling) (hC1 : Comp1) (hC3 : Comp3)
    (hC4 : Comp4) (hC5 : Comp5) : WillsConj 4 :=
  S12.conj_n4_of hE1 hE2 hE3 hTRI hC1 C2P.comp2_proof hC3 hC5
    (fun P hP hG hr => Sec5.case_III_transfer hTILE hC4 P hP hG hr)

/-- Corollary 1.4, l.105-111 (and abstract, Table 1 l.79, Figure 1 l.140): Wills' conjecture holds in `ℝⁿ`
(`n ≥ 1`: l.158) if and only if `n ≤ 4`. -/
theorem cor_1_4 (hEHR : EhrhartThm) (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (hTRI : BoundaryTriangulation) (hTILE : CrossPolytopeNoTiling) (hVolW : VolW)
    (hC1 : Comp1) (hC3 : Comp3) (hC4 : Comp4) (hC5 : Comp5) (n : ℕ) (hn : 1 ≤ n) :
    WillsConj n ↔ n ≤ 4 :=
  S12.cor_1_4_of hEHR hE1 hE2 hE3 hTRI hVolW hC1 C2P.comp2_proof hC3 hC5
    (fun P hP hG hr => Sec5.case_III_transfer hTILE hC4 P hP hG hr) n hn

/-! ## Section 7: the equality cases -/

/-- l.378: `T` is the 24-cell `conv{±e_a ± e_b}` written in the basis `e_1, e_2, e_3, ½(1,1,1,1)` of the lattice
`ℤ⁴ ∪ (ℤ⁴ + ½(1,1,1,1))`: these four vectors are a basis of that lattice, and `(T, ℤ⁴) ≅ (24-cell, that lattice)`. -/
theorem T_iso :
    latD4star = lat (Matrix.of ![![1, 0, 0, 1 / 2], ![0, 1, 0, 1 / 2], ![0, 0, 1, 1 / 2], ![0, 0, 0, 1 / 2]]) ∧
      IsoPair T (Zn 4) cell24 latD4star :=
  Rows7.T_iso

/-- l.389: every point of the 24-cell has `|x_i| ≤ 1` and `Σ|x_i| ≤ 2`; its lattice points other than `0` are the
24 vertices, the 8 points `±e_i` and the 16 points `(±½, ±½, ±½, ±½)` (48 in all), and none is interior. -/
theorem cell24_points :
    (∀ x ∈ cell24, (∀ i, |x i| ≤ 1) ∧ ∑ i, |x i| ≤ 2) ∧ (cell24 ∩ latD4star).ncard = 49 ∧
      interior cell24 ∩ latD4star = {0} :=
  Rows7.cell24_points

/-- l.389: the polytope `conv{±e_a ± e_b}` is the set of points `x` with `|x_i| ≤ 1` for all `i` and
`|x_1| + ⋯ + |x_4| ≤ 2`. -/
theorem cell24_eq_box : cell24 = {x : Pt 4 | (∀ i, |x i| ≤ 1) ∧ ∑ i, |x i| ≤ 2} :=
  C24.cell24_eq_box_proof

/-- l.389: the lattice points of the 24-cell in `ℤ⁴ ∪ (ℤ⁴ + ½(1,1,1,1))` are `0`, the 24 vertices `±e_a ± e_b`,
the 8 points `±e_i` and the 16 points `(±½, ±½, ±½, ±½)` (with `cell24_points`: 49 points in all). -/
theorem cell24_lattice_points :
    cell24 ∩ latD4star = {0} ∪
      {x | ∃ a b : Fin 4, a < b ∧ ∃ s t : ℝ, (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
        x = s • Pi.single a 1 + t • Pi.single b 1} ∪
      {x | ∃ (i : Fin 4) (c : ℝ), (c = 1 ∨ c = -1) ∧ x = c • unitVec i} ∪
      {x | ∀ i, x i = 1 / 2 ∨ x i = -1 / 2} :=
  Sec7H.cell24_lattice_points

/-- l.389: each of the 48 nonzero points of `conv{±e_a ± e_b} ∩ (ℤ⁴ ∪ (ℤ⁴ + ½(1,1,1,1)))` has a coordinate `±1` or
all four coordinates `±½`, so it lies on one of the hyperplanes `{x_i = ±1}` or `{±x_1 ± x_2 ± x_3 ± x_4 = 2}`; and
the 24-cell lies on one side of each of them. (The word "facet": not formalized, no faces of polytopes in Lean's
library.) -/
theorem cell24_hyperplanes :
    (∀ x ∈ cell24 ∩ latD4star, x ≠ 0 →
      ((∃ i, x i = 1 ∨ x i = -1) ∨ ∀ i, x i = 1 / 2 ∨ x i = -1 / 2) ∧
      ((∃ i, x i = 1 ∨ x i = -1) ∨ ∃ s : Pt 4, (∀ i, s i = 1 ∨ s i = -1) ∧ s ⬝ᵥ x = 2)) ∧
    ∀ x ∈ cell24, (∀ i, |x i| ≤ 1) ∧ ∀ s : Pt 4, (∀ i, s i = 1 ∨ s i = -1) → s ⬝ᵥ x ≤ 2 :=
  Sec7H.cell24_hyperplanes

/-- l.389: `T ∈ O⁴`. -/
theorem T_mem : InW (Zn 4) T :=
  Rows7.T_mem

/-- l.389: `G(T) = 49`. -/
theorem T_G : G (Zn 4) T = 49 :=
  Rows7.T_G

/-- l.389: the dual lattice of `ℤ⁴ ∪ (ℤ⁴ + ½(1,1,1,1))` is `{y ∈ ℤ⁴ : y_1 + ⋯ + y_4 even}`. -/
theorem D4star_dual : dualLat latD4star = gammaI Finset.univ :=
  Rows7.D4star_dual

/-- l.389: the vectors `±2e_i` and `(±1,±1,±1,±1)` lie in the dual lattice of `ℤ⁴ ∪ (ℤ⁴ + ½(1,1,1,1))` and are
primitive there; they are normal to the hyperplanes `{x_i = ±1}` and `{s ⬝ x = 2}` and take the value 2 on them (the
lattice distance 2); the 24-cell lies on one side, and each hyperplane contains four affinely independent vertices.
(The word "facet", "every facet": not formalized, no faces of polytopes in Lean's library.) -/
theorem cell24_normals :
    (∀ (i : Fin 4) (c : ℝ), (c = 1 ∨ c = -1) →
      (2 * c) • unitVec i ∈ dualLat latD4star ∧
      (∀ w ∈ dualLat latD4star, ∀ k : ℤ, 2 ≤ k → (2 * c) • unitVec i ≠ (k : ℝ) • w) ∧
      (∀ x : Pt 4, ((2 * c) • unitVec i) ⬝ᵥ x = 2 ↔ x i = c) ∧
      (∀ x ∈ cell24, ((2 * c) • unitVec i) ⬝ᵥ x ≤ 2) ∧
      ∃ p : Fin 4 → Pt 4, (∀ k, p k ∈ cell24) ∧ (∀ k, ((2 * c) • unitVec i) ⬝ᵥ p k = 2) ∧ AffineIndependent ℝ p) ∧
    ∀ s : Pt 4, (∀ i, s i = 1 ∨ s i = -1) →
      s ∈ dualLat latD4star ∧ (∀ w ∈ dualLat latD4star, ∀ k : ℤ, 2 ≤ k → s ≠ (k : ℝ) • w) ∧
      (∀ x ∈ cell24, s ⬝ᵥ x ≤ 2) ∧
      ∃ p : Fin 4 → Pt 4, (∀ k, p k ∈ cell24) ∧ (∀ k, s ⬝ᵥ p k = 2) ∧ AffineIndependent ℝ p :=
  Sec7H.cell24_normals

/-- l.389: the 24-cell `conv{±e_a ± e_b}` has volume 8. -/
theorem cell24_vol (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) : volume cell24 = 8 :=
  Rows7.cell24_vol hE1 hE2

/-- l.389: `vol(T) = 16`. -/
theorem T_vol (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) : volume T = 16 :=
  Rows7.T_vol hE1 hE2

/-- l.391: `0` is the only interior lattice point of `X`, so `X ∈ O⁴`. -/
theorem X_mem : InW (Zn 4) X :=
  Rows7.X_mem

/-- l.391: `G(X) = 33`. -/
theorem X_G : G (Zn 4) X = 33 :=
  Rows7.X_G

/-- l.391: `vol(X) = (2⁴/4!) · 18 = 12`; the four vectors have determinant 18. -/
theorem X_vol : (colMat (fun i => ofInt (xVec i))).det = 18 ∧ volume X = 12 :=
  Rows7.X_vol

/-- l.391: for each of the 16 sign vectors `ε`, the hyperplane through the four vertices `ε_i xVec i` of `X` is
`{u ⬝ x = 3}` for a primitive vector `u` of the dual lattice `ℤ⁴`; `X` lies on one side, and the four vertices are
affinely independent. So each of these hyperplanes has lattice distance 3. (That they cut out 16 distinct facets,
and all the facets: not formalized, no faces of polytopes in Lean's library.) -/
theorem X_hyperplanes : ∀ ε : Fin 4 → Bool, ∃ u : Pt 4,
    u ∈ dualLat (Zn 4) ∧ (∀ w ∈ dualLat (Zn 4), ∀ k : ℤ, 2 ≤ k → u ≠ (k : ℝ) • w) ∧
    (∀ i, (if ε i then -1 else 1 : ℝ) • ofInt (xVec i) ∈ X) ∧
    (∀ i, u ⬝ᵥ ((if ε i then -1 else 1 : ℝ) • ofInt (xVec i)) = 3) ∧ (∀ y ∈ X, u ⬝ᵥ y ≤ 3) ∧
    AffineIndependent ℝ (fun i => (if ε i then -1 else 1 : ℝ) • ofInt (xVec i)) :=
  Sec7H.X_hyperplanes

/-- l.393: if every facet of `P ∈ O⁴` has lattice distance `l` (in (E3)'s facet data), then `g_3 = σ/2 = 2g_4/l`;
and Lemma 4.1 gives `g_1 = (G-1)/2 - g_3`, `g_2 = (G-1)/2 - g_4`. -/
theorem g3_of_dist (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (_hE3 : FacetFormula) (P : Set (Pt 4))
    (hP : InW (Zn 4) P)
    (l : ℤ) (hl : 1 ≤ l) :
    (∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData 1 P m relvol b → (∀ j, b j = l) →
        g (Zn 4) P 3 = (1 / 2) * ∑ j, relvol j ∧ g (Zn 4) P 3 = 2 * g (Zn 4) P 4 / l) ∧
      g (Zn 4) P 1 = ((G (Zn 4) P : ℝ) - 1) / 2 - g (Zn 4) P 3 ∧
      g (Zn 4) P 2 = ((G (Zn 4) P : ℝ) - 1) / 2 - g (Zn 4) P 4 :=
  Rows7.g3_of_dist hE1 hE2 P hP l hl

/-- l.393: `C_4` has `G = 81` and volume 16. -/
theorem cube4_G_vol : G (Zn 4) (cube 4) = 81 ∧ volume (cube 4) = 16 :=
  Rows7.cube4_G_vol

/-- l.393: `±e_i` lies in the dual lattice `ℤ⁴` of `ℤ⁴` and is primitive there; the hyperplane `{±e_i ⬝ x = 1}` is
`{x_i = ±1}`, the cube `C_4` lies on one side, and the hyperplane contains four affinely independent points of `C_4`;
so the lattice distance is 1. (The word "facet": not formalized, no faces of polytopes in Lean's library.) -/
theorem cube4_hyperplanes : ∀ (i : Fin 4) (c : ℝ), (c = 1 ∨ c = -1) →
    c • unitVec i ∈ dualLat (Zn 4) ∧ (∀ w ∈ dualLat (Zn 4), ∀ k : ℤ, 2 ≤ k → c • unitVec i ≠ (k : ℝ) • w) ∧
    (∀ x : Pt 4, (c • unitVec i) ⬝ᵥ x = 1 ↔ x i = c) ∧ (∀ x ∈ cube 4, (c • unitVec i) ⬝ᵥ x ≤ 1) ∧
    ∃ p : Fin 4 → Pt 4, (∀ k, p k ∈ cube 4) ∧ (∀ k, (c • unitVec i) ⬝ᵥ p k = 1) ∧ AffineIndependent ℝ p :=
  Sec7H.cube4_hyperplanes

/-- l.395: `L_{C_4} = 1 + 8k + 24k² + 32k³ + 16k⁴`. -/
theorem poly_C4 : ehrhartPoly (Zn 4) (cube 4) = polyC4 ∧
    ∀ k : ℕ, (latCount (Zn 4) (cube 4) k : ℝ) = polyC4.eval (k : ℝ) :=
  Rows7.poly_C4

/-- l.395: `L_T = 1 + 8k + 8k² + 16k³ + 16k⁴`. -/
theorem poly_T (hEHR : EhrhartThm) (hE2 : EhrhartReciprocity) : ehrhartPoly (Zn 4) T = polyT ∧
    ∀ k : ℕ, (latCount (Zn 4) T k : ℝ) = polyT.eval (k : ℝ) :=
  Rows7.poly_T hEHR hE2

/-- l.395: `L_X = 1 + 8k + 4k² + 8k³ + 12k⁴`. -/
theorem poly_X (hEHR : EhrhartThm) (hE2 : EhrhartReciprocity) : ehrhartPoly (Zn 4) X = polyX ∧
    ∀ k : ℕ, (latCount (Zn 4) X k : ℝ) = polyX.eval (k : ℝ) :=
  Rows7.poly_X hEHR hE2

/-- l.397: `M(T) = {0}`. -/
theorem M_T : MP T = {0} :=
  Rows7.M_T

/-- l.399: `M(X) = {0}`. -/
theorem M_X : MP X = {0} :=
  Rows7.M_X

/-- Remark 7.3, l.415 (and l.85): the cube satisfies Henze's root condition. -/
theorem henze_C4 : HenzeRoots (ehrhartPoly (Zn 4) (cube 4)) :=
  Rows7.henze_C4

/-- Remark 7.3, l.415 (and l.85): `T` does not satisfy Henze's root condition. -/
theorem henze_T_not (hE2 : EhrhartReciprocity) : ¬ HenzeRoots (ehrhartPoly (Zn 4) T) :=
  Rows7.henze_T_not hE2

/-- Remark 7.3, l.415 (and l.85): `X` does not satisfy Henze's root condition. -/
theorem henze_X_not (hE2 : EhrhartReciprocity) : ¬ HenzeRoots (ehrhartPoly (Zn 4) X) :=
  Rows7.henze_X_not hE2

/-- Remark 7.3, l.415: if all four roots of `L_P`, for `P ∈ O⁴`, have real part `-1/2`, they sum to `-2`, so
`g_3(P) = 2 g_4(P)` by Vieta's formulas. -/
theorem henze_vieta (hE1 : EhrhartLeading) (P : Set (Pt 4)) (hP : InW (Zn 4) P)
    (hH : HenzeRoots (ehrhartPoly (Zn 4) P)) : g (Zn 4) P 3 = 2 * g (Zn 4) P 4 :=
  Fig3.henze_vieta_proof hE1 P hP hH

/-- Remark 7.3, l.415: `L_T` has `g_3 = 16 ≠ 2 · 16` and `L_X` has `g_3 = 8 ≠ 2 · 12`. -/
theorem henze_coeffs (hE2 : EhrhartReciprocity) :
    g (Zn 4) T 3 = 16 ∧ g (Zn 4) T 4 = 16 ∧ g (Zn 4) X 3 = 8 ∧ g (Zn 4) X 4 = 12 ∧
      (16 : ℝ) ≠ 2 * 16 ∧ (8 : ℝ) ≠ 2 * 12 :=
  Fig3.henze_coeffs_proof hE2

/-- Proof of Theorem 7.1, l.403: unimodular maps preserve `G`. -/
theorem G_unimod_inv (P P' : Set (Pt 4)) (h : UnimodEquiv P P') : G (Zn 4) P' = G (Zn 4) P :=
  Rows7.G_unimod_inv P P' h

/-- Theorem 7.1, l.383-385, proof l.403 (and abstract, Table 1 l.76, l.85): `P ∈ O⁴` has `g_1(P) = 8` if and only if
it is unimodularly equivalent to `C_4`, `T` or `X`; and these three are pairwise inequivalent. -/
theorem thm_7_1 (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (hTRI : BoundaryTriangulation) (hTILE : CrossPolytopeNoTiling) (hC1 : Comp1) (hC3 : Comp3)
    (hC4 : Comp4) (hC5 : Comp5) :
    (∀ P : Set (Pt 4), InW (Zn 4) P →
      (g (Zn 4) P 1 = 8 ↔ UnimodEquiv (cube 4) P ∨ UnimodEquiv T P ∨ UnimodEquiv X P)) ∧
      ¬ UnimodEquiv (cube 4) T ∧ ¬ UnimodEquiv (cube 4) X ∧ ¬ UnimodEquiv T X :=
  S71.thm_7_1_of hE2 hE3 hTRI hC1 C2P.comp2_proof hC3 hC5 (fun P hP hG hr => Sec5.case_III_transfer hTILE hC4 P hP hG hr)

/-- Corollary 7.2, l.406-408, proof l.410-412 (and Table 1 l.77): `P ∈ O⁴` has `g_2(P) = 24` if and only if it is
unimodularly equivalent to `C_4`. The proof is the printed one, from the rows of Theorems 1.2 and 7.1, Proposition 4.2
and Lemma 4.1: `g_1 ≤ 8`, so `24 = g_2 ≤ g_4 + 8 ≤ 24` and `g_4 = 16`; then `G = 81` and `g_1 + g_3 = 40`; `g_3 ≤ 32`
forces `g_1 = 8`; of `C_4`, `T`, `X` only `C_4` has 81 lattice points. -/
theorem cor_7_2 (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (hTRI : BoundaryTriangulation) (hTILE : CrossPolytopeNoTiling) (hC1 : Comp1) (hC3 : Comp3)
    (hC4 : Comp4) (hC5 : Comp5) :
    ∀ P : Set (Pt 4), InW (Zn 4) P → (g (Zn 4) P 2 = 24 ↔ UnimodEquiv (cube 4) P) := by
  intro P hP
  constructor
  · intro h2
    have h12 := thm_1_2 hE1 hE2 hE3 hTRI hTILE hC1 hC3 hC4 hC5 P hP
    have hB : (1 : Matrix (Fin 4) (Fin 4) ℝ).det ≠ 0 := by simp
    have hP1 : InW (lat 1) P := by rw [lat_one]; exact hP
    have h1 : g (lat 1) P 1 ≤ 8 := by rw [lat_one]; exact h12.1
    have hg2 := prop_4_2_g2 hE1 hE2 hE3 1 hB P hP1 h1
    have hid := lem_4_1 hE2 1 hB P hP1
    have hg3 := prop_4_2_g3 hE1 hE3 1 hB P hP1
    rw [lat_one] at hg2 hid hg3
    have hg4 : g (Zn 4) P 4 = 16 := by linarith [hg2.1, hg2.2]
    have hG : (G (Zn 4) P : ℝ) = 81 := by linarith [hid.2]
    have hg1 : g (Zn 4) P 1 = 8 := by linarith [hid.1, hg3.1, h12.1]
    rcases ((thm_7_1 hE2 hE3 hTRI hTILE hC1 hC3 hC4 hC5).1 P hP).1 hg1 with hc | hT | hX
    · exact hc
    · rw [G_unimod_inv T P hT, T_G] at hG
      norm_num at hG
    · rw [G_unimod_inv X P hX, X_G] at hG
      norm_num at hG
  · intro hc
    rw [iso_g 4 (cube 4) (Zn 4) P (Zn 4) (S71.iso_of_unimod hc) 2, cube_g 4 2]
    norm_num [Nat.choose]

/-! ## Figure 3 (Section 6, l.330; its caption is line 32 of fig_maxg1.tex) -/

/-- l.263 (after the proof of Lemma 4.3) and Figure 3, caption: the bound `g_1 ≤ (3G+7)/12` follows from the inequality `Σ_F NVol(F) ≥ 3G - 13` in the
proof of Lemma 4.3, since `g_1 = (G-1)/2 - σ/2` (Lemma 4.1 and (E3)) and `σ = (1/6) Σ_F NVol(F)`. Over (E3)'s facet
data, `σ = Σ relvol_j` and `NVol(F_j) = 6 relvol_j`; the bound is proved for every `P ∈ O⁴_Λ` (the figure draws it
for `G ≤ 29`). -/
theorem fig3_g1_bound (hE2 : EhrhartReciprocity) (hE3 : FacetFormula) (hTRI : BoundaryTriangulation)
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.det ≠ 0) (P : Set (Pt 4)) (hP : InW (lat B) P) :
    g (lat B) P 1 ≤ (3 * (G (lat B) P : ℝ) + 7) / 12 ∧
      (∃ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b) ∧
      ∀ (m : ℕ) (relvol : Fin m → ℝ) (b : Fin m → ℤ), IsFacetData B P m relvol b →
        ∑ j, 6 * relvol j ≥ 3 * (G (lat B) P : ℝ) - 13 ∧
          g (lat B) P 1 = ((G (lat B) P : ℝ) - 1) / 2 - (∑ j, relvol j) / 2 :=
  ⟨(Fig3.fig3_g1_bound_proof hE2 hTRI B hB P hP).1, hE3 4 (by norm_num) B hB P hP,
    (Fig3.fig3_g1_bound_proof hE2 hTRI B hB P hP).2⟩

/-- RETIRED (Figure 3's caption up to text version 2.30; no longer printed): for `G ≥ 31` the bound `(3G+7)/12`
exceeds `8`. -/
theorem fig3_bound_gt (Gc : ℝ) (hG : 31 ≤ Gc) : 8 < (3 * Gc + 7) / 12 :=
  Fig3.fig3_bound_gt_proof Gc hG

/-- RETIRED (Figure 3's caption up to text version 2.30; no longer printed): by Theorems 1.2 and 7.1, every
polytope in `O⁴` that is not unimodularly equivalent to `C_4`,
`T` or `X` has `g_1 < 8`. -/
theorem fig3_lt_eight (hE1 : EhrhartLeading) (hE2 : EhrhartReciprocity) (hE3 : FacetFormula)
    (hTRI : BoundaryTriangulation) (hTILE : CrossPolytopeNoTiling) (hC1 : Comp1) (hC3 : Comp3)
    (hC4 : Comp4) (hC5 : Comp5) (P : Set (Pt 4)) (hP : InW (Zn 4) P)
    (hne : ¬ (UnimodEquiv (cube 4) P ∨ UnimodEquiv T P ∨ UnimodEquiv X P)) : g (Zn 4) P 1 < 8 :=
  lt_of_le_of_ne (thm_1_2 hE1 hE2 hE3 hTRI hTILE hC1 hC3 hC4 hC5 P hP).1
    (fun h => hne (((thm_7_1 hE2 hE3 hTRI hTILE hC1 hC3 hC4 hC5).1 P hP).1 h))

/-- Figure 3, caption: `T` and `X` belong to Case III (`r(P) ≤ 3`, as in the case split), since
`M(T) = M(X) = {0}` (rows `M_T`, `M_X`). -/
theorem fig3_T_X_case_III : rP T ≤ 3 ∧ rP X ≤ 3 :=
  ⟨S71.T_caseIII.2, S71.X_caseIII.2⟩

/-- Figure 3, caption (fig_maxg1.tex l.32): `C_4` belongs to Case I: `M(C_4)` contains the basis `e_1, …, e_4` of
`ℤ⁴` (the rows of the identity matrix). -/
theorem cube4_case_I : CaseI (cube 4) :=
  R280.cube4_case_I_proof

end Wills
