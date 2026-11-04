# AUDIT_NOTES — the Lean formalization of "Wills' (1981) conjecture is fully resolved"

Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

These notes are for a reader of the Lean tree. AUDIT.md (made by `scripts/audit.py`) gives the status of every row and
every printed claim; these notes explain the modelling choices and every place where the Lean route differs from the
printed proof. Line numbers "l.N" refer to the paper's source, version 1.90 (TeX source md5 0c30e1ff). The abstract's
last sentence (l.47) and the footnote "Lean 4 proof:" (l.38) are remarks about this Lean folder, not mathematical
claims: CLAIM_MAP.tsv lists them as NOT COUNTED.

The Lean sources declare no axioms (`scripts/check.sh` fails on any). Two kinds of input enter only as explicit
hypotheses of the rows that use them, so nothing is assumed globally: the facts of section 2 (NOT formalized) and the
computer checks of section 3 (checked by computer, NOT proved in Lean). A row proved from such hypotheses has the status
PROVED GIVEN followed by their names.

## 1. Modelling (the trust surface: Wills/Defs/)
- Points of ℝⁿ are `Fin n → ℝ`; `volume` is Lebesgue measure. ℤⁿ is `Zn n`; a lattice is a set of points, `lat B` is
  `B ℤⁿ` for a real matrix `B` with `det B ≠ 0` (`det Λ = |det B|`).
- `latCount Λ P k = #(kP ∩ Λ)`, `intCount Λ P k = #(int(kP) ∩ Λ)`, `G Λ P = #(P ∩ Λ)` (`Set.ncard`).
- `g Λ P i` is DEFINED as coefficient `i` of `ehrhartPoly Λ P`, the polynomial of degree at most `n` through the
  points `(k, L(k))`, `k = 0, …, n` (Lagrange interpolation); by Ehrhart's theorem (fact EHR below, not formalized)
  this is the Ehrhart polynomial `L_P` of the paper. With this definition `g_i` exists for every `P`. The hypothesis
  EHR appears only in the rows that use "`L(k) = L_P(k)` for every `k ≥ 0`": `lem_2_2`, `thm_1_3_poly`, `w_L3456`,
  `thm_1_3_prod`, `cor_1_4`, `poly_T`, `poly_X`.
- `InW Λ P` (the paper's `W^n_Λ`): `P` is the convex hull of finitely many points of `Λ`, `-P = P`, and
  `int P ∩ Λ = {0}`.
- Wills' conjecture in dimension `n` is `WillsConj n`: `g_i(P) ≤ 2^i binom(n,i)` for every `P ∈ Wⁿ` and `0 ≤ i ≤ n`.
- A sublattice of ℤ⁴ is `subLat B = B ℤ⁴` for an integer matrix `B`; its index is `|det B|`, so where the paper says
  "of index `d`", the rows say `|det B| = d`.
- The rows `lem_2_1_sub`, `conj_in1`, `conj_le_two` and `cor_1_4` assume `n ≥ 1` explicitly: the paper's standing
  assumption, l.158 (at `n = 0` the remark after Lemma 2.1 would fail for the empty set).

## 2. Facts the paper uses from areas Lean's library does not cover (Wills/Facts/Basic.lean)
Each fact is a `Prop`, TRUE as stated, and every row that uses it takes it as an explicit hypothesis (nothing is
assumed globally).
A row proved from such hypotheses has the status PROVED GIVEN <facts>.
- EHR (`EhrhartThm`) Ehrhart's theorem; E1 (`EhrhartLeading`) `g_n = vol/det Λ`; E2 (`EhrhartReciprocity`)
  reciprocity; WIL3 (`WillsDim3`) Wills' theorem for `n = 3`: not formalized, no Ehrhart theory in Lean's library.
- E3 (`FacetFormula`): the facet formula `g_{n-1} = ½ Σ relvol(F)`, `vol/det Λ = (1/n) Σ b_F relvol(F)`. Lean's library
  has no faces of polytopes, so facets enter the tree ONLY as these numbers (`IsFacetData`): every sentence about the
  lattice surface area `σ` is stated for the numbers that E3 provides.
- TRI (`BoundaryTriangulation`): the facts of the proof of Lemma 4.3 (a boundary triangulation, its f-vector, Walkup's
  lower bound theorem, the Dehn-Sommerville relations). The deduction from these facts is proved.
- TILE (`CrossPolytopeNoTiling`): a 4-dimensional cross-polytope does not tile ℝ⁴ by its translates by ℤ⁴ (the tile
  theorem in the form l.323 uses).
Minkowski's first theorem is PROVED from Lean's library (it is not a fact here).

## 3. Computer checks (Wills/Checks/Computations.lean)
The results of Computations 1-5, their class counts, and vol(W) = 386/15 are `Prop`s, each stated as printed, and
enter the rows that use them as explicit hypotheses: "checked by computer, NOT proved in Lean:
./reproduce.sh computation-N (repository folder wills-1981-conjecture/)" (`theorem-1.3` for vol(W)). The recorded
outputs are in wills-1981-conjecture/expected/<claim>/ of the computation repository, commit dc85abb.

## 4. Proved by the Lean kernel from certificates (no computer check needed)
- Theorem 1.3's counts `G(W) = 117`, `#(2W ∩ ℤ⁵) = 1815`, `#(int(2W) ∩ ℤ⁵) = 243`, the 50 vertices of Table 2:
  certificates (convex combinations, facet inequalities, separating functionals) checked by `decide +kernel`, with
  soundness lemmas that tie them to the definitions (Wills/Proofs/Count*.lean, WVertices.lean).
- Section 7's counts for `T` and `X` (`L(1)`, `L(2)`, `#(int(2P) ∩ ℤ⁴)` = 49, 433, 145 and 33, 289, 129), membership
  in `W⁴`: a generic 4-dimensional engine (Wills/Proofs/Count4.lean: facet filter on a box, convex-combination
  certificates, and for each interior point a small cube in `kP` given by 16 corner certificates), data in
  Wills/Certs/S7Data.lean, instances in Wills/Proofs/Sec7Counts.lean.

## 5. Route differences (where the Lean proof differs from the printed one)
- Section 7 polynomials (l.395): from the counts `L(0), L(1), L(2)` and, by reciprocity (E2), `L(-1) = 1`,
  `L(-2) = #(int(2P) ∩ ℤ⁴)`; a polynomial of degree at most 4 is fixed by its values at -2, …, 2. The printed route uses
  facet distances, which Lean's library cannot state.
- `vol(T) = 16` and `vol(24-cell) = 8` (l.389): from E1 (`g_4 = vol`) and the polynomial of `T`; the 24-cell is the
  image of `T` under a linear map of determinant 1/2. So these two rows are PROVED GIVEN E1, E2.
- `vol(X) = 12` (l.391): from the volume of a cross-polytope, `(2⁴/4!) |det|` (proved), with `det = 18`.
- `g_{n-1} ≤ 2^{n-1} binom(n,n-1)` (l.67): from E3's numbers (`σ ≤ n vol/det Λ` since every `b_F ≥ 1`) and
  Minkowski's theorem.
- Corollary 1.4 for `n = 4` uses Proposition 4.2's `g_3 ≤ 32` for the coefficient `g_3` (the printed proof, l.110,
  cites Wills' Theorem (i) for this bound, which is the row `conj_in1`).
- Theorem 1.3's polynomial: from the four numbers `G, L(2), #int(2W), vol(W)` and E1, E2 (five linear equations); its
  values `L_W(3..6)` then follow by evaluation (EHR).
- Remark 4.4's first sentence is not used (NOT COUNTED). Henze's theorem for `n ≥ 7` (l.90) is not used; the root
  condition of l.88 is proved for `C_4`, `T`, `X` (rows `henze_C4`, `henze_T_not`, `henze_X_not`).

## 6. Rows stronger than printed (a hypothesis of the printed statement is not needed)
- `g0_eq_one` (`hB`, `hP`: only `int P ≠ ∅` is used); `thm_1_3_prod` (`hm`: also true for `m = 0`);
  `thm_1_2_case_split`, `case_II_d_ge_2` (`hP`); `case_II_d_le_16` (`hdet`); `lem_6_1_i` (`hfin`); `lem_6_1_ii` (the
  symmetry and saturation of `Q`); `sandwich_split` (`hv`); `frame_lat_GL` (`hV`); `minkowski_first` (`hcpt`:
  compactness is not used; convexity, symmetry and the interior condition suffice).
- The lattice surface area `σ` enters only through E3's data. So every row that speaks about E3's facet numbers
  (`prop_4_2_iff`, `key_equiv`, `star_iff`, `lem_4_3`, `g3_of_dist`) takes E3 as a hypothesis, even where the proof
  does not use it (`g3_of_dist`, l.393: its first conjunct is E3's equation `g_3 = ½ σ`).

## 7. Facets
Lean's library has no faces of polytopes. A facet of an `n`-dimensional polytope `P` is written out by its definition:
a hyperplane `H` with `P` on one side and `n` affinely independent points of `P` on `H` (for `W` also a point of `W`
off `H`). Stated this way, the facet sentences are PROVED (no hypothesis):
- `W_facets` (Table 2 caption): 92 such hyperplanes of `W`, each through 5 affinely independent vertices, no two with
  the same face.
- `cell24_hyperplanes` (l.389): each nonzero lattice point of the 24-cell has a coordinate `±1` or all coordinates
  `±½`, so it lies on one of the hyperplanes `{x_i = ±1}`, `{±x_1 ± x_2 ± x_3 ± x_4 = 2}`; the 24-cell lies on one
  side of each.
- `cell24_normals` (l.389), `X_hyperplanes` (l.391), `cube4_hyperplanes` (l.393): for each printed facet, a primitive
  normal vector of the dual lattice with the printed value (2, 3, 1: the lattice distance), the polytope on one side,
  and 4 affinely independent points of the polytope on the hyperplane.
- `cell24_lattice_points` (l.389) lists the 49 lattice points of the 24-cell by name.
Four printed statements say that these are ALL the facets; they are separate claims, NOT FORMALIZED (no faces of
polytopes in Lean's library): TW2c (`W` has exactly 92 facets), T7dc (every facet of `T` is one of the 24), X7bc (the
16 hyperplanes of `X` cut out 16 distinct facets, and these are all), E7b2c (the 8 hyperplanes `{x_i = ±1}` are all the
facets of `C_4`).
