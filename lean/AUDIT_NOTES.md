# AUDIT_NOTES — the Lean formalization of "Wills' (1981) conjecture is fully resolved"

Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

These notes are for a reader of the Lean tree. AUDIT.md (made by `scripts/audit.py`) gives the status of every row and
every printed claim; these notes explain the modelling choices and every place where the Lean route differs from the
printed proof. Line numbers "l.N" refer to the paper's source, version 3.20 (TeX source md5 47e41917); Figure 3 is the
file fig_maxg1.tex (md5 a9f75b6d), input at the end of l.330, its caption on its line 32. The abstract's
last sentence (l.47) and the footnote "Lean 4 formalization:" (l.38) are remarks about this Lean folder, not mathematical
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
- `InW Λ P` (the paper's `O^n_Λ`): `P` is the convex hull of finitely many points of `Λ`, `-P = P`, and
  `int P ∩ Λ = {0}`.
- The paper prints this class with a script O since text version 2.90 (a script W before; the polytope `W` of
  Theorem 1.3 keeps its letter). Statements.lean, CLAIM_MAP.tsv and these notes follow the paper; the Lean names
  (`InW`) and the comments inside Wills/Proofs, Wills/Defs, Wills/Facts and Wills/Checks keep the letter W.
- Wills' conjecture in dimension `n` is `WillsConj n`: `g_i(P) ≤ 2^i binom(n,i)` for every `P ∈ Oⁿ` and `0 ≤ i ≤ n`.
- A sublattice of ℤ⁴ is `subLat B = B ℤ⁴` for an integer matrix `B`; its index is `|det B|`, so where the paper says
  "of index `d`", the rows say `|det B| = d`.
- The rows `lem_2_1_sub`, `conj_in1`, `conj_le_two` and `cor_1_4` assume `n ≥ 1` explicitly: the paper's standing
  assumption, l.158 (at `n = 0` the remark after Lemma 2.1 would fail for the empty set).

## 2. Facts the paper uses from areas Lean's library does not cover (Wills/Facts/Basic.lean)
Each fact is a `Prop`, TRUE as stated, and every row that uses it takes it as an explicit hypothesis (nothing is
assumed globally).
A row proved from such hypotheses has the status PROVED GIVEN <facts>.
- EHR (`EhrhartThm`) Ehrhart's theorem; E1 (`EhrhartLeading`) `g_n = vol/det Λ`; E2 (`EhrhartReciprocity`)
  reciprocity: not formalized, no Ehrhart theory in Lean's library.
- E3 (`FacetFormula`): the facet formula `g_{n-1} = ½ Σ relvol(F)`, `vol/det Λ = (1/n) Σ b_F relvol(F)`. Lean's library
  has no faces of polytopes, so facets enter the tree ONLY as these numbers (`IsFacetData`): every sentence about the
  lattice surface area `σ` is stated for the numbers that E3 provides.
- TRI (`BoundaryTriangulation`): the facts of the proof of Lemma 4.3 (a boundary triangulation, its f-vector, Walkup's
  lower bound theorem, the Dehn-Sommerville relations). The deduction from these facts is proved.
  THE SOURCE OF THE TRIANGULATION (l.262: "take a triangulation of P whose vertices are exactly the points of P ∩ Λ;
  one exists, for example by strong pulling ([HPPS21, Lemma 2.1(2)], applied in the coordinates of a basis of Λ)"). [HPPS21] = C. Haase, A. Paffenholz, L. C. Piechnik and
  F. Santos, Existence of unimodular triangulations — positive results, Mem. Amer. Math. Soc. 270 (2021), no. 1321;
  arXiv:1405.1687. Its words, as numbered in arXiv:1405.1687v3 (11 Dec 2017; `Z^d`, `pull_m` and `F′` are the PDF's
  superscript, subscript and prime):
  > "A full triangulation is a lattice triangulation which uses all the lattice points in P." (Section 1.1)
  > "If S is a subdivision of P and m ∈ P ∩ Z^d is a lattice point in P, the strong pulling refinement pull_m S is
  > obtained by replacing every face F ∈ S containing m by the pyramids conv(m, F′), for each face F′ of F which does
  > not contain m." (Section 2.1.1)
  > "Lemma 2.1. Let P be a lattice polytope with a subdivision S. (1) Strong pulling preserves regularity. (2) Strongly
  > pulling all lattice points of P in any order results in a full triangulation. (3) If only vertices of P are
  > pulled, then ..." (Section 2.1.1, page 14)

  WHAT THE LEMMA GIVES: part (2), with S the trivial subdivision of P: a triangulation of P whose vertices are exactly
  the lattice points of P (for the lattice Λ: in the coordinates of a basis of Λ, where Λ becomes Z^4).
  WHAT THE PAPER ADDS ITSELF (l.262): the faces of this triangulation that lie in the boundary of P form Δ; Δ is a
  triangulated 3-sphere with G - 1 vertices; each tetrahedron lies in a facet and has normalized volume at least 1.
  All of this stays inside the hypothesis TRI, whose type is unchanged since text version 2.30.
- TILE (`CrossPolytopeNoTiling`): a 4-dimensional cross-polytope does not tile ℝ⁴ by its translates by ℤ⁴ (the tile
  theorem in the form l.323 uses).
Minkowski's first theorem is PROVED from Lean's library (it is not a fact here).

## 3. Computer checks (Wills/Checks/Computations.lean)
The results of Computations 1-5, their class counts, and vol(W) = 386/15 are `Prop`s, each stated as printed, and
enter the rows that use them as explicit hypotheses: "checked by computer, NOT proved in Lean:
./reproduce.sh computation-N (repository folder wills-1981-conjecture/)" (`theorem-1.3` for vol(W)). The recorded
outputs are in wills-1981-conjecture/expected/<claim>/ of the computation repository, commit dc85abb.
- Figure 3's dots are the check `Comp1Max`: for each odd `G` from 81 down to 31, the largest `g_1(conv S)` over the
  sets `S` of Computation 1 with `#S = G`, as an exact rational (`comp1MaxTable`, from both programs' maxima in
  expected/computation-1/case1_compare.txt; `./reproduce.sh computation-1`). The figure draws these 26 values to four
  decimals.
- The class counts (`Comp1Count`, ..., `Comp5Count`) and `Comp1Max` are claims checked by computer; no row takes them as
  a hypothesis. The rows' hypotheses among the checks are `VolW`, `Comp1`, `Comp3`, `Comp4` and `Comp5`. The result of
  Computation 2 (`Comp2`) is proved in Lean (section 4); only its count of sublattices (`Comp2Count`) is a check.
- Computation 5's sandwich search (l.367, l.369): each step that the printed text justifies is a proved row:
  `sandwich_start` (every member lies between the two start sets; the lower one is a member), `sandwich_split`,
  `sandwich_prune`, `M_antitone` (the rule `r(S⁺) = 4`), `sandwich_include_member` (an include step that is kept gives
  a member; with `sandwich_start`, by induction over the steps, every lower set of the search is a member, so the sets
  at the pairs with `S⁻ = S⁺` are members), `sandwich_symm` (a pair carried onto a pair met earlier is discarded).
  Where the search stops and how the sets found are reduced to one per class describe the program. How Computation 5 computes each polynomial (l.330: from point counts) is a description of the program; its
  one mathematical step, that the counts give the values at `k = -2, …, 3` and so fix the polynomial, is the row
  `poly_six_values`. The result of Computation 5 (`Comp5`) stays a hypothesis.

## 4. Proved by the Lean kernel from certificates (no computer check needed)
- Computation 2's result (row `comp2_result`, Wills/Proofs/Comp2Proof.lean): a sublattice `B ℤ⁴` of index `d ≥ 3` has
  at most 27 points in `{-1,0,1}⁴`. If an odd prime `p` divides `d`, then `B` is singular mod `p`, so a nonzero vector
  `v` over `ZMod p` has `Σ v_i y_i ≡ 0` on the lattice; fixing a coordinate `j` with `v_j ≠ 0`, the other three
  coordinates of a point of `{-1,0,1}⁴` determine `x_j` (three distinct residues mod `p ≥ 3`): at most 27. Otherwise
  `d = 2^a`, `a ≥ 2`: twice, `B` is singular mod 2, so `B = M_I M_J B''` with the index-2 matrices `M_I` of `Γ_I`;
  the lattice lies in the index-4 lattice `M_I Γ_J`, and a kernel check over the 225 pairs `(I, J)` counts at most 27
  points of `{-1,0,1}⁴` in each. For `d = 2` the lattice is some `Γ_I` (at most 45 points, 45 attained: rows
  `index2_eq_gammaI`, `gammaI_counts`, `comp2_d2_max`). The printed computation lists the 40,406 sublattices; that
  count (`Comp2Count`) stays a computer check.
- Theorem 1.3's counts `G(W) = 117`, `#(2W ∩ ℤ⁵) = 1815`, `#(int(2W) ∩ ℤ⁵) = 243`, the 50 vertices of Table 2:
  certificates (convex combinations, facet inequalities, separating functionals) checked by `decide +kernel`, with
  soundness lemmas that tie them to the definitions (Wills/Proofs/Count*.lean, WVertices.lean).
- Section 7's counts for `T` and `X` (`L(1)`, `L(2)`, `#(int(2P) ∩ ℤ⁴)` = 49, 433, 145 and 33, 289, 129), membership
  in `O⁴`: a generic 4-dimensional engine (Wills/Proofs/Count4.lean: facet filter on a box, convex-combination
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
- Corollary 1.4 for `n = 3` (l.110 cites Wills' theorem [Wil81]; l.67: [Wil81, Theorem (i), (ii)]): Lean proves it from E1, E2, E3 (row
  `wills_dim3`, Wills/Proofs/Dim3.lean): `g_0 = 1`; `g_3 = vol(P) ≤ 8` (Minkowski); `2 g_2 = σ ≤ 3 vol(P)` (E3, every
  `b_F ≥ 1`); and E2 at `k = 1` gives `1 - g_1 + g_2 - g_3 = L(-1) = -1`, so `g_1 = 2 + g_2 - g_3 ≤ 2 + g_3/2 ≤ 6`.
- Corollary 1.4 for `n = 4` uses Proposition 4.2's `g_3 ≤ 32` for the coefficient `g_3` (the printed proof, l.110,
  cites Wills' Theorem (i) for this bound, which is the row `conj_in1`).
- Theorem 1.3's polynomial: from the four numbers `G, L(2), #int(2W), vol(W)` and E1, E2 (five linear equations); its
  values `L_W(3..6)` then follow by evaluation (EHR).
- Remark 4.4's first sentence is not used (NOT COUNTED). Henze's theorem for `n ≥ 7` is not used; the root
  condition of l.85 and Remark 7.3 (l.415) is proved for `C_4`, `T`, `X` (rows `henze_C4`, `henze_T_not`,
  `henze_X_not`), by the printed route of l.415: Vieta's formulas give `g_3 = 2 g_4` when all four roots have real part `-1/2` (row `henze_vieta`), and the
  coefficients of `L_T` and `L_X` break it (row `henze_coeffs`).

## 6. Rows stronger than printed (a hypothesis of the printed statement is not needed)
- `g0_eq_one` (`hB`, `hP`: only `int P ≠ ∅` is used); `thm_1_3_prod` (`hm`: also true for `m = 0`);
  `thm_1_2_case_split`, `case_II_d_ge_2` (`hP`); `case_II_d_le_16` (`hdet`); `lem_6_1_i` (`hfin`); `lem_6_1_ii` (the
  symmetry and saturation of `Q`); `sandwich_split` (`hv`); `sandwich_include_member` (the test that the new `S⁻`
  lies in `S⁺`: only `v ∈ Λ ∩ C_4` is used); `frame_lat_GL` (`hV`); `minkowski_first` (`hcpt`:
  compactness is not used; convexity, symmetry and the interior condition suffice).
- `fig3_g1_bound` (l.263, Figure 3): the bound `g_1 ≤ (3G+7)/12` holds for every `P ∈ O⁴_Λ`, as l.263 states; the
  figure draws it for `G ≤ 29`, where it is below 8.
- `poly_six_values` (l.330): the value `1` at `k = 0` is printed "by (E1)"; in the tree it holds by counting
  (`L(0) = #(0P ∩ Λ) = 1`, as in `g0_eq_one`), so the row does not take E1; it takes E2 for the values at `-1, -2`.
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
The 24-cell as a set (l.389: `conv{±e_a ± e_b}` "is the set of points" `x` with `|x_i| ≤ 1` and `Σ|x_i| ≤ 2`) is the
row `cell24_eq_box`: a set equality, PROVED; it needs no faces.

## 8. Retired rows (no longer printed)
Three rows state sentences that were printed in earlier versions of the paper and are not printed in this version.
They are kept, proved as before, and not counted (CLAIM_MAP.tsv lists them as SUPPORT only):
- `fig3_bound_gt` (last printed: text version 2.30): Figure 3's caption: for `G ≥ 31` the bound `(3G+7)/12` exceeds 8.
- `fig3_lt_eight` (last printed: text version 2.30): Figure 3's caption: by Theorems 1.2 and 7.1, every polytope in
  `O⁴` that is not unimodularly equivalent to `C_4`, `T` or `X` has `g_1 < 8`.
- `comp5_maximal` (last printed: text version 2.80): Computation 5's walk: every `S` with `r(S) ≤ 3` lies in a maximal
  member `Q` of the family with `r(Q) ≤ r(S)`. Computation 5 is now described by the sandwich search alone.
The row `w_int2_all` (`int(2W)` contains every point of `{-1,0,1}⁵`) states a sentence of l.220 last printed in text
version 2.30; it stays as SUPPORT of the claim of l.220 (`A(W) = 1029`).

## 9. Re-checking the proofs outside the elaborator (optional)
Optional, after a build: `scripts/kernel_replay.sh` re-checks every declaration outside the elaborator: first
`leanchecker` replays each compiled module; then `leanexport` exports the declarations, and the export is checked by
independent checkers: `leanchecker`, its paranoid mode, `lean4lean`, `nanoda`, `con-leche` and `con-ron` (the tools
are listed at the top of the script). The script runs every tool through `scripts/lean_run.sh`, which needs two
settings; on a machine with no shared compile lock and no job gate:
`LEAN_RUN_LOCK=none LEAN_RUN_GATE=none scripts/kernel_replay.sh`.
