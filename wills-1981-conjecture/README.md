# Wills' (1981) conjecture is fully resolved

Supporting materials for the paper "Wills' (1981) conjecture is fully resolved" by Dave Goel.

Copyright (C) Dave Goel 2026--now. All rights reserved.

## Directions to Reproduce

Install Python 3.12 with NumPy 1.26.4 and SciPy 1.11.4, Normaliz 3.10.2 and LattE integrale 1.7.6. One way, on Ubuntu 24.04:

```bash
sudo apt install python3-venv normaliz-bin latte-int
python3 -m venv venv && venv/bin/pip install numpy==1.26.4 scipy==1.11.4
export PATH="$PWD/venv/bin:$PATH"
```

Then, from this folder, run one command per claim (the table below names them):

```bash
./reproduce.sh <claim>
```

A run writes its outputs to `out/<claim>/` and ends with one line for each number the paper states, `OK` or `FAIL`. For example, `./reproduce.sh theorem-1.3` takes about a minute and ends with:

```
OK   W, first program: L_W coefficients 1, 101/10, 127/12, 139/6, 557/12, 386/15
OK   W, first program: L_W(0..6) = [1, 117, 1815, 10765, 39927, 112639, 265705]
OK   W, first program: 92 facets
OK   W, first program: interior points of W, 2W = (1, 243)
OK   W, first program: 50 vertices
OK   W, Normaliz: L_W coefficients 1, 101/10, 127/12, 139/6, 557/12, 386/15
OK   W, Normaliz: G = 117, 92 facets
OK   W, LattE integrale 1.7.6: the same polynomial
OK   W, LattE: the recorded run of November 3 (latte_w_recorded.log) gives the same polynomial
OK   W, exact counter of the search: the greedy reduction of W_5 ends at 25 pairs with L_W as above
OK   W, exact counter of the search: its 25 pairs equal data/w_pairs.txt
OK   W: the four numbers G = 117, #2W = 1815, #int 2W = 243, vol = 386/15 give g_1 = 101/10 > 10
theorem-1.3: 12 of 12 checks OK
```

`./reproduce.sh test` runs the test of every program. The outputs of our own runs are in `expected/<claim>/`, and `python3 programs/check_claims.py <claim> expected/<claim>` checks them without a rerun. Every program runs on one core with exact integer and rational arithmetic; the times are those of our runs on one core.

## What the proof takes as given

The proof of Theorem 1.3 rests on the lattice-point counts of W, and the proofs of Theorems 1.2 and 7.1 rest on Computations 1-5; the programs here carry out these computations. They take no cited result as given.

| Calculation | Command | Program | Second program | Time |
|---|---|---|---|---|
| Theorem 1.3: W lies in W^5, and its Ehrhart polynomial | `theorem-1.3` | `w_ehrhart_check.py`: facets from all sets of 5 vertices, direct counts of kW | Normaliz (`data/normaliz/w.in`); LattE (`data/latte/w.vrep`); `w5_reduction.py` with `ehrhart_exact.py` | 1 min |
| Computation 1 (Case I) | `computation-1` | `case1_walk.py` | `walk_second.py`; `case1_compare.py` compares every level | 5 h + 12 h |
| Computation 2 (index bound) | `computation-2` | `index_bound_first.py` | `index_bound_second.py` | 15 s |
| Computation 3 (Case II) | `computation-3` | `case2_walk.py` | `walk_second.py` | 15 s |
| Computation 4 (frame lattices) | `computation-4` | `frame_lattices_first.py` (index D <= 24) | `frame_lattices_second.py`, `frame_lattices_orbits.py` | 4 min |
| Computation 5 (Case III) | `computation-5` | `case3_run_all.py` with `case3_frame_search.py` | `case3_sandwich.py`; `case3_compare.py` compares every lattice | 1.5 h + 3.6 h |
| Section 7: T, X, and the sets with M(S) = {0} | `section-7` | `case3_frame_search.py`; `w_ehrhart_check.py` | `case3_sandwich.py`; Normaliz | 3 min |
| Expanded version: Computation 6 (r <= rho, rho = 0, 1, 2) | `computation-6` | `case3_frame_search.py` | `case3_sandwich.py` | 36 min |
| Expanded version: Computation 7 (the boxes) | `computation-7` | `boxes_list_first.py` | `boxes_list_second.py` | 5 s |
| Expanded version: Computation 8 (rank three) | `computation-8` | `boxes_walk_first.py` | `boxes_walk_second.py`; `boxes_compare.py` compares every level; small boxes also `boxes_small_third.py` | under 4 h + 25 min |
| Expanded version: Computation 9 (enlargements of X) | `computation-9` | `x_growth.py --frame` | `x_maximal_check.py` | 10 s |
| Expanded version: W_5 and its Ehrhart polynomial | `w5` | `w5_vertices.py` with `ehrhart_exact.py` (the exact counter of the search) | `w_ehrhart_check.py`; Normaliz; LattE | 20 s |
| Expanded version: the 25 one-pair deletions of W | `deletions` | `w_deletions.py` | Normaliz (`data/normaliz/deletions/`) | 4 min |
| The tests of the programs | `test` | each program's `--test` | | 3 min |
