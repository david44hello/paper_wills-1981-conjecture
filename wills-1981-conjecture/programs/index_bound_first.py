#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# index_bound_first.py - index bound, first program: for every sublattice Gamma of Z^4 of index 2..16, |Gamma cap {-1,0,1}^4|
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# Sublattices of index d <-> row-style Hermite normal forms H (lower triangular,
# diagonal h_ii > 0 with product d, 0 <= h_ij < h_jj for i > j); Gamma = Z-row-span of H.
# A point x is in Gamma iff x = y H with y integral: forward substitution from the last column (H lower triangular).
import itertools
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ehrhart_count as ehr  # noqa: E402

CUBE = [pp for pp in itertools.product((-1, 0, 1), repeat=4)]


def diagonals(index):
    for aa in range(1, index + 1):
        for bb in range(1, index + 1):
            for cc in range(1, index + 1):
                if index % (aa * bb * cc) == 0:
                    yield (aa, bb, cc, index // (aa * bb * cc))


def hnfs(index):
    """All row-style lower-triangular HNFs of determinant index."""
    for diag in diagonals(index):
        below = [(ii, jj) for ii in range(4) for jj in range(ii)]       # entry (i, j), j < i, range 0..diag[j]-1
        for vals in itertools.product(*[range(diag[jj]) for _ii, jj in below]):
            mat = [[0] * 4 for _ in range(4)]
            for ii in range(4):
                mat[ii][ii] = diag[ii]
            for (ii, jj), vv in zip(below, vals):
                mat[ii][jj] = vv
            yield mat


def in_lattice(point, mat):
    """x = y H with H lower triangular: solve from the last coordinate (column 3 only has H[3][3])."""
    rem = list(point)
    for col in range(3, -1, -1):
        if rem[col] % mat[col][col]:
            return False
        coef = rem[col] // mat[col][col]
        for jj in range(4):
            rem[jj] -= coef * mat[col][jj]
    return all(xx == 0 for xx in rem)


def main():
    best = Counter()
    hist = Counter()
    big = []
    total = 0
    for index in range(2, 17):
        for mat in hnfs(index):
            total += 1
            pts = [pp for pp in CUBE if in_lattice(pp, mat)]
            full = len(pts) >= 4 and ehr.rank_of([list(pp) for pp in pts]) == 4
            if not full:
                continue
            hist[(index, len(pts))] += 1
            best[index] = max(best[index], len(pts))
            if len(pts) >= 31:
                big.append((index, len(pts), mat))
    print(f"sublattices of index 2..16 examined: {total}")
    for index in range(2, 17):
        print(f"index {index:2d}: max |Gamma cap cube| among full-rank = {best[index]}")
    print(f"Gamma with >= 31 cube points: {len(big)}; (index, count) histogram:",
          sorted(Counter((ii, cc) for ii, cc, _m in big).items()))


if __name__ == "__main__":
    main()
