#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# index_bound_second.py - index bound, second program: all sublattices of Z^4 of index 2..16 by column HNF; spanning ones and maxima
## version 1.00 - 20261104 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
"""Checks the sentence of Computation 2: is 40,406 the number of ALL sublattices of index 2..16,
or of those whose points in {-1,0,1}^4 span R^4?  Also recomputes the maxima 45 (d=2) and <=27 (d>=3)."""
import itertools
import sys
from fractions import Fraction

CUBE_POINTS = [pt for pt in itertools.product((-1, 0, 1), repeat=4) if any(pt)]


def divisor_tuples(index_d):
    """All (a1,a2,a3,a4) of positive integers with product index_d."""
    divs = [k for k in range(1, index_d + 1) if index_d % k == 0]
    for a1 in divs:
        for a2 in divs:
            for a3 in divs:
                prod3 = a1 * a2 * a3
                if index_d % prod3 == 0:
                    yield (a1, a2, a3, index_d // prod3)


def lower_hnf_matrices(index_d):
    """Lower-triangular B (columns generate Gamma), diagonal a_i, row-i entries left of diagonal in [0, a_i)."""
    for diag in divisor_tuples(index_d):
        ranges = [range(diag[row]) for row in range(4) for _col in range(row)]
        for offdiag in itertools.product(*ranges):
            mat = [[0] * 4 for _ in range(4)]
            pos = 0
            for row in range(4):
                mat[row][row] = diag[row]
                for col in range(row):
                    mat[row][col] = offdiag[pos]
                    pos += 1
            yield mat


def in_lattice(mat, point):
    """Forward substitution: is point in B Z^4?"""
    coeffs = []
    for row in range(4):
        rest = point[row] - sum(mat[row][col] * coeffs[col] for col in range(row))
        if rest % mat[row][row]:
            return False
        coeffs.append(rest // mat[row][row])
    return True


def rank_of(points):
    rows = [[Fraction(v) for v in pt] for pt in points]
    rank = 0
    for col in range(4):
        pivot = next((r for r in range(rank, len(rows)) if rows[r][col] != 0), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for r in range(len(rows)):
            if r != rank and rows[r][col] != 0:
                factor = rows[r][col] / rows[rank][col]
                rows[r] = [x - factor * y for x, y in zip(rows[r], rows[rank])]
        rank += 1
    return rank


def main_count():
    total, spanning, max_by_d = 0, 0, {}
    for index_d in range(2, 17):
        for mat in lower_hnf_matrices(index_d):
            total += 1
            pts = [pt for pt in CUBE_POINTS if in_lattice(mat, pt)]
            if rank_of(pts) == 4:
                spanning += 1
                count = len(pts) + 1
                max_by_d[index_d] = max(max_by_d.get(index_d, 0), count)
    print(f"all sublattices of index 2..16: {total}")
    print(f"of these, cube points span R^4: {spanning}")
    print(f"max #(Gamma cap {{-1,0,1}}^4) by d (spanning only): {max_by_d}")
    return total, spanning, max_by_d


def main_test():
    total, _spanning, max_by_d = main_count()
    assert total == 40406, total
    assert max_by_d[2] == 45, max_by_d
    assert all(val <= 27 for d, val in max_by_d.items() if d >= 3), max_by_d
    print("tests pass")


def main():
    if "--test" in sys.argv:
        main_test()
    else:
        main_count()


if __name__ == "__main__":
    main()
