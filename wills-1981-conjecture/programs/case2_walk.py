#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# case2_walk.py - Case II, first program: walk the Gamma-saturated symmetric subsets of Gamma cap {-1,0,1}^4
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# For each Gamma: S = Gamma cap {-1,0,1}^4; conv(S) is in W_4 w.r.t. Gamma (its interior lies in (-1,1)^4); walk top-down
# (S minus a vertex pair stays saturated), dedupe under the stabilizer of Gamma in B_4, invariants in a Gamma-basis
# (z = H^{-1} y), n = 4 identities g_1 = (G-1)/2 - g_3, g_2 = (G-1)/2 - vol.
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 case2_walk.py --min-g 31 [--test]
import argparse
import itertools
from fractions import Fraction

import numpy as np

from case1_walk import POINTS, INDEX, NEG, GROUP
from ehrhart_exact import ehrhart

INDICES = (2,)  # index >= 3 has at most 27 cube points (closed by L3)
SIGNED_PERMS = [(order, signs) for order in itertools.permutations(range(4)) for signs in itertools.product([1, -1], repeat=4)]


def hnf_lattices(index):
    """All lower-triangular column HNFs H (Gamma = H Z^4) with det = index."""
    for diag in itertools.product([d for d in range(1, index + 1) if index % d == 0], repeat=4):
        if int(np.prod(diag)) != index:
            continue
        ranges = [range(diag[i]) for i in range(4) for j in range(i)]
        for below in itertools.product(*ranges):
            mat = np.diag(diag).astype(np.int64)
            pos = 0
            for i in range(4):
                for j in range(i):
                    mat[i, j] = below[pos]
                    pos += 1
            yield mat


def members(mat, vecs):
    """Boolean: which integer vectors (rows of vecs) lie in Gamma = mat Z^4 (forward substitution, exact)."""
    rest = vecs.copy()
    ok = np.ones(len(vecs), dtype=bool)
    for i in range(4):
        coeff = rest[:, i] // mat[i, i]
        ok &= (rest[:, i] % mat[i, i] == 0)
        rest = rest - np.outer(coeff, mat[:, i])
    return ok


def to_basis(mat, vecs):
    """Exact coordinates z with mat z = y, for rows y in Gamma."""
    rest = vecs.copy()
    coords = np.zeros_like(vecs)
    for i in range(4):
        assert np.all(rest[:, i] % mat[i, i] == 0)
        coeff = rest[:, i] // mat[i, i]
        coords[:, i] = coeff
        rest = rest - np.outer(coeff, mat[:, i])
    assert np.all(rest == 0)
    return coords


def stabilizer(mat):
    """Indices g of GROUP (signed perms, as point permutations) with g(Gamma) = Gamma."""
    keep = []
    for gidx, (order, signs) in enumerate(SIGNED_PERMS):
        image = mat[list(order), :] * np.array(signs)[:, None]  # g applied to the columns of mat
        if np.all(members(mat, image.T)):
            keep.append(gidx)
    return keep


def invariants_in(zpts):
    from scipy.spatial import ConvexHull
    hull = ConvexHull(zpts.astype(float))
    simp = zpts[hull.simplices].astype(float)
    dets = np.rint(np.abs(np.linalg.det(simp))).astype(np.int64)
    diffs = simp[:, 1:, :] - simp[:, :1, :]
    minors = np.stack([np.rint(np.linalg.det(np.delete(diffs, c, axis=2))).astype(np.int64) for c in range(4)], axis=1)
    nvol3 = np.gcd.reduce(np.abs(minors), axis=1)
    keep = dets > 0
    count = len(zpts)
    half = Fraction(count - 1, 2)
    vol, g3 = Fraction(int(dets[keep].sum()), 24), Fraction(int(nvol3[keep].sum()), 12)
    return (count, vol, g3, half - g3, half - vol), hull.vertices


def walk_gamma(mat, mask0, group_rows, min_g):
    """Top-down walk from mask0 (cube points in Gamma); returns (classes, max g1, max g2, best masks)."""
    def canon(mask):
        images = np.zeros((len(group_rows), 81), dtype=bool)
        images[np.arange(len(group_rows))[:, None], group_rows] = mask[None, :]
        return min(row.tobytes() for row in np.packbits(images, axis=1))

    frontier = {canon(mask0): mask0}
    total, best1, best2, arg1 = 0, Fraction(-99), Fraction(-99), None
    while frontier:
        nxt = {}
        for mask in frontier.values():
            zpts = to_basis(mat, POINTS[mask])
            (count, vol, g3, g1, g2), vidx = invariants_in(zpts)
            if g1 > best1:
                best1, arg1 = g1, mask.copy()
            best2 = max(best2, g2)
            pairs = sorted({min(i, NEG[i]) for i in np.flatnonzero(mask)[vidx]})
            for rep in pairs:
                child = mask.copy()
                child[rep] = child[NEG[rep]] = False
                if child.sum() < min_g or np.linalg.matrix_rank(POINTS[child].astype(float)) < 4:
                    continue
                key = canon(child)
                if key not in nxt:
                    nxt[key] = child
        total += len(frontier)
        frontier = nxt
    return total, best1, best2, arg1


def main_case2(min_g, test):
    if test:  # Gamma = Z^4 must reproduce enum4 (G >= 63: 2853 classes, max g1 = 8, g2 = 24)
        mat = np.eye(4, dtype=np.int64)
        total, b1, b2, _ = walk_gamma(mat, np.ones(81, dtype=bool), GROUP, 63)
        assert (total, b1, b2) == (2853, 8, 24), (total, b1, b2)
        zcheck = to_basis(np.array([[2, 0, 0, 0], [1, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]), np.array([[2, 2, 0, 0], [0, 0, 1, 0]]))
        print("test passed: Gamma = Z^4 reproduces 2853 classes, max g1 = 8, max g2 = 24; basis change", zcheck.tolist())
        return
    overall1, overall2, rows = Fraction(-99), Fraction(-99), []
    for index in INDICES:
        lattices = 0
        for mat in hnf_lattices(index):
            mask0 = members(mat, POINTS)
            if mask0.sum() < min_g or np.linalg.matrix_rank(POINTS[mask0].astype(float)) < 4:
                continue
            lattices += 1
            group_rows = GROUP[stabilizer(mat)]
            total, b1, b2, arg1 = walk_gamma(mat, mask0, group_rows, min_g)
            overall1, overall2 = max(overall1, b1), max(overall2, b2)
            rows.append((index, int(mask0.sum()), total, b1, b2, mat.tolist()))
            print(f"index {index} G0={int(mask0.sum())} classes={total} max g1={b1} ({float(b1):.3f}) max g2={b2} "
                  f"({float(b2):.3f}) H={mat.tolist()}", flush=True)
        print(f"== index {index}: {lattices} lattices with >= {min_g} cube points", flush=True)
    print(f"CASE II (G >= {min_g}): overall max g1 = {overall1} ({float(overall1):.4f}), max g2 = {overall2} ({float(overall2):.4f})")


def main():
    parser = argparse.ArgumentParser(description="L6 Case II walk")
    parser.add_argument("--min-g", type=int, default=31)
    parser.add_argument("--test", action="store_true")
    args = parser.parse_args()
    main_case2(args.min_g, args.test)


if __name__ == "__main__":
    main()
