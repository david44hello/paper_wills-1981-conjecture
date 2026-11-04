#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# boxes_list_second.py - the rank-3 boxes, second program: the list of boxes up to unimodular maps
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# Box Pi(Gamma, a') = {(z, t): z in Gamma cap {-1,0,1}^3, abs(t - a'.z) <= 1}. Conditions (N10 (B)): the cube points C of
# Gamma span R^3; a' solves a'.z_j in Z for 3 independent z_j in C; a' not in Gamma*. a' is taken mod Gamma* (shears).
# Classes: raw boxes are grouped by their exact Ehrhart data (G, vol, g_3, g_1, g_2) in a basis of Gamma x Z, and inside a
# group each box is shown lattice-equivalent to the group's first box by an EXPLICIT U in GL_4(Z) (no canonical key).
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 nice -n 19 python3 boxes_list_second.py --max-index 6
import argparse
import itertools
import time
from fractions import Fraction

import numpy as np
from scipy.spatial import ConvexHull

from generic_walk import invariants
from case3_reverse_search import fast_facets

CUBE = [tuple(v) for v in itertools.product((-1, 0, 1), repeat=3)]


def hnf3(index):
    """All lower-triangular column HNFs H (Gamma = H Z^3): 0 <= h21 < h22, 0 <= h31, h32 < h33, h11 h22 h33 = index."""
    out = []
    for h11, h22, h33 in itertools.product(range(1, index + 1), repeat=3):
        if h11 * h22 * h33 != index:
            continue
        for h21, h31, h32 in itertools.product(range(h22), range(h33), range(h33)):
            out.append(((h11, 0, 0), (h21, h22, 0), (h31, h32, h33)))
    return out


def solve3(mat, rhs):
    """Exact solution x of mat x = rhs (3 x 3, Fractions), or None if singular."""
    m = [[Fraction(v) for v in row] + [Fraction(r)] for row, r in zip(mat, rhs)]
    for col in range(3):
        piv = next((r for r in range(col, 3) if m[r][col] != 0), None)
        if piv is None:
            return None
        m[col], m[piv] = m[piv], m[col]
        for r in range(3):
            if r != col and m[r][col] != 0:
                fac = m[r][col] / m[col][col]
                m[r] = [a - fac * b for a, b in zip(m[r], m[col])]
    return tuple(m[i][3] / m[i][i] for i in range(3))


def det3(rows):
    (a, b, c), (d, e, f), (g, h, i) = rows
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def cube_points(hmat):
    """Gamma cap {-1,0,1}^3 with Gamma = H Z^3 (H's COLUMNS generate Gamma)."""
    cols = [tuple(hmat[r][c] for r in range(3)) for c in range(3)]
    pts = []
    for z in CUBE:
        y = solve3([[cols[c][r] for c in range(3)] for r in range(3)], z)
        if all(v.denominator == 1 for v in y):
            pts.append((z, tuple(int(v) for v in y)))
    return pts, cols


def shift_classes(points, cols):
    """All classes of a' mod Gamma* with a'.z_j integral for 3 independent cube points; key = (a'.c mod 1 for the columns c)."""
    reps = [z for z, _ in points if z > tuple(-v for v in z)]
    classes = {}
    for trio in itertools.combinations(reps, 3):
        q = abs(det3(trio))
        if q == 0:
            continue
        for n_vec in itertools.product(range(q), repeat=3):
            a = solve3(trio, n_vec)
            key = tuple(sum(ai * ci for ai, ci in zip(a, col)) % 1 for col in cols)
            if any(key):
                classes.setdefault(key, a)
    return classes


def box_points(points, a):
    out = []
    for z, y in points:
        center = sum(Fraction(zi) * ai for zi, ai in zip(z, a))
        lo, hi = -(-(center - 1).numerator // (center - 1).denominator), (center + 1).numerator // (center + 1).denominator
        out.extend(list(y) + [t] for t in range(lo, hi + 1))
    return np.array(out, dtype=np.int64)


def exact_vertex_invariant(points):
    """Vertices and a GL_4(Z)-invariant per vertex: (number of facets through it - exact integer facets, multiset of lattice
    lengths to the other vertices). (generic_walk's float version can miscount facets after rounding; not used here.)"""
    normals, rhs, hull = fast_facets(points)
    vidx = [int(v) for v in hull.vertices]
    on = (points[vidx] @ normals.T == rhs).sum(axis=1)
    inv = {}
    for k, v in enumerate(vidx):
        lengths = sorted(int(np.gcd.reduce(np.abs(points[w] - points[v]))) for w in vidx if w != v)
        inv[v] = (int(on[k]), tuple(lengths))
    return vidx, inv


def isomorphism(src, dst):
    """An integer U with det +-1 and U(src) = dst as point sets, found by matching 4 base vertices; None if none exists."""
    vs, inv_s = exact_vertex_invariant(src)
    vd, inv_d = exact_vertex_invariant(dst)
    if sorted(inv_s.values()) != sorted(inv_d.values()):
        return None
    base = []
    for v in vs:  # any 4 independent vertices determine U
        if np.linalg.matrix_rank(src[base + [v]].astype(float)) == len(base) + 1:
            base.append(v)
        if len(base) == 4:
            break
    binv = np.linalg.inv(src[list(base)].T.astype(float))
    target = {tuple(p) for p in dst}

    def pair_len(p, q):
        return int(np.gcd.reduce(np.abs(p - q)))

    def extend(chosen):
        k = len(chosen)
        if k == 4:
            umat = dst[chosen].T.astype(float) @ binv
            rounded = np.rint(umat)
            if np.max(np.abs(umat - rounded)) > 1e-9 or round(abs(np.linalg.det(rounded))) != 1:
                return None
            uint = rounded.astype(np.int64)
            return uint if {tuple(p) for p in (uint @ src.T).T} == target else None
        for cand in vd:
            if cand in chosen or inv_d[cand] != inv_s[base[k]]:
                continue
            if any(pair_len(dst[cand], dst[chosen[j]]) != pair_len(src[base[k]], src[base[j]]) for j in range(k)):
                continue
            found = extend(chosen + [cand])
            if found is not None:
                return found
        return None

    return extend([])


def main_boxlist(max_index):
    t0 = time.time()
    groups = {}  # Ehrhart key -> list of (index, H, a', points, rep_class_id)
    raw = 0
    for index in range(1, max_index + 1):
        n_gamma = n_span = 0
        for hmat in hnf3(index):
            n_gamma += 1
            points, cols = cube_points(hmat)
            if np.linalg.matrix_rank(np.array([z for z, _ in points], dtype=float)) < 3:
                continue
            n_span += 1
            for key, a in shift_classes(points, cols).items():
                raw += 1
                box = box_points(points, a)
                (count, vol, g3, g1, g2), _ = invariants(box, np.ones(len(box), dtype=bool))
                groups.setdefault((count, vol, g3, g1, g2), []).append((index, hmat, a, box))
        print(f"index {index}: {n_gamma} lattices Gamma, {n_span} with spanning cube points", flush=True)
    print(f"raw (Gamma, a' mod Gamma*) boxes: {raw}; Ehrhart groups: {len(groups)}", flush=True)
    classes = []
    for ekey, members in sorted(groups.items(), key=lambda kv: -kv[0][0]):
        reps = []
        for index, hmat, a, box in members:
            for rep in reps:
                if len(rep[3]) == len(box) and isomorphism(box, rep[3]) is not None:
                    rep[4] += 1
                    break
            else:
                reps.append([index, hmat, a, box, 1])
        for index, hmat, a, box, n_members in reps:
            classes.append((ekey, index, hmat, a, n_members))
    print(f"CLASSES (explicit GL_4(Z) maps, no canonical key): {len(classes)}  ({time.time() - t0:.1f} s)")
    for (count, vol, g3, g1, g2), index, hmat, a, n_members in classes:
        print(f"  G={count} vol={vol} g3={g3} g1={g1} g2={g2} | d={index} H={hmat} a'={tuple(str(v) for v in a)} "
              f"| raw boxes in class: {n_members}")


def main_test():
    """HNF counts = numbers of sublattices of Z^3; the isomorphism search finds a known map and rejects a non-map."""
    assert [len(hnf3(d)) for d in range(1, 7)] == [1, 7, 13, 35, 31, 91]
    points, _ = cube_points(((1, 0, 0), (0, 1, 0), (0, 0, 1)))
    box_a = box_points(points, (Fraction(1, 2), Fraction(1, 2), Fraction(0)))
    box_b = box_points(points, (Fraction(1), Fraction(1, 2), Fraction(1, 2)))   # shear t -> t - z_1, then z_1 <-> z_3
    box_c = box_points(points, (Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)))  # G 67: not equivalent
    umat = isomorphism(box_b, box_a)
    assert umat is not None and {tuple(p) for p in (umat @ box_b.T).T} == {tuple(p) for p in box_a}
    assert isomorphism(box_a, box_c) is None
    print("TEST PASS (HNF counts 1 7 13 35 31 91; known map found; G 69 vs G 67 rejected)")


def main():
    parser = argparse.ArgumentParser(description="the rank-3 box list, second program")
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--max-index", type=int)
    args = parser.parse_args()
    if args.test:
        main_test()
        return
    if args.max_index is None:
        parser.error("--max-index is required (no default)")
    main_boxlist(args.max_index)


if __name__ == "__main__":
    main()
