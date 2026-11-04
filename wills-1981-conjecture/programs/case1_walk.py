#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# case1_walk.py - Case I, first program: exhaustive top-down walk over the symmetric saturated subsets of {-1,0,1}^4
## version 0.50 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# Why exhaustive: if S is saturated (S = conv(S) cap Z^4) and S != T, some vertex pair of conv(T) lies outside S, so removing
# it from T and re-saturating keeps S inside; hence every saturated S is reached from the cube.
# n = 4 identities (ledger L0): g_1 = (G-1)/2 - g_3, g_2 = (G-1)/2 - vol; g_3 = sum_F NVol_3(F)/12, vol = sum |det|/24.
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 case1_walk.py --test   |   --enumerate --min-g 1
import argparse
import itertools
import time
from fractions import Fraction

import numpy as np
from scipy.spatial import ConvexHull

from ehrhart_exact import ehrhart, facets_of
from set_guard import exact_guard

POINTS = np.array(list(itertools.product([-1, 0, 1], repeat=4)), dtype=np.int64)
INDEX = {tuple(p): i for i, p in enumerate(POINTS)}
NEG = np.array([INDEX[tuple(-p)] for p in POINTS])


def symmetry_permutations():
    """The 384 signed coordinate permutations, as permutations of the 81 point indices."""
    perms = []
    for order in itertools.permutations(range(4)):
        for signs in itertools.product([1, -1], repeat=4):
            image = POINTS[:, order] * np.array(signs)
            perms.append(np.array([INDEX[tuple(p)] for p in image]))
    return np.array(perms)


GROUP = symmetry_permutations()
WEIGHTS = np.array([1 << i for i in range(81)], dtype=object)


def canonical(mask):
    """Canonical key of a boolean point mask: the lexicographically least packed image under the group."""
    images = np.zeros((len(GROUP), 81), dtype=bool)
    images[np.arange(len(GROUP))[:, None], GROUP] = mask[None, :]
    packed = np.packbits(images, axis=1)
    best = min(range(len(GROUP)), key=lambda g: packed[g].tobytes())
    return packed[best].tobytes()


def saturate(mask):
    """(saturated mask, exact facets) of conv(points in mask); None if not full-dimensional."""
    pts = POINTS[mask]
    if np.linalg.matrix_rank(pts.astype(float)) < 4:
        return None
    normals, rhs = facets_of(pts)
    inside = np.all(POINTS @ normals.T <= rhs, axis=1)
    return inside, normals, rhs


def invariants(mask, want_vertices=False):
    """Exact (G, vol, g_3, g_1, g_2) for the saturated set mask (0 interior; n = 4); optionally qhull's vertex indices."""
    pts = POINTS[mask]
    hull = ConvexHull(pts.astype(float))
    simp = pts[hull.simplices].astype(float)                      # (k, 4, 4)
    dets = np.rint(np.abs(np.linalg.det(simp))).astype(np.int64)
    diffs = simp[:, 1:, :] - simp[:, :1, :]                       # (k, 3, 4)
    minors = np.stack([np.rint(np.linalg.det(np.delete(diffs, c, axis=2))).astype(np.int64) for c in range(4)], axis=1)
    nvol3 = np.gcd.reduce(np.abs(minors), axis=1)
    keep = dets > 0
    assert np.all(nvol3[keep] > 0) and np.all(dets[keep] % nvol3[keep] == 0), "lattice height not integral"
    count = int(mask.sum())
    vol = Fraction(int(dets[keep].sum()), 24)
    g3 = Fraction(int(nvol3[keep].sum()), 12)
    half = Fraction(count - 1, 2)
    result = (count, vol, g3, half - g3, half - vol)
    if want_vertices:
        return result, np.flatnonzero(mask)[hull.vertices]
    return result


def run_test(samples):
    """Cross-check invariants() against the full Ehrhart interpolation of ehrhart_exact on random saturated sets."""
    rng = np.random.default_rng(7)
    checked = 0
    while checked < samples:
        reps = rng.random(81) < rng.uniform(0.1, 0.6)
        mask = reps | reps[NEG]
        mask[INDEX[(0, 0, 0, 0)]] = True
        result = saturate(mask)
        if result is None:
            continue
        sat = result[0]
        count, vol, g3, g1, g2 = invariants(sat)
        coeffs, inner = ehrhart(POINTS[sat])
        assert inner == 1 and coeffs[1] == g1 and coeffs[2] == g2 and coeffs[3] == g3 and coeffs[4] == vol, (coeffs, g1, g2, g3, vol)
        checked += 1
    print(f"invariants() agrees with ehrhart_exact.ehrhart() on {samples} random saturated sets")


def vertex_pairs(mask):
    pts = POINTS[mask]
    hull = ConvexHull(pts.astype(float))
    idx = np.flatnonzero(mask)[hull.vertices]
    return sorted({min(i, NEG[i]) for i in idx})


def unpack(key):
    return np.unpackbits(np.frombuffer(key, dtype=np.uint8))[:81].astype(bool)


def enumerate_classes(min_g, seconds, out_path):
    """Level by level (G = 81, 79, ...): every class at the level is evaluated; near-records (g1 > 7, g2 > 22) are logged."""
    from case3_reverse_search import fast_facets  # imported here: case3_reverse_search -> dual_lattice_l1 -> case2_walk imports THIS module
    records = open(out_path, "w")
    frontier = [canonical(np.ones(81, dtype=bool))]
    best_g1, best_g2 = Fraction(-99), Fraction(-99)
    ties, total = [], 0
    deadline = time.time() + seconds
    while frontier and time.time() < deadline:
        nxt = set()
        level_g1, level_g2, level_g = Fraction(-99), Fraction(-99), None
        for key in frontier:
            mask = unpack(key)
            (count, vol, g3, g1, g2), verts = invariants(mask, want_vertices=True)
            assert level_g in (None, count), ("level mixes G", level_g, count)
            normals, rhs, _ = fast_facets(POINTS[mask])
            exact_guard(POINTS, mask, verts, normals, rhs, "CaseI-cube")
            pairs = sorted({int(min(i, NEG[i])) for i in verts})
            level_g = count
            level_g1, level_g2 = max(level_g1, g1), max(level_g2, g2)
            if g1 > 7 or g2 > 22:
                records.write(f"{count} {vol} {g3} {g1} {g2} {','.join(map(str, np.flatnonzero(mask).tolist()))}\n")
            if (g1 >= 8 or g2 >= 24) and count < 81:
                ties.append((count, g1, g2, np.flatnonzero(mask).tolist()))
            for rep in pairs:
                child = mask.copy()
                child[rep] = False
                child[NEG[rep]] = False
                if child.sum() < min_g or np.linalg.matrix_rank(POINTS[child].astype(float)) < 4:
                    continue
                nxt.add(canonical(child))
        total += len(frontier)
        best_g1, best_g2 = max(best_g1, level_g1), max(best_g2, level_g2)
        records.flush()
        print(f"G={level_g}: classes {len(frontier)} (total {total}); level max g1 {level_g1} = {float(level_g1):.4f}, "
              f"max g2 {level_g2} = {float(level_g2):.4f}; next level {len(nxt)}; {time.strftime('%H:%M:%S')}", flush=True)
        frontier = list(nxt)
    complete = not frontier
    records.close()
    return total, complete, (best_g1, None), (best_g2, None), ties


def main():
    parser = argparse.ArgumentParser(description="exhaustive W_4 search inside the cube")
    parser.add_argument("--test", type=int, default=0, help="number of random cross-checks")
    parser.add_argument("--enumerate", action="store_true")
    parser.add_argument("--min-g", type=int, default=1, help="prune classes with fewer lattice points")
    parser.add_argument("--seconds", type=float, default=600)
    parser.add_argument("--out", default="enum4_records.txt", help="one line per class: G vol g3 g1 g2 point-indices")
    args = parser.parse_args()
    if args.test:
        run_test(args.test)
    if args.enumerate:
        total, complete, best_g1, best_g2, ties = enumerate_classes(args.min_g, args.seconds, args.out)
        print(f"classes {total} complete={complete} (min G {args.min_g}); max g1 = {best_g1[0]}, max g2 = {best_g2[0]}")
        print(f"non-cube classes with g1 >= 8 or g2 >= 24: {len(ties)}")
        for row in ties[:20]:
            print("  ", row[:3])


if __name__ == "__main__":
    main()
