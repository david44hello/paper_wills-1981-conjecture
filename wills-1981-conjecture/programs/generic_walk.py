#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# generic_walk.py - top-down walk of the saturated symmetric sub-polytopes of any Q in W_4, up to the automorphisms of Q
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# Input: Q's lattice points (all of them; Q saturated). Output per level G: classes, max g_1, max g_2 (n = 4 identities).
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 generic_walk.py --test   |   --points FILE --min-g 31
import argparse
import ast
import itertools
from fractions import Fraction

import numpy as np
from scipy.spatial import ConvexHull


def vertex_invariant(points, vidx, hull):
    """A unimodular invariant of each vertex: (number of facets through it, lattice-length multiset to other vertices)."""
    normals = np.unique(np.round(hull.equations / np.linalg.norm(hull.equations[:, :-1], axis=1)[:, None], 6), axis=0)
    keys = {}
    for v in vidx:
        on = int(np.sum(np.abs(normals[:, :-1] @ points[v] + normals[:, -1]) < 1e-9))
        lengths = []
        for w in vidx:
            if w != v:
                diff = points[w] - points[v]
                lengths.append(int(np.gcd.reduce(np.abs(diff))))
        keys[v] = (on, tuple(sorted(lengths)))
    return keys


def automorphisms(points):
    """All U in GL_4(Z) with U(points) = points, as index permutations of points."""
    hull = ConvexHull(points.astype(float))
    vidx = list(hull.vertices)
    inv = vertex_invariant(points, vidx, hull)
    lookup = {tuple(p): i for i, p in enumerate(points)}
    base = None
    for combo in itertools.combinations(vidx, 4):
        det = round(abs(np.linalg.det(points[list(combo)].astype(float))))
        if det and (base is None or det < base[0]):
            base = (det, combo)
    det_b, base_idx = base
    bmat = points[list(base_idx)].T.astype(float)
    binv = np.linalg.inv(bmat)
    perms = []

    def extend(chosen):
        if len(chosen) == 4:
            img = points[chosen].T.astype(float)
            umat = img @ binv
            rounded = np.rint(umat)
            if np.max(np.abs(umat - rounded)) > 1e-9 or round(abs(np.linalg.det(rounded))) != 1:
                return
            mapped = (rounded.astype(np.int64) @ points.T).T
            perm = [lookup.get(tuple(m)) for m in mapped]
            if None not in perm:
                perms.append(perm)
            return
        target = base_idx[len(chosen)]
        for cand in vidx:
            if inv[cand] != inv[target] or cand in chosen:
                continue
            sub = list(base_idx[:len(chosen) + 1])
            img = list(chosen) + [cand]
            if round(abs(np.linalg.det(np.vstack([points[img], np.eye(4)[len(img):]]).astype(float)))) != \
               round(abs(np.linalg.det(np.vstack([points[sub], np.eye(4)[len(sub):]]).astype(float)))):
                pass  # partial dets are not invariant under U in general; full check happens at depth 4
            extend(chosen + [cand])

    extend([])
    return np.array(perms)


def invariants(points, mask):
    pts = points[mask]
    hull = ConvexHull(pts.astype(float))
    simp = pts[hull.simplices].astype(float)
    dets = np.rint(np.abs(np.linalg.det(simp))).astype(np.int64)
    diffs = simp[:, 1:, :] - simp[:, :1, :]
    minors = np.stack([np.rint(np.linalg.det(np.delete(diffs, c, axis=2))).astype(np.int64) for c in range(4)], axis=1)
    nvol3 = np.gcd.reduce(np.abs(minors), axis=1)
    keep = dets > 0
    half = Fraction(int(mask.sum()) - 1, 2)
    vol, g3 = Fraction(int(dets[keep].sum()), 24), Fraction(int(nvol3[keep].sum()), 12)
    return (int(mask.sum()), vol, g3, half - g3, half - vol), np.flatnonzero(mask)[hull.vertices]


def walk(points, perms, min_g, verbose=True):
    neg = np.array([{tuple(p): i for i, p in enumerate(points)}[tuple(-p)] for p in points])
    size = len(points)

    def canon(mask):
        images = np.zeros((len(perms), size), dtype=bool)
        images[np.arange(len(perms))[:, None], perms] = mask[None, :]
        return min(row.tobytes() for row in np.packbits(images, axis=1))

    full = np.ones(size, dtype=bool)
    frontier = {canon(full): full}
    total, best1, best2, levels = 0, Fraction(-99), Fraction(-99), []
    while frontier:
        nxt, lv1, lv2, level_g = {}, Fraction(-99), Fraction(-99), None
        for mask in frontier.values():
            (count, vol, g3, g1, g2), verts = invariants(points, mask)
            level_g, lv1, lv2 = count, max(lv1, g1), max(lv2, g2)
            for rep in sorted({min(i, neg[i]) for i in verts}):
                child = mask.copy()
                child[rep] = child[neg[rep]] = False
                if child.sum() < min_g or np.linalg.matrix_rank(points[child].astype(float)) < 4:
                    continue
                key = canon(child)
                if key not in nxt:
                    nxt[key] = child
        total += len(frontier)
        best1, best2 = max(best1, lv1), max(best2, lv2)
        levels.append((level_g, len(frontier), lv1, lv2))
        if verbose:
            print(f"  G={level_g}: classes {len(frontier)}; max g1 {lv1} ({float(lv1):.3f}), max g2 {lv2} ({float(lv2):.3f})",
                  flush=True)
        frontier = nxt
    return total, best1, best2, levels


def run_test():
    cube = np.array(list(itertools.product([-1, 0, 1], repeat=4)), dtype=np.int64)
    perms = automorphisms(cube)
    assert len(perms) == 384, len(perms)
    total, b1, b2, _ = walk(cube, perms, 63, verbose=False)
    assert (total, b1, b2) == (2853, 8, 24), (total, b1, b2)
    from cell24_walk import LATT
    tperms = automorphisms(LATT)
    total_t, b1t, _, _ = walk(LATT, tperms, 9, verbose=False)
    print(f"test passed: |Aut(cube)| = 384, cube walk G>=63 = 2853 classes; |Aut(T)| = {len(tperms)}, T walk = {total_t} "
          f"classes (cell24_walk used only B_4: 8863), max g1 = {b1t}")


def main():
    parser = argparse.ArgumentParser(description="generic W_4 walk")
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--points", help="file: a Python list of Q's lattice points")
    parser.add_argument("--min-g", type=int, default=31)
    args = parser.parse_args()
    if args.test:
        run_test()
    if args.points:
        points = np.array(ast.literal_eval(open(args.points).read()), dtype=np.int64)
        perms = automorphisms(points)
        print(f"|Q cap Z^4| = {len(points)}, |Aut(Q)| = {len(perms)}")
        total, b1, b2, _ = walk(points, perms, args.min_g)
        print(f"WALK (G >= {args.min_g}): {total} classes, max g1 = {b1} ({float(b1):.4f}), max g2 = {b2} ({float(b2):.4f})")


if __name__ == "__main__":
    main()
