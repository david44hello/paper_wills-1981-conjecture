#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# case3_frame_setup.py - Case III, first program: set-up of a frame lattice (frame points, symmetries, admissibility tests)
## version 0.20 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# Frame = rows of a column HNF H (D = det H) whose cross-polytope is in W_4 (frame_lattices_first list). Candidates: x in Z^4 with
# x V^{-1} in [-1,1]^4. Symmetry: signed permutations of the frame coordinates that preserve the lattice (checked exactly).
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 case3_frame_setup.py --index 12 --which 0 --max-states 20000
import argparse
import itertools
import time
from fractions import Fraction

import numpy as np
from scipy.spatial import ConvexHull

from dual_lattice_l1 import min_l1_dual
from case2_walk import hnf_lattices
from maximal_members import lattice_points_and_interior
from ehrhart_exact import facets_of
from generic_walk import invariants


def frame_setup(hmat):
    vmat = hmat.astype(np.int64)
    det = int(round(abs(np.linalg.det(vmat.astype(float)))))
    radius = int(np.abs(vmat).sum(axis=0).max())
    span = np.arange(-radius, radius + 1)
    box = np.array(list(itertools.product(span, repeat=4)), dtype=np.int64)
    coords = box @ np.linalg.inv(vmat.astype(float))
    frame = box[np.all(np.abs(coords) <= 1 + 1e-9, axis=1)]
    index = {tuple(p): i for i, p in enumerate(frame)}
    neg = np.array([index[tuple(-p)] for p in frame])
    perms = []
    cframe = np.rint(frame @ np.linalg.inv(vmat.astype(float)) * det).astype(np.int64)  # det * c (exact integers)
    cindex = {tuple(c): i for i, c in enumerate(cframe)}
    for order in itertools.permutations(range(4)):
        for signs in itertools.product([1, -1], repeat=4):
            image = cframe[:, list(order)] * np.array(signs)
            perm = [cindex.get(tuple(c)) for c in image]
            if None not in perm:
                perms.append(perm)
    return frame, neg, np.array(perms), det, vmat


def max_vertex_det(points):
    verts = points[ConvexHull(points.astype(float)).vertices]
    reps = {tuple(v) if tuple(v) > tuple(-v) else tuple(-v) for v in verts}
    reps = np.array(sorted(reps), dtype=float)
    best = 0
    for combo in itertools.combinations(range(len(reps)), 4):
        best = max(best, abs(np.linalg.det(reps[list(combo)])))
    return int(round(best))


def bfs(hmat, max_states, min_g, max_seconds):
    frame, neg, perms, det, vmat = frame_setup(hmat)
    size = len(frame)

    def canon(mask):
        images = np.zeros((len(perms), size), dtype=bool)
        images[np.arange(len(perms))[:, None], perms] = mask[None, :]
        return min(row.tobytes() for row in np.packbits(images, axis=1))

    def saturate(points):
        """Frame points in conv(points) (all lattice points of conv lie in the frame); None if a nonzero one is interior."""
        normals, rhs = facets_of(points)
        values = frame @ normals.T
        inside = np.all(values <= rhs, axis=1)
        strict = np.all(values < rhs, axis=1)
        if strict.sum() != 1:
            return None
        return inside

    def det_ok(old_mask, new_pt):
        """All |det(new, a, b, c)| <= D for a, b, c among the vertex reps of the old hull (old tuples already passed)."""
        pts = frame[old_mask]
        verts = pts[ConvexHull(pts.astype(float)).vertices]
        reps = np.array(sorted({tuple(v) if tuple(v) > tuple(-v) else tuple(-v) for v in verts}), dtype=float)
        triples = np.array(list(itertools.combinations(range(len(reps)), 3)))
        if len(triples) == 0:
            return True
        stack = np.concatenate([np.repeat(new_pt[None, None, :].astype(float), len(triples), axis=0), reps[triples]], axis=1)
        return bool(np.all(np.abs(np.linalg.det(stack)) <= det + 1e-6))

    start = saturate(np.vstack([vmat, -vmat]))
    assert start is not None
    seen = {canon(start)}
    frontier, states, best1, best2, flagged = [start], 0, Fraction(-99), Fraction(-99), []
    t0 = time.time()
    while frontier and states < max_states and time.time() - t0 < max_seconds:
        nxt = []
        for mask in frontier:
            states += 1
            pts = frame[mask]
            (count, vol, g3, g1, g2), _ = invariants(pts, np.ones(len(pts), dtype=bool))
            if count >= min_g:
                best1, best2 = max(best1, g1), max(best2, g2)
                if g1 >= 8 or g2 >= 24:
                    flagged.append((count, str(g1), str(g2)))
            for rep in range(size):
                if mask[rep] or rep > neg[rep]:
                    continue
                child_pts = np.vstack([pts, frame[rep], frame[neg[rep]]])
                if not det_ok(mask, frame[rep]):
                    continue
                child = saturate(child_pts)
                if child is None:
                    continue
                key = canon(child)
                if key not in seen:
                    seen.add(key)
                    nxt.append(child)
        frontier = nxt
    complete = not frontier
    return dict(det=det, frame_points=size, symmetries=len(perms), states=states, complete=complete, levels_left=len(frontier),
                best_g1=best1, best_g2=best2, flagged=flagged, seconds=round(time.time() - t0, 1))


def main():
    parser = argparse.ArgumentParser(description="PATH C prototype")
    parser.add_argument("--index", type=int, required=True)
    parser.add_argument("--which", type=int, required=True, help="which valid HNF of that index (0-based)")
    parser.add_argument("--max-states", type=int, required=True)
    parser.add_argument("--min-g", type=int, default=31)
    parser.add_argument("--max-seconds", type=float, default=90)
    args = parser.parse_args()
    valid = [h for h in hnf_lattices(args.index) if min_l1_dual(h, args.index)[0] >= 1]
    hmat = valid[args.which]
    result = bfs(hmat, args.max_states, args.min_g, args.max_seconds)
    print(f"D={args.index} frame #{args.which}/{len(valid)} H={hmat.tolist()}: {result}")


if __name__ == "__main__":
    main()
