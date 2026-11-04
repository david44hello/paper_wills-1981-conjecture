#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# x_growth.py - grow a member of W_4 (default: X) inside W_4; track g_1 and g_2 at every step
## version 0.20 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# Candidates: lattice points of Q+(X) \ X addable to X (Q+ from the Minkowski pyramid bound, maximality_check); Q+ only shrinks as the
# polytope grows, so this list is complete for every later step. Then random greedy orders; report the best g_1 / g_2 seen.
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 x_growth.py --start claimd_witness_D18.txt --runs 200 --seed 1
import argparse
import ast
import itertools
import random
from fractions import Fraction

import numpy as np

from ehrhart_exact import facets_of, ehrhart
from maximality_check import facet_nvols
from maximal_members import try_add
from generic_walk import invariants


def q_plus_candidates(points):
    normals, rhs = facets_of(points)
    coeffs, inner = ehrhart(points)
    vol = coeffs[4]
    nvol = facet_nvols(points, normals, rhs)
    slack = np.array([float(Fraction(24) * (16 - vol) / int(nv)) for nv in nvol])
    lam = 1 + max(slack / rhs)
    bound = int(np.ceil(lam * np.abs(points).max()))
    span = np.arange(-bound, bound + 1)
    tail = np.array(list(itertools.product(span, repeat=3)), dtype=np.int64)
    found = []
    for first in span:
        pts = np.hstack([np.full((len(tail), 1), first), tail])
        vals = pts @ normals.T
        keep = np.all(vals <= rhs + slack + 1e-9, axis=1) & np.any(vals > rhs, axis=1)
        found.extend(p for p in pts[keep] if tuple(p) > tuple(-p))
    return found, bound


def frame_candidates(points):
    """Lattice x with |c_i| <= 1, c = coordinates of x in the basis of 4 independent vertices of the start (its max-det frame)."""
    from scipy.spatial import ConvexHull
    verts = points[ConvexHull(points.astype(float)).vertices]
    best = None
    for combo in itertools.combinations(range(len(verts)), 4):
        det = abs(round(np.linalg.det(verts[list(combo)].astype(float))))
        if best is None or det > best[0]:
            best = (det, verts[list(combo)])
    det, vmat = best
    radius = int(np.abs(vmat).sum(axis=0).max())
    span = np.arange(-radius, radius + 1)
    box = np.array(list(itertools.product(span, repeat=4)), dtype=np.int64)
    coords = box @ np.linalg.inv(vmat.astype(float))  # x = c V  (rows of V are the vertices)
    keep = np.all(np.abs(coords) <= 1 + 1e-9, axis=1)
    present = {tuple(p) for p in points}
    cands = [x for x in box[keep] if tuple(x) not in present and tuple(x) > tuple(-x)]
    return cands, det


def score(points):
    (count, vol, g3, g1, g2), _ = invariants(points, np.ones(len(points), dtype=bool))
    return count, vol, g1, g2


def main_grow(path, runs, seed, use_frame):
    rng = random.Random(seed)
    start = np.array(ast.literal_eval(open(path).read()), dtype=np.int64)
    if use_frame:
        cands, bound = frame_candidates(start)
    else:
        cands, bound = q_plus_candidates(start)
    addable = [c for c in cands if try_add(start, c) is not None]
    print(f"start G={len(start)} score={score(start)}; region bound/det {bound}: {len(cands)} candidates, {len(addable)} addable",
          flush=True)
    best1, best2, maximal_seen = (Fraction(-99), None), (Fraction(-99), None), {}
    for run in range(runs):
        current = start
        order = list(range(len(addable)))
        rng.shuffle(order)
        present = {tuple(p) for p in current}
        for idx in order:
            if tuple(addable[idx]) in present:
                continue
            grown = try_add(current, addable[idx])
            if grown is None:
                continue
            current = grown
            present = {tuple(p) for p in current}
            count, vol, g1, g2 = score(current)
            if g1 > best1[0]:
                best1 = (g1, current.copy())
                print(f"  run {run}: new best g1 = {g1} ({float(g1):.4f}) at G={count}, vol={vol}", flush=True)
            if g2 > best2[0]:
                best2 = (g2, current.copy())
        final = score(current)
        maximal_seen[final] = maximal_seen.get(final, 0) + 1
    print(f"BEST g1 = {best1[0]} ({float(best1[0]):.4f}); BEST g2 = {best2[0]} ({float(best2[0]):.4f})")
    print("maximal end states (G, vol, g1, g2): count")
    for key, cnt in sorted(maximal_seen.items(), key=lambda kv: -kv[1]):
        print(f"  {tuple(str(x) for x in key)}: {cnt}")
    with open(path.replace(".txt", "_bestg1.txt"), "w") as out:
        out.write(str(best1[1].tolist() if best1[1] is not None else []))


def main():
    parser = argparse.ArgumentParser(description="grow a W_4 member")
    parser.add_argument("--start", required=True)
    parser.add_argument("--runs", type=int, required=True)
    parser.add_argument("--seed", type=int, required=True)
    parser.add_argument("--frame", action="store_true", help="candidates in the max-det parallelepiped of the start")
    args = parser.parse_args()
    main_grow(args.start, args.runs, args.seed, args.frame)


if __name__ == "__main__":
    main()
