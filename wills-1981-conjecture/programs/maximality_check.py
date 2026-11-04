#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# maximality_check.py - exact maximality test for members of W_4 and for the box polytopes
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# Claim used: if lattice x is beyond facet F of Q by delta = a_F.x - b_F >= 1 (a_F primitive), conv(Q u {+-x}) contains the
# pyramid conv(F u {x}) outside Q, of volume delta * NVol_3(F) / 24. Minkowski (vol <= 16 on W_4) then forces
# delta <= 24 (16 - vol Q) / NVol_3(F) for EVERY facet F. So all addable x lie in the bounded Q+ = {a_F.x <= b_F + d_F},
# Q+ inside lambda*Q with lambda = 1 + max d_F / b_F. We test every lattice x in Q+ \ Q (one of each +-pair).
import argparse
import itertools
from fractions import Fraction

import numpy as np
from scipy.spatial import ConvexHull

from ehrhart_exact import facets_of, ehrhart
from maximal_members import try_add, l6_case


def facet_nvols(points, normals, rhs):
    """NVol_3 of each facet: sum over boundary simplices on that facet of |det| / height."""
    hull = ConvexHull(points.astype(float))
    nvol = np.zeros(len(normals), dtype=np.int64)
    for simplex in hull.simplices:
        pts = points[simplex]
        det = int(round(abs(np.linalg.det(pts.astype(float)))))
        if det == 0:
            continue
        tight = np.flatnonzero(np.all(pts @ normals.T == rhs, axis=0))
        assert len(tight) == 1
        nvol[tight[0]] += det // int(rhs[tight[0]])
    return nvol


def certify_maximal(points):
    normals, rhs = facets_of(points)
    coeffs, inner = ehrhart(points)
    assert inner == 1
    vol = coeffs[4]
    nvol = facet_nvols(points, normals, rhs)
    assert Fraction(int(nvol.sum() * 0 + (rhs * nvol).sum()), 24) == vol, "facet volumes do not add up to vol"
    slack = [Fraction(24) * (16 - vol) / int(nv) for nv in nvol]
    lam = 1 + max(sl / int(b) for sl, b in zip(slack, rhs))
    bound = int(np.ceil(float(lam) * np.abs(points).max()))
    span = np.arange(-bound, bound + 1)
    box = np.array(list(itertools.product(span, repeat=4)), dtype=np.int64)
    values = box @ normals.T
    limit = np.array([float(int(b) + sl) for b, sl in zip(rhs, slack)])
    in_plus = np.all(values <= limit + 1e-9, axis=1)
    outside_q = np.any(values > rhs, axis=1)
    cands = box[in_plus & outside_q]
    cands = np.array([c for c in cands if tuple(c) > tuple(-c)])
    addable = [c for c in cands if try_add(points, c) is not None]
    return coeffs, len(cands), addable, bound


def box_polytope(a_vec):
    """Lattice points of Pi(a) = {|y_i| <= 1 (i = 1..3), |t - a.y| <= 1}, coordinates (y1, y2, y3, t)."""
    pts = []
    for y in itertools.product([-1, 0, 1], repeat=3):
        center = sum(Fraction(ai) * yi for ai, yi in zip(a_vec, y))
        for t in range(int(np.floor(float(center))) - 2, int(np.ceil(float(center))) + 3):
            if abs(t - center) <= 1:
                pts.append(list(y) + [t])
    return np.array(pts, dtype=np.int64)


def main():
    parser = argparse.ArgumentParser(description="maximality certificates")
    parser.add_argument("--boxes", action="store_true")
    parser.add_argument("--cube-and-t", action="store_true")
    args = parser.parse_args()
    targets = []
    if args.cube_and_t:
        from cell24_walk import LATT
        targets += [("cube", np.array(list(itertools.product([-1, 0, 1], repeat=4)), dtype=np.int64)), ("24-cell T", LATT)]
    if args.boxes:
        targets += [("Q_b a=(1/2,1/2,1/2)", box_polytope([Fraction(1, 2)] * 3)),
                    ("Q_b a=(1/3,1/3,1/3)", box_polytope([Fraction(1, 3)] * 3))]
    for name, pts in targets:
        coeffs, ncand, addable, bound = certify_maximal(pts)
        case, rank = l6_case(pts)
        print(f"{name}: G={len(pts)} g={[str(c) for c in coeffs]} case {case} (rank M {rank}); candidates in Q+\\Q "
              f"(box radius {bound}): {ncand}; addable: {len(addable)} -> MAXIMAL={not addable}", flush=True)
        for c in addable[:5]:
            print("   addable:", c.tolist())


if __name__ == "__main__":
    main()
