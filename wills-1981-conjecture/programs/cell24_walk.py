#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# cell24_walk.py - top-down walk over the saturated symmetric sub-polytopes of the 24-cell T in its lattice
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# c-coordinates are doubled (2c in Z^4) for exact symmetry; invariants are computed in Z^4 = L-coordinates via cell24_coords.
import itertools
import time
from fractions import Fraction

import numpy as np
from scipy.spatial import ConvexHull

from cell24_coords import to_lattice_coords
from ehrhart_exact import ehrhart


def t_points_doubled():
    """All L-points of T = {|c_i| <= 1, sum |c_i| <= 2}, as doubled c-coordinates."""
    pts = []
    for d in itertools.product(range(-2, 3), repeat=4):
        parity = {x % 2 for x in d}
        if len(parity) == 1 and max(abs(x) for x in d) <= 2 and sum(abs(x) for x in d) <= 4:
            pts.append(d)
    return pts


DOUBLED = t_points_doubled()
INDEX = {p: i for i, p in enumerate(DOUBLED)}
LATT = np.array([to_lattice_coords([Fraction(x, 2) for x in p]) for p in DOUBLED], dtype=np.int64)
NEG = np.array([INDEX[tuple(-x for x in p)] for p in DOUBLED])
GROUP = []
for order in itertools.permutations(range(4)):
    for signs in itertools.product([1, -1], repeat=4):
        GROUP.append([INDEX[tuple(signs[k] * p[order[k]] for k in range(4))] for p in DOUBLED])
GROUP = np.array(GROUP)


def canonical(mask):
    images = np.zeros((len(GROUP), len(DOUBLED)), dtype=bool)
    images[np.arange(len(GROUP))[:, None], GROUP] = mask[None, :]
    packed = np.packbits(images, axis=1)
    return min(row.tobytes() for row in packed)


def unpack(key):
    return np.unpackbits(np.frombuffer(key, dtype=np.uint8))[:len(DOUBLED)].astype(bool)


def invariants(mask):
    pts = LATT[mask]
    hull = ConvexHull(pts.astype(float))
    simp = pts[hull.simplices].astype(float)
    dets = np.rint(np.abs(np.linalg.det(simp))).astype(np.int64)
    diffs = simp[:, 1:, :] - simp[:, :1, :]
    minors = np.stack([np.rint(np.linalg.det(np.delete(diffs, c, axis=2))).astype(np.int64) for c in range(4)], axis=1)
    nvol3 = np.gcd.reduce(np.abs(minors), axis=1)
    keep = dets > 0
    count = int(mask.sum())
    half = Fraction(count - 1, 2)
    vol, g3 = Fraction(int(dets[keep].sum()), 24), Fraction(int(nvol3[keep].sum()), 12)
    pairs = sorted({min(i, NEG[i]) for i in np.flatnonzero(mask)[hull.vertices]})
    return (count, vol, g3, half - g3, half - vol), pairs


def main_walk():
    full = np.ones(len(DOUBLED), dtype=bool)
    coeffs, inner = ehrhart(LATT)
    assert inner == 1 and sum(coeffs) == len(DOUBLED), (coeffs, inner)
    frontier, total, ties = [canonical(full)], 0, []
    while frontier:
        nxt, lv1, lv2, level_g = set(), Fraction(-99), Fraction(-99), None
        for key in frontier:
            mask = unpack(key)
            (count, vol, g3, g1, g2), pairs = invariants(mask)
            level_g, lv1, lv2 = count, max(lv1, g1), max(lv2, g2)
            if g1 >= 8 and count < len(DOUBLED):
                ties.append((count, str(g1), np.flatnonzero(mask).tolist()))
            for rep in pairs:
                child = mask.copy()
                child[rep] = child[NEG[rep]] = False
                if np.linalg.matrix_rank(LATT[child].astype(float)) == 4:
                    nxt.add(canonical(child))
        total += len(frontier)
        print(f"G={level_g}: classes {len(frontier)} (total {total}); max g1 {lv1} = {float(lv1):.4f}, max g2 {lv2} = {float(lv2):.4f}",
              flush=True)
        frontier = list(nxt)
    print("sub-polytopes of T with g1 >= 8 (other than T):", len(ties))
    for row in ties[:10]:
        print("  ", row)


if __name__ == "__main__":
    main_walk()
