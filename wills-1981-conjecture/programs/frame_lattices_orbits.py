#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# frame_lattices_orbits.py - frame lattices, second program: the list up to signed permutations, written to frame_lattices.json
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# Uses frame_lattices_second for the HNF enumeration and the coset (W_4) test.
# L <-> (D, its coset set C = L/Z^4 as integer vectors y mod D, c = y/D). Signed permutations act on C coordinate-wise
# (permute coordinates; y_i -> -y_i mod D). Orbit key = min over the 384 images of the sorted coset tuple.
# |L cap [-1,1]^4| = sum over cosets of prod_i (3 if y_i == 0 else 2)  (values t = y_i/D mod 1 in [-1,1]).
# For each orbit: g_1 of the cross-polytope conv(+-e_i) w.r.t. L (= g_1 of conv(+-rows of H) in Z^4).
import itertools
import json
import sys
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import frame_lattices_second as cps  # noqa: E402
import ehrhart_count as ehr  # noqa: E402

SIGNED_PERMS = [(sigma, signs) for sigma in itertools.permutations(range(4))
                for signs in itertools.product((1, -1), repeat=4)]


def coset_set(mat):
    det = mat[0][0] * mat[1][1] * mat[2][2] * mat[3][3]
    inv = cps.inverse_rows(mat)
    gens = [tuple(int(xx * det) % det for xx in row) for row in inv]
    elems = {(0, 0, 0, 0)}
    frontier = [(0, 0, 0, 0)]
    while frontier:
        new = []
        for ee in frontier:
            for gg in gens:
                ss = tuple((aa + bb) % det for aa, bb in zip(ee, gg))
                if ss not in elems:
                    elems.add(ss)
                    new.append(ss)
        frontier = new
    return det, elems


def orbit_key(det, elems):
    best = None
    for sigma, signs in SIGNED_PERMS:
        img = tuple(sorted(tuple((signs[jj] * ee[sigma[jj]]) % det for jj in range(4)) for ee in elems))
        if best is None or img < best:
            best = img
    return (det, best)


def box_points(det, elems):
    return sum(eval_prod(ee) for ee in elems)


def eval_prod(ee):
    out = 1
    for yy in ee:
        out *= 3 if yy == 0 else 2
    return out


def main():
    orbits = {}
    per_det = defaultdict(lambda: [0, 0])
    for det in range(1, 24):
        for mat in cps.column_hnfs(det):
            if not cps.in_w4_by_cosets(mat):
                continue
            dd, elems = coset_set(mat)
            key = orbit_key(dd, elems)
            per_det[det][0] += 1
            if key not in orbits:
                verts = [tuple(row) for row in mat] + [tuple(-xx for xx in row) for row in mat]
                g1 = ehr.main_ehrhart(verts, extra=1)[0][1]
                orbits[key] = {"D": det, "H": mat, "box_points": box_points(dd, elems), "g1_cross": str(g1), "size": 0}
                per_det[det][1] += 1
            orbits[key]["size"] += 1
    total_l = sum(vv[0] for vv in per_det.values())
    print(f"lattices with (ii): {total_l}; orbits under signed permutations: {len(orbits)}")
    for det in sorted(per_det):
        reps = [oo for oo in orbits.values() if oo["D"] == det]
        print(f"D = {det:2d}: lattices {per_det[det][0]:4d}, orbits {per_det[det][1]:3d}, |L cap [-1,1]^4| max "
              f"{max(oo['box_points'] for oo in reps)}, min {min(oo['box_points'] for oo in reps)}; "
              f"max g_1(cross) {max(oo['g1_cross'] for oo in reps)}")
    Path("frame_lattices.json").write_text(
        json.dumps(sorted(orbits.values(), key=lambda oo: (oo["D"], -oo["box_points"])), indent=1))
    print("orbit list written: frame_lattices.json")


if __name__ == "__main__":
    main()
