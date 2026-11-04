#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# width2_survey.py - helpers for point sets in W_4: g_1, M(P) and the width-2 directions
## version 0.20 - 20261102 - the version used for the runs reported in the paper
# K_u = A_u  <=>  every midpoint (b - b')/2 (u.b = 1, u.b' = 1) lies in conv(A_u), A_u = {x in S : u.x = 0}.
# Membership in conv(A_u) is tested exactly with the facets of the 4-D pyramid conv(A_u u {apex}), u.apex = 1.
# Input: JSON lines with a key holding the full lattice point list of P (default key "points_wt", data/boxes.jsonl).
import argparse
import itertools
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ehrhart_count as ehr  # noqa: E402



def dot(aa, bb):
    return sum(xx * yy for xx, yy in zip(aa, bb))


def width2_directions(points):
    """All primitive u (one per +-pair) with |u.x| <= 1 on all points. Complete: for 4 independent points s_i of the
    set, every such u has u.s_i in {-1,0,1}, so u = S4^{-1} eps for one of the 81 sign vectors eps."""
    basis = []
    for pp in points:
        if ehr.rank_of([list(qq) for qq in basis + [pp]]) == len(basis) + 1:
            basis.append(pp)
        if len(basis) == 4:
            break
    assert len(basis) == 4, "point set must span R^4"
    out = set()
    for eps in itertools.product((-1, 0, 1), repeat=4):
        if not any(eps):
            continue
        sol = ehr.solve_exact([list(bb) for bb in basis], list(eps))
        if any(Fraction(xx).denominator != 1 for xx in sol):
            continue
        uu = tuple(int(xx) for xx in sol)
        if math.gcd(*uu) != 1 or not all(abs(dot(uu, pp)) <= 1 for pp in points):
            continue
        out.add(max(uu, tuple(-xx for xx in uu)))
    return sorted(out)


def k_equals_a(points, uu):
    """Exact test of K_u = A_u (None if A_u is not 3-dimensional)."""
    a_set = [pp for pp in points if dot(uu, pp) == 0]
    b_set = [pp for pp in points if dot(uu, pp) == 1]
    if ehr.rank_of([list(pp) for pp in a_set]) < 3:
        return None
    apex = b_set[0]
    rays = ehr.extreme_rays([tuple([1] + list(pp)) for pp in a_set + [apex]])
    facets = [(tuple(-cc for cc in ray[1:]), ray[0]) for ray in rays]      # normal.x <= height on the pyramid
    mids2 = [tuple(xx - yy for xx, yy in zip(bb, cc)) for bb in b_set for cc in b_set]   # = 2 * midpoint
    return all(dot(nn, mm) <= 2 * hh for mm in mids2 for nn, hh in facets)


def survey_one(points):
    coeffs = ehr.main_ehrhart([tuple(pp) for pp in points])[0]
    dirs = width2_directions(points)
    flags = [(uu, k_equals_a(points, uu)) for uu in dirs]
    return coeffs, flags


def main_survey(path, key):
    for num, line in enumerate(Path(path).read_text().splitlines()):
        rec = json.loads(line)
        points = [tuple(pp) for pp in rec[key]]
        assert ehr.rank_of([list(pp) for pp in points]) == 4
        coeffs, flags = survey_one(points)
        n_ka = sum(1 for _uu, ff in flags if ff)
        print(f"#{num} G={len(points)} g_1={coeffs[1]} g_2={coeffs[2]} vol={coeffs[4]} | width-2 dirs {len(flags)}: "
              f"K=A in {n_ka}; " + ", ".join(f"{uu}:{'A' if ff else ('-' if ff is None else 'half')}" for uu, ff in flags),
              flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True)
    parser.add_argument("--key", required=True)
    args = parser.parse_args()
    main_survey(args.input, args.key)


if __name__ == "__main__":
    main()
