#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# frame_lattices_first.py - frame lattices, first program: all lattice cross-polytopes conv{+-v_i} in W_4 (rows of a column HNF H, det H <= 24)
## version 0.10 - 20261102 - the version used for the runs reported in the paper
import sys
from fractions import Fraction

import numpy as np

from dual_lattice_l1 import min_l1_dual
from case2_walk import hnf_lattices
from maximal_members import lattice_points_and_interior, l6_case
from generic_walk import invariants


def main_scan(max_index):
    overall = []
    for index in range(1, max_index + 1):
        valid, best1, best2, arg = 0, Fraction(-99), Fraction(-99), None
        for hmat in hnf_lattices(index):
            best, _ = min_l1_dual(hmat, index)
            if best < 1:
                continue
            valid += 1
            verts = np.vstack([hmat, -hmat])
            pts, inner = lattice_points_and_interior(verts)
            assert inner == 1
            (count, vol, g3, g1, g2), _ = invariants(pts, np.ones(len(pts), dtype=bool))
            if g1 > best1:
                best1, arg = g1, (hmat.tolist(), count, vol, g2)
            best2 = max(best2, g2)
            if g1 >= 8 or g2 >= 24:
                print(f"  D={index} FLAG g1={g1} g2={g2} G={count} vol={vol} case={l6_case(pts)} H={hmat.tolist()}", flush=True)
        print(f"D={index:2d}: W_4 cross-polytopes {valid:6d}; max g1 = {best1} ({float(best1):.3f}), max g2 = {best2}; argmax {arg}",
              flush=True)


if __name__ == "__main__":
    main_scan(int(sys.argv[1]))
