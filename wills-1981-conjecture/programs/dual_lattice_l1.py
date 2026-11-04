#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# dual_lattice_l1.py - lattices L* of index D (16 <= D <= 24) with L* cap {-1,0,1}^4 = {0}; the minimum l1 norm on a dual lattice
## version 0.20 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
import itertools
from fractions import Fraction

import numpy as np

from case2_walk import hnf_lattices, members

SMALL = np.array([u for u in itertools.product([-1, 0, 1], repeat=4) if any(u)], dtype=np.int64)


def min_l1_dual(hmat, index):
    """Min l1 norm over nonzero vectors of L = H^{-T} Z^4 (L/Z^4 of order D): BFS closure of the 4 generators mod 1, scaled by D."""
    gens = np.rint(np.linalg.inv(hmat.astype(float)).T * index).astype(np.int64) % index  # columns = generators * D
    gens = [tuple(gens[:, j]) for j in range(4)]
    seen = {(0, 0, 0, 0)}
    frontier = [(0, 0, 0, 0)]
    while frontier:
        nxt = []
        for elem in frontier:
            for gen in gens:
                new = tuple((a + b) % index for a, b in zip(elem, gen))
                if new not in seen:
                    seen.add(new)
                    nxt.append(new)
        frontier = nxt
    best = Fraction(10 ** 9)
    for frac in seen:
        if any(frac):
            best = min(best, Fraction(sum(min(r, index - r) for r in frac), index))
    return best, len(seen)


def main_scan():
    for index in range(16, 25):
        total, case4, valid = 0, 0, []
        for hmat in hnf_lattices(index):
            total += 1
            if np.any(members(hmat, SMALL)):
                continue
            case4 += 1
            best, nreps = min_l1_dual(hmat, index)
            assert nreps == index
            if best >= 1:
                valid.append((hmat.tolist(), best))
        print(f"D={index}: sublattices {total}, with L* cap {{-1,0,1}}^4 = {{0}}: {case4}, ALSO cross-polytope in W_4: {len(valid)}"
              + (f"  e.g. {valid[0]}" if valid else ""), flush=True)


if __name__ == "__main__":
    main_scan()
