#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# cell24_coords.py - the 24-cell conv{+-e_i +- e_j} in the lattice Z^4 + Z(1/2,1/2,1/2,1/2), in Z^4 coordinates
## version 0.10 - 20261102 - the version used for the runs reported in the paper
import itertools
from fractions import Fraction
import numpy as np
from ehrhart_exact import ehrhart, cube_coeffs

BASIS = np.array([[1, 0, 0, Fraction(1, 2)], [0, 1, 0, Fraction(1, 2)], [0, 0, 1, Fraction(1, 2)], [0, 0, 0, Fraction(1, 2)]],
                 dtype=object)  # columns e1, e2, e3, h


def to_lattice_coords(c):
    """Solve BASIS x = c exactly (c in L) -> integer x."""
    x4 = Fraction(c[3]) * 2
    xs = [Fraction(c[i]) - x4 / 2 for i in range(3)] + [x4]
    assert all(v.denominator == 1 for v in xs), c
    return tuple(int(v) for v in xs)


def cell24_vertices():
    verts = []
    for i, j in itertools.combinations(range(4), 2):
        for si, sj in itertools.product([1, -1], repeat=2):
            c = [0, 0, 0, 0]
            c[i], c[j] = si, sj
            verts.append(to_lattice_coords(c))
    return verts


if __name__ == "__main__":
    verts = cell24_vertices()
    coeffs, inner = ehrhart(verts)
    cube = cube_coeffs(4)
    print("24-cell in L: interior lattice points =", inner, " G =", sum(coeffs))
    print("g =", [str(c) for c in coeffs], " ratios:", [f"{float(coeffs[i] / cube[i]):.3f}" for i in range(1, 4)])
