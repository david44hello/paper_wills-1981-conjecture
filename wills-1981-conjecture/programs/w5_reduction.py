#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# w5_reduction.py - greedy reduction: drop vertex pairs of W_5 while g_1 > 10 holds; prints the final set W
## version 0.10 - 20261102 - the version used for the runs reported in the paper
import numpy as np
from fractions import Fraction
from ehrhart_exact import ehrhart


def load():
    verts = [tuple(int(c) for c in line.split()) for line in open("witness_n5_vertices.txt")]
    return sorted({v for v in verts if v > tuple(-c for c in v)})


def g1_of(pairs):
    rows = list(pairs) + [tuple(-c for c in p) for p in pairs]
    if np.linalg.matrix_rank(np.array(rows, dtype=float)) < 5:
        return None, None
    coeffs, inner = ehrhart(rows)
    assert inner == 1
    return coeffs[1], coeffs


def main_shrink():
    pairs = load()
    value, coeffs = g1_of(pairs)
    print("start:", len(pairs), "pairs, g_1 =", value)
    improved = True
    while improved:
        improved = False
        best = None
        for p in pairs:
            trial = [q for q in pairs if q != p]
            val, cf = g1_of(trial)
            if val is not None and val > 10 and (best is None or val > best[0]):
                best = (val, trial, cf)
        if best:
            value, pairs, coeffs = best
            improved = True
            print(f"  {len(pairs)} pairs, g_1 = {value} = {float(value):.5f}", flush=True)
    print("MINIMAL (no single pair can be dropped):", len(pairs), "pairs; g =", [str(c) for c in coeffs])
    for p in pairs:
        print("  +-", p)
    with open("witness_n5_min_pairs.txt", "w") as out:
        for p in pairs:
            out.write(" ".join(map(str, p)) + "\n")


if __name__ == "__main__":
    main_shrink()
