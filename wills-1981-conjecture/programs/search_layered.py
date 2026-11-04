#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# search_layered.py - search over layered polytopes conv{A x 0, B x {+1}, -B x {-1}} inside [-1,1]^n
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 search_layered.py --dim 6 --seconds 120 --seed 1 --index 1
import argparse
import itertools
import random
import time

import numpy as np

from ehrhart_exact import cube_coeffs, ehrhart, cube_vertices, cross_vertices
from search_cube import antipodal_pairs


def stack_rows(a_pairs, b_points, pair_reps, point_reps):
    rows = []
    for idx in a_pairs:
        rows.append(list(pair_reps[idx]) + [0])
        rows.append([-c for c in pair_reps[idx]] + [0])
    for idx in b_points:
        rows.append(list(point_reps[idx]) + [1])
        rows.append([-c for c in point_reps[idx]] + [-1])
    return rows


def evaluate(rows, dim, index):
    if np.linalg.matrix_rank(np.array(rows, dtype=float)) < dim:
        return None
    coeffs, inner = ehrhart(rows)
    assert inner == 1
    return float(coeffs[index] / cube_coeffs(dim)[index]), coeffs


def climb(dim, seconds, seed, index):
    rng = random.Random(seed)
    m = dim - 1
    pair_reps = antipodal_pairs(m)
    point_reps = list(itertools.product([-1, 0, 1], repeat=m))
    a_pairs = {pair_reps.index(v) for v in pair_reps if all(abs(c) == 1 for c in v)}  # start: A = cube
    b_points = {point_reps.index(tuple(v)) for v in cross_vertices(m)}  # start: B = cross-polytope (Henze P_n)
    current, coeffs = evaluate(stack_rows(a_pairs, b_points, pair_reps, point_reps), dim, index)
    best = (current, sorted(a_pairs), sorted(b_points), coeffs)
    deadline = time.time() + seconds
    evaluated = 1
    while time.time() < deadline:
        new_a, new_b = set(a_pairs), set(b_points)
        if rng.random() < 0.75:
            new_b ^= {rng.randrange(len(point_reps))}
        else:
            new_a ^= {rng.randrange(len(pair_reps))}
        result = evaluate(stack_rows(new_a, new_b, pair_reps, point_reps), dim, index)
        evaluated += 1
        if result is None:
            continue
        value, trial_coeffs = result
        if value >= current or rng.random() < 0.03:
            a_pairs, b_points, current = new_a, new_b, value
            if value > best[0]:
                best = (value, sorted(new_a), sorted(new_b), trial_coeffs)
    return best, evaluated, pair_reps, point_reps


def main():
    parser = argparse.ArgumentParser(description="layered Wills search")
    parser.add_argument("--dim", type=int, required=True)
    parser.add_argument("--seconds", type=float, required=True)
    parser.add_argument("--seed", type=int, required=True)
    parser.add_argument("--index", type=int, required=True)
    args = parser.parse_args()
    (value, a_set, b_set, coeffs), evaluated, pair_reps, point_reps = climb(args.dim, args.seconds, args.seed, args.index)
    print(f"dim={args.dim} seed={args.seed} g_{args.index} evaluated={evaluated} best ratio={value:.5f}")
    print("  g =", " ".join(str(c) for c in coeffs))
    print("  A pairs:", [pair_reps[i] for i in a_set])
    print("  B points:", [point_reps[i] for i in b_set])


if __name__ == "__main__":
    main()
