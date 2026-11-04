#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# search_cube.py - counterexample search for Wills' conjecture among symmetric polytopes inside [-1,1]^n
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# Every full-dimensional 0-symmetric P with vertices in {-1,0,1}^n meets Wills' hypothesis (int P is inside (-1,1)^n).
# Objective: the best ratio g_i(P)/g_i(C_n) over the OPEN indices i = 1..n-2 (g_{n-1}: Wills; g_n: Minkowski).
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 search_cube.py --dim 5 --seconds 120 --seed 1
import argparse
import itertools
import random
import time

import numpy as np

from ehrhart_exact import cube_coeffs, ehrhart


def antipodal_pairs(dim):
    """One representative of each pair {v, -v}, v in {-1,0,1}^n minus 0 (first nonzero coordinate positive)."""
    reps = []
    for vec in itertools.product([-1, 0, 1], repeat=dim):
        nonzero = [c for c in vec if c != 0]
        if nonzero and nonzero[0] > 0:
            reps.append(vec)
    return reps


def vertices_from(chosen, reps):
    rows = []
    for idx in chosen:
        rows.append(reps[idx])
        rows.append(tuple(-c for c in reps[idx]))
    return rows


def score(chosen, reps, dim):
    """(best open ratio, its index, coefficients) or None if P is not full-dimensional."""
    rows = vertices_from(chosen, reps)
    if np.linalg.matrix_rank(np.array(rows, dtype=float)) < dim:
        return None
    try:
        coeffs, inner = ehrhart(rows)
    except Exception:  # qhull precision trouble: report loudly, never silently accept
        print("WARN: hull failure on", sorted(chosen), flush=True)
        return None
    assert inner == 1, "hypothesis broken: P inside the cube must have only 0 inside"
    cube = cube_coeffs(dim)
    ratios = [(coeffs[i] / cube[i], i) for i in range(1, dim - 1)]
    best_ratio, best_i = max(ratios)
    return float(best_ratio), best_i, coeffs


def hill_climb(dim, seconds, seed, objective_index):
    """Toggle one antipodal pair at a time; keep the move if the chosen ratio does not drop (plateau moves allowed)."""
    rng = random.Random(seed)
    reps = antipodal_pairs(dim)
    cube = cube_coeffs(dim)
    chosen = {idx for idx in range(len(reps)) if rng.random() < 0.3}
    current = None
    best_seen = (0.0, None, None)
    deadline = time.time() + seconds
    evaluated = 0
    while time.time() < deadline:
        trial = set(chosen)
        trial ^= {rng.randrange(len(reps))}
        result = score(trial, reps, dim)
        evaluated += 1
        if result is None:
            continue
        coeffs = result[2]
        value = float(coeffs[objective_index] / cube[objective_index])
        if current is None or value >= current or rng.random() < 0.02:
            chosen, current = trial, value
            if value > best_seen[0]:
                best_seen = (value, sorted(trial), coeffs)
    return best_seen, evaluated, reps


def main_search(dim, seconds, seed, objective_index):
    (value, chosen, coeffs), evaluated, reps = hill_climb(dim, seconds, seed, objective_index)
    print(f"dim={dim} seed={seed} objective=g_{objective_index} evaluated={evaluated} best ratio={value:.5f}")
    if chosen is not None:
        print("  g =", " ".join(str(c) for c in coeffs))
        print("  vertex pairs:", [reps[i] for i in chosen])


def main():
    parser = argparse.ArgumentParser(description="Wills counterexample search inside the cube")
    parser.add_argument("--dim", type=int, required=True)
    parser.add_argument("--seconds", type=float, required=True)
    parser.add_argument("--seed", type=int, required=True)
    parser.add_argument("--index", type=int, required=True, help="which g_i ratio to climb on (1..n-2)")
    args = parser.parse_args()
    main_search(args.dim, args.seconds, args.seed, args.index)


if __name__ == "__main__":
    main()
