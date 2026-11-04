#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# maximal_members.py - inclusion-maximal members of W_n by greedy augmentation from random seeds
## version 0.20 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# A Q is reported MAXIMAL(R') when no primitive p in [-R',R']^n can be added. Records vol, G, g_1 for each maximal Q found.
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 maximal_members.py --dim 3 --radius 2 --seeds 20 --seed 1
import argparse
import itertools
import math
import random
from fractions import Fraction

import numpy as np

from ehrhart_exact import facets_of, ehrhart


def lattice_points_and_interior(pts):
    """(all lattice points of conv(pts), number of interior lattice points); pts integer rows, full-dimensional."""
    normals, rhs = facets_of(pts)
    dim = pts.shape[1]
    radius = int(np.abs(pts).max())
    span = np.arange(-radius, radius + 1)
    box = np.array(list(itertools.product(span, repeat=dim)), dtype=np.int64)
    values = box @ normals.T
    closed = np.all(values <= rhs, axis=1)
    interior = np.all(values < rhs, axis=1)
    return box[closed], int(interior.sum())


def primitive_reps(dim, radius):
    reps = []
    for vec in itertools.product(range(-radius, radius + 1), repeat=dim):
        nonzero = [c for c in vec if c != 0]
        if nonzero and nonzero[0] > 0 and math.gcd(*[abs(c) for c in vec]) == 1:
            reps.append(np.array(vec, dtype=np.int64))
    return reps


def try_add(current, vec):
    """Lattice points of conv(current + {+-vec}) if it stays in W_n, else None."""
    trial = np.vstack([current, vec, -vec])
    points, inner = lattice_points_and_interior(trial)
    return points if inner == 1 else None


def augment(start, reps, rng):
    current = start
    changed = True
    while changed:
        changed = False
        order = list(range(len(reps)))
        rng.shuffle(order)
        present = {tuple(p) for p in current}
        for idx in order:
            if tuple(reps[idx]) in present:
                continue
            grown = try_add(current, reps[idx])
            if grown is not None:
                current, changed = grown, True
                present = {tuple(p) for p in current}
    return current


def is_maximal(current, reps):
    present = {tuple(p) for p in current}
    return all(tuple(v) in present or try_add(current, v) is None for v in reps)


def random_seed(dim, rng):
    """A random valid cross-polytope conv{+-v_i} with small entries."""
    while True:
        basis = np.array([[rng.randint(-1, 1) for _ in range(dim)] for _ in range(dim)], dtype=np.int64)
        basis += np.eye(dim, dtype=np.int64) * rng.choice([0, 1])
        if round(abs(np.linalg.det(basis.astype(float)))) == 0:
            continue
        pts = np.vstack([basis, -basis])
        points, inner = lattice_points_and_interior(pts)
        if inner == 1:
            return points


def l6_case(current):
    """L6 case from M(Q) = integer u with |u.x| <= 1 on Q: I (M has a basis), II (rank 4, no basis), III (rank 1-3), IV."""
    normals, rhs = facets_of(current)
    dual_vertices = normals / rhs[:, None]
    bound = int(np.ceil(np.abs(dual_vertices).max()))
    dim = current.shape[1]
    box = np.array(list(itertools.product(range(-bound, bound + 1), repeat=dim)), dtype=np.int64)
    inside = np.all(np.abs(box @ current.T) <= 1, axis=1)
    members = box[inside]
    members = members[np.any(members != 0, axis=1)]
    if len(members) == 0:
        return "IV", 0
    rank = np.linalg.matrix_rank(members.astype(float))
    if rank < dim:
        return "III", rank
    for combo in itertools.combinations(range(len(members)), dim):
        if round(abs(np.linalg.det(members[list(combo)].astype(float)))) == 1:
            return "I", rank
    return "II", rank


def describe(current):
    coeffs, inner = ehrhart(current)
    assert inner == 1
    dim = current.shape[1]
    return coeffs, coeffs[dim] == 2 ** dim


def main_search(dim, radius, seeds, seed):
    rng = random.Random(seed)
    reps_by_r = {r: primitive_reps(dim, r) for r in range(radius, 5)}
    found = {}
    for run in range(seeds):
        result, cur_r = random_seed(dim, rng), radius
        while True:
            result = augment(result, reps_by_r[cur_r], rng)
            if cur_r >= 4:
                maximal = False
                break
            maximal = is_maximal(result, reps_by_r[cur_r + 1])
            if maximal:
                break
            cur_r += 1
        coeffs, extremal = describe(result)
        case, rank = l6_case(result)
        key = tuple(coeffs)
        found.setdefault(key, [0, maximal, result, case])[0] += 1
        with open(f"maxel_dim{dim}_found.txt", "a") as log:
            log.write(f"{case} rankM={rank} maximal={maximal} G={len(result)} g={[str(c) for c in coeffs]} pts="
                      f"{result.tolist()}\n")
        print(f"run {run}: case {case} (rank M {rank}) G={len(result)} vol={coeffs[dim]} g1={coeffs[1]} maximal(R={cur_r + 1})={maximal} "
              f"vol=2^n:{extremal} g={[str(c) for c in coeffs]}", flush=True)
    print("DISTINCT Ehrhart polynomials of the maximal elements found:")
    for key, (count, maximal, result, case) in sorted(found.items(), key=lambda kv: -kv[1][0]):
        print(f"  x{count} case {case} maximal={maximal} G={len(result)} g={[str(c) for c in key]}")


def main():
    parser = argparse.ArgumentParser(description="maximal elements of W_n")
    parser.add_argument("--dim", type=int, required=True)
    parser.add_argument("--radius", type=int, required=True)
    parser.add_argument("--seeds", type=int, required=True)
    parser.add_argument("--seed", type=int, required=True)
    args = parser.parse_args()
    main_search(args.dim, args.radius, args.seeds, args.seed)


if __name__ == "__main__":
    main()
