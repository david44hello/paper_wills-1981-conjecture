#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# ehrhart_probe.py - exact Ehrhart coefficients of centrally symmetric lattice polytopes
## version 0.11 - 20261102 - the version used for the runs reported in the paper
"""Exact Ehrhart polynomial of P = conv(S), S = -S a set of lattice points, via
counting L(k) = #(kP cap Z^n) and I(k) = #(int kP cap Z^n) for k = 1..K and Ehrhart-Macdonald
reciprocity L(-k) = (-1)^n I(k); then exact Lagrange interpolation over Fractions.
Facets: Qhull (floating) gives candidate facets; each is re-derived EXACTLY as an integer normal
from its incident points (sympy nullspace) and verified exactly on all points of S."""
import argparse
import itertools
import random
import sys
from fractions import Fraction
from math import comb

import numpy as np
import sympy
from scipy.spatial import ConvexHull


def exact_facets(points):
    """Return list of (a, b) integer facet inequalities a.x <= b for conv(points); points int ndarray."""
    hull = ConvexHull(points.astype(float))
    facets = set()
    for eq in hull.equations:
        normal, offset = eq[:-1], -eq[-1]
        incident = points[np.abs(points @ normal - offset) < 1e-7]
        diffs = sympy.Matrix((incident[1:] - incident[0]).tolist())
        null = diffs.nullspace()
        if len(null) != 1:
            raise RuntimeError("facet normal not unique")
        vec = null[0]
        lcm = sympy.ilcm(*[sympy.fraction(c)[1] for c in vec])
        ivec = [int(c * lcm) for c in vec]
        gcd = int(np.gcd.reduce(np.abs(ivec)))
        ivec = [c // gcd for c in ivec]
        if np.dot(ivec, normal) < 0:
            ivec = [-c for c in ivec]
        bval = int(np.dot(ivec, incident[0]))
        facets.add((tuple(ivec), bval))
    normals = np.array([f[0] for f in facets], dtype=np.int64)
    offsets = np.array([f[1] for f in facets], dtype=np.int64)
    vals = points @ normals.T
    if np.any(vals > offsets):
        raise RuntimeError("exact facet check failed")
    return normals, offsets


def box_points(dim, radius):
    """All integer points of [-radius, radius]^dim as an int64 array."""
    axis = np.arange(-radius, radius + 1, dtype=np.int64)
    grid = np.stack(np.meshgrid(*([axis] * dim), indexing="ij"), axis=-1)
    return grid.reshape(-1, dim)


def counts(normals, offsets, dim, kmax, radius):
    """L(k), I(k) for k = 1..kmax; P must lie in [-radius, radius]^dim."""
    lattice = box_points(dim, radius * kmax)
    vals = lattice @ normals.T
    out = []
    for k in range(1, kmax + 1):
        inside = np.all(vals <= k * offsets, axis=1)
        strict = np.all(vals < k * offsets, axis=1)
        out.append((int(inside.sum()), int(strict.sum())))
    return out


def interpolate(xs, ys):
    """Exact coefficients (low to high) of the polynomial through (xs, ys)."""
    size = len(xs)
    mat = sympy.Matrix([[sympy.Integer(x) ** j for j in range(size)] for x in xs])
    sol = mat.LUsolve(sympy.Matrix(ys))
    return [Fraction(int(sympy.fraction(c)[0]), int(sympy.fraction(c)[1])) for c in sol]


def ehrhart(points):
    """Exact Ehrhart coefficients g_0..g_n of conv(points), plus #interior lattice points."""
    dim = points.shape[1]
    radius = int(np.abs(points).max())
    normals, offsets = exact_facets(points)
    kmax = (dim + 1) // 2 if dim % 2 else dim // 2
    kmax = max(kmax, (dim + 1) // 2)
    data = counts(normals, offsets, dim, kmax, radius)
    xs, ys = [0], [1]
    for k, (lat, inner) in enumerate(data, start=1):
        xs += [k, -k]
        ys += [lat, (-1) ** dim * inner]
    coeffs = interpolate(xs, ys)
    if any(coeffs[dim + 1:]):
        raise RuntimeError("interpolation consistency check failed (degree > n)")
    return coeffs[:dim + 1], data[0][1]


def cube_coeffs(dim):
    return [Fraction(2 ** i * comb(dim, i)) for i in range(dim + 1)]


def random_symmetric_set(dim, rng, density):
    cube = [p for p in itertools.product((-1, 0, 1), repeat=dim) if any(p)]
    half = [p for p in cube if next(c for c in p if c) > 0]
    chosen = [p for p in half if rng.random() < density]
    pts = chosen + [tuple(-c for c in p) for p in chosen] + [tuple([0] * dim)]
    return np.array(pts, dtype=np.int64)


def main_probe(dim, trials, seed):
    rng = random.Random(seed)
    cube = cube_coeffs(dim)
    best = [Fraction(-10 ** 9)] * (dim + 1)
    best_poly = [None] * (dim + 1)
    for _ in range(trials):
        pts = random_symmetric_set(dim, rng, rng.uniform(0.15, 0.9))
        if np.linalg.matrix_rank(pts) < dim:
            continue
        coeffs, interior = ehrhart(pts)
        if interior != 1:
            raise RuntimeError("polytope inside cube with extra interior point?")
        for i in range(dim + 1):
            ratio = coeffs[i] / cube[i]
            if ratio > best[i]:
                best[i] = ratio
                best_poly[i] = (len(pts), [str(c) for c in coeffs])
                if ratio > 1:
                    print("VIOLATION", i, coeffs, pts.tolist(), flush=True)
    print("dim", dim, "max g_i / g_i(cube):", [f"{float(b):.4f}" for b in best])
    for i in range(1, dim - 1):
        print("  best for g_%d: G=%d coeffs=%s" % (i, best_poly[i][0], best_poly[i][1]))


def self_test():
    for dim in (2, 3, 4):
        pts = np.array(list(itertools.product((-1, 0, 1), repeat=dim)), dtype=np.int64)
        coeffs, interior = ehrhart(pts)
        assert coeffs == cube_coeffs(dim) and interior == 1, (dim, coeffs)
    cross4 = np.array([v for i in range(4) for v in (np.eye(4, dtype=int)[i], -np.eye(4, dtype=int)[i])] + [[0] * 4])
    coeffs, _ = ehrhart(cross4)
    assert coeffs == [1, Fraction(8, 3), Fraction(10, 3), Fraction(4, 3), Fraction(2, 3)], coeffs
    print("self-test OK")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--dim", type=int)
    parser.add_argument("--trials", type=int)
    parser.add_argument("--seed", type=int)
    args = parser.parse_args()
    if args.test:
        self_test()
        return
    main_probe(args.dim, args.trials, args.seed)


if __name__ == "__main__":
    main()
