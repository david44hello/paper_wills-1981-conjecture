#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# ehrhart_exact.py - exact Ehrhart polynomial of a full-dimensional lattice polytope given by its vertices
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# Written independently of ehrhart_probe.py (not read, by design).
# Method: L(k) = #(kP cap Z^n) for k = 1..K, L(0) = 1, L(-k) = (-1)^n #(int(kP) cap Z^n); interpolate exactly with Fractions.
# Run single-threaded: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 ehrhart_exact.py --test
import argparse
import itertools
import math
import sys
from fractions import Fraction

import numpy as np
from scipy.spatial import ConvexHull


def integer_normal(points):
    """Integer normal of the hyperplane through n affinely independent integer points (rows)."""
    diffs = (points[1:] - points[0]).astype(float)
    dim = points.shape[1]
    normal = []
    for col in range(dim):
        minor = np.delete(diffs, col, axis=1)
        det = np.linalg.det(minor) if minor.size else 1.0
        rounded = round(det)
        assert abs(det - rounded) < 1e-6, f"non-integer minor {det}"
        normal.append(((-1) ** col) * int(rounded))
    common = 0
    for entry in normal:
        common = math.gcd(common, abs(entry))
    if common == 0:
        return None  # qhull 'Qt' may emit zero-volume simplices; the caller skips them
    return tuple(entry // common for entry in normal)


def facets_of(vertices):
    """Exact facet inequalities (a, b) with a.x <= b for the hull of integer vertices; asserts 0 is interior."""
    verts = np.asarray(vertices, dtype=np.int64)
    hull = ConvexHull(verts.astype(float))
    found = {}
    for simplex in hull.simplices:
        exact = integer_normal(verts[simplex])
        if exact is None:
            continue
        normal = np.array(exact, dtype=np.int64)
        rhs = int(normal @ verts[simplex[0]])
        if rhs < 0:
            normal, rhs = -normal, -rhs
        assert rhs > 0, "origin on a facet hyperplane: 0 is not interior"
        found[tuple(normal)] = rhs
    normals = np.array(list(found.keys()), dtype=np.int64)
    rhs_vec = np.array(list(found.values()), dtype=np.int64)
    assert np.all(verts @ normals.T <= rhs_vec), "a vertex violates a facet: hull is wrong"
    qhull_facets = {tuple(np.round(eq / np.linalg.norm(eq[:-1]), 6)) for eq in hull.equations}
    assert len(qhull_facets) == len(found), f"facet count mismatch: qhull {len(qhull_facets)} vs exact {len(found)}"
    tight = (verts @ normals.T == rhs_vec).sum(axis=0)
    assert np.all(tight >= verts.shape[1]), "an inequality is not a facet"
    return normals, rhs_vec


def count_points(normals, rhs_vec, scale, radius):
    """(closed count, interior count) of lattice points in scale*P, P inside [-radius, radius]^n."""
    dim = normals.shape[1]
    span = np.arange(-radius * scale, radius * scale + 1, dtype=np.int64)
    closed_total = 0
    interior_total = 0
    tail_dim = dim
    while tail_dim > 1 and len(span) ** tail_dim > 60000:
        tail_dim -= 1
    tail = np.array(list(itertools.product(span, repeat=tail_dim)), dtype=np.int64).reshape(-1, tail_dim)
    tail_values = tail @ normals[:, dim - tail_dim:].T
    bound = scale * rhs_vec
    for head in itertools.product(span, repeat=dim - tail_dim):
        head_value = np.array(head, dtype=np.int64) @ normals[:, :dim - tail_dim].T if head else 0
        values = tail_values + head_value
        closed_total += int(np.count_nonzero(np.all(values <= bound, axis=1)))
        interior_total += int(np.count_nonzero(np.all(values < bound, axis=1)))
    return closed_total, interior_total


def interpolate(nodes, values):
    """Exact coefficients (low to high) of the interpolating polynomial through (nodes, values)."""
    size = len(nodes)
    coeffs = [Fraction(0)] * size
    for idx, (x_i, y_i) in enumerate(zip(nodes, values)):
        basis = [Fraction(1)]
        denom = Fraction(1)
        for jdx, x_j in enumerate(nodes):
            if jdx == idx:
                continue
            basis = [Fraction(0)] + basis
            for pos in range(len(basis) - 1):
                basis[pos] -= x_j * basis[pos + 1]
            denom *= (x_i - x_j)
        for pos in range(size):
            coeffs[pos] += Fraction(y_i) * basis[pos] / denom
    return coeffs


def ehrhart(vertices, extra_check=None):
    """Exact Ehrhart coefficients g_0..g_n, plus the interior count of P itself (hypothesis: must be 1)."""
    verts = np.asarray(vertices, dtype=np.int64)
    dim = verts.shape[1]
    normals, rhs_vec = facets_of(verts)
    radius = int(np.abs(verts).max())
    if extra_check is None:
        extra_check = dim <= 6
    top = math.ceil(dim / 2) + (1 if extra_check else 0)
    nodes, values = [0], [1]
    interior_of_p = None
    for scale in range(1, top + 1):
        closed, interior = count_points(normals, rhs_vec, scale, radius)
        if scale == 1:
            interior_of_p = interior
        nodes += [scale, -scale]
        values += [closed, (-1) ** dim * interior]
    coeffs = interpolate(nodes, values)
    assert all(c == 0 for c in coeffs[dim + 1:]), f"interpolation inconsistent: {coeffs[dim + 1:]}"
    return coeffs[:dim + 1], interior_of_p


def cube_vertices(dim):
    return list(itertools.product([-1, 1], repeat=dim))


def cross_vertices(dim):
    rows = []
    for axis in range(dim):
        for sign in (1, -1):
            row = [0] * dim
            row[axis] = sign
            rows.append(row)
    return rows


def cube_coeffs(dim):
    return [Fraction(2 ** i * math.comb(dim, i)) for i in range(dim + 1)]


def stack(bottom, top_layer, height=1):
    """conv{A x {0}, B x {+height}, -B x {-height}}: vertices of the layered polytope."""
    rows = [list(v) + [0] for v in bottom]
    rows += [list(v) + [height] for v in top_layer]
    rows += [[-c for c in v] + [-height] for v in top_layer]
    return rows


def run_tests():
    for dim in range(2, 6):
        coeffs, inner = ehrhart(cube_vertices(dim))
        assert coeffs == cube_coeffs(dim) and inner == 1, (dim, coeffs)
    for dim in range(2, 6):
        coeffs, inner = ehrhart(cross_vertices(dim))
        expected = [Fraction(0)] * (dim + 1)
        # L(k) = sum_i 2^i C(n,i) C(k,i) for the cross-polytope
        poly = [Fraction(0)] * (dim + 1)
        for i in range(dim + 1):
            falling = [Fraction(1)]
            for j in range(i):
                falling = [Fraction(0)] + falling
                for pos in range(len(falling) - 1):
                    falling[pos] -= j * falling[pos + 1]
            for pos, val in enumerate(falling):
                poly[pos] += Fraction(2 ** i * math.comb(dim, i)) * val / math.factorial(i)
        expected = poly
        assert coeffs == expected and inner == 1, (dim, coeffs, expected)
    q5 = stack(cube_vertices(4), [[0, 0, 0, 0]])
    coeffs, inner = ehrhart(q5)
    assert coeffs[1] == Fraction(134, 15), coeffs  # Henze Thm 2.1(ii): 2(n-1) + (4-2^n) B_{n-1}, n = 5
    print("self-tests passed: cubes n=2..5, cross-polytopes n=2..5, Henze Q_5 g_1 = 134/15")


def report(name, vertices):
    coeffs, inner = ehrhart(vertices)
    dim = len(coeffs) - 1
    ratios = [float(coeffs[i] / cube_coeffs(dim)[i]) for i in range(1, dim)]
    print(f"{name}: interior={inner} g=" + " ".join(str(c) for c in coeffs)
          + " | g_i/g_i(C), i=1..n-1: " + " ".join(f"{r:.4f}" for r in ratios))
    return coeffs


def main():
    parser = argparse.ArgumentParser(description="exact Ehrhart polynomials")
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--p7", action="store_true", help="Henze P_7 check (n = 7, slower)")
    args = parser.parse_args()
    if args.test:
        run_tests()
    if args.p7:
        report("P7", stack(cube_vertices(6), cross_vertices(6)))


if __name__ == "__main__":
    main()
