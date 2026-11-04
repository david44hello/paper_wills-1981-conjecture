#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# w_ehrhart_check.py - exact Ehrhart check of W, W_5, W_5 x [-1,1], T and X: facets from all n-subsets of vertices, direct counts
## version 0.10 - 20261103 - the version used for the runs reported in the paper
#
# Method (all exact except one float step that is re-verified exactly):
#   facets   : every facet of a full-dimensional polytope in R^n contains n affinely independent vertices, so trying
#              every n-subset of the vertices finds ALL facet hyperplanes (normal = generalized cross product of the
#              n-1 difference vectors; the 4x4 / 3x3 minors are tiny integers, computed in float and rounded, then
#              every kept facet is re-verified in exact Python integers). Cross-check: qhull (scipy) facet count.
#   vertices : a point is a vertex iff the normals of the facets through it have rank n (exact, fractions).
#   L_P(k)   : direct count of lattice points of kP in its bounding box, for k = 0 .. n+1; the polynomial is
#              interpolated EXACTLY from k = 0 .. n, and k = n+1 must match it (consistency check).
#   interior : #int(kP cap Z^n) by strict inequalities; reciprocity L_P(-k) = (-1)^n #int(kP) checked for k = 1, 2.
# Usage: w_ehrhart_check.py --all   (prints a report)   |   w_ehrhart_check.py --test
import argparse
import itertools
import sys
from fractions import Fraction
from math import gcd
from pathlib import Path

import os

os.environ.setdefault("OMP_NUM_THREADS", "1")  # one thread
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import numpy as np  # noqa: E402 (after the thread pins)

W5_FILE = Path(str(Path(__file__).resolve().parent.parent / "data" / "w5_vertices.txt"))
W5MIN_FILE = Path(str(Path(__file__).resolve().parent.parent / "data" / "w_pairs.txt"))
CHUNK = 200_000


def read_points(path):
    """Integer points, one per line; '#' comments and blank lines ignored."""
    rows = []
    for line in path.read_text().splitlines():
        line = line.split("#")[0].strip()
        if line:
            rows.append(tuple(int(tok) for tok in line.replace(",", " ").split()))
    return rows


def primitive(normal, offset):
    """Divide (normal, offset) by the gcd of all entries."""
    common = 0
    for val in list(normal) + [offset]:
        common = gcd(common, abs(int(val)))
    return tuple(int(val) // common for val in normal), int(offset) // common


def subset_normals(diffs):
    """Generalized cross product of the n-1 rows of each (n-1) x n matrix in diffs -> (m, n) rounded normals."""
    count, rows, dim = diffs.shape
    normals = np.empty((count, dim), dtype=np.int64)
    for col in range(dim):
        minor = np.delete(diffs, col, axis=2).astype(np.float64)
        normals[:, col] = ((-1) ** col) * np.rint(np.linalg.det(minor)).astype(np.int64)
    return normals


def candidate_facets(verts):
    """All supporting hyperplanes through n vertices (float minors, rounded) as primitive (u, b) with u.x <= b."""
    dim = verts.shape[1]
    found = set()
    combos = itertools.combinations(range(len(verts)), dim)
    while True:
        block = np.array(list(itertools.islice(combos, CHUNK)), dtype=np.int64)
        if block.size == 0:
            return found
        base = verts[block[:, 0]]
        diffs = verts[block[:, 1:]] - base[:, None, :]
        normals = subset_normals(diffs)
        keep = np.any(normals != 0, axis=1)
        normals, base = normals[keep], base[keep]
        offsets = np.einsum("ij,ij->i", normals, base)
        values = verts @ normals.T - offsets
        below = np.all(values <= 0, axis=0)
        above = np.all(values >= 0, axis=0)
        for idx in np.nonzero(below | above)[0]:
            sign = 1 if below[idx] else -1
            found.add(primitive(sign * normals[idx], sign * offsets[idx]))


def exact_rank(rows):
    """Rank of a list of integer vectors, exact (fraction Gaussian elimination)."""
    mat = [[Fraction(val) for val in row] for row in rows]
    rank = 0
    width = len(mat[0]) if mat else 0
    for col in range(width):
        pivot = next((r for r in range(rank, len(mat)) if mat[r][col] != 0), None)
        if pivot is None:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        for r in range(len(mat)):
            if r != rank and mat[r][col] != 0:
                factor = mat[r][col] / mat[rank][col]
                mat[r] = [a - factor * b for a, b in zip(mat[r], mat[rank])]
        rank += 1
    return rank


def verify_facets_exact(points, facets):
    """Exact: every point satisfies u.x <= b, and the tight points of each facet span an affine (n-1)-plane."""
    dim = len(points[0])
    for normal, offset in facets:
        dots = [sum(a * b for a, b in zip(normal, pt)) for pt in points]
        if max(dots) != offset:
            return False
        tight = [pt for pt, dot in zip(points, dots) if dot == offset]
        diffs = [[a - b for a, b in zip(pt, tight[0])] for pt in tight[1:]]
        if exact_rank(diffs) != dim - 1:
            return False
    return True


def qhull_facet_count(points):
    """Independent cross-check: number of distinct facet hyperplanes reported by qhull."""
    from scipy.spatial import ConvexHull
    hull = ConvexHull(np.array(points, dtype=float))
    return len({tuple(np.round(eq, 9)) for eq in hull.equations})


def vertex_count(points, facets):
    """Number of points at which the tight facet normals have rank n (= vertices)."""
    dim = len(points[0])
    total = 0
    for pt in points:
        tight = [normal for normal, offset in facets if sum(a * b for a, b in zip(normal, pt)) == offset]
        if tight and exact_rank(tight) == dim:
            total += 1
    return total


def count_points(points, facets, scale, strict):
    """#(scale * P cap Z^n), or the interior count if strict; vectorized over the last <= 4 coordinates."""
    dim = len(points[0])
    lows = [scale * min(pt[i] for pt in points) for i in range(dim)]
    highs = [scale * max(pt[i] for pt in points) for i in range(dim)]
    normals = np.array([normal for normal, _ in facets], dtype=np.int64)
    bounds = scale * np.array([offset for _, offset in facets], dtype=np.int64)
    tail = min(dim, 4)
    tail_axes = [np.arange(lows[i], highs[i] + 1) for i in range(dim - tail, dim)]
    tail_grid = np.stack(np.meshgrid(*tail_axes, indexing="ij"), axis=-1).reshape(-1, tail)
    head_axes = [range(lows[i], highs[i] + 1) for i in range(dim - tail)]
    total = 0
    for head in itertools.product(*head_axes):
        fixed = normals[:, : dim - tail] @ np.array(head, dtype=np.int64) if head else 0
        values = tail_grid @ normals[:, dim - tail:].T + fixed
        inside = np.all(values < bounds, axis=1) if strict else np.all(values <= bounds, axis=1)
        total += int(inside.sum())
    return total


def interpolate(values):
    """Exact coefficients c_0..c_d of the polynomial with p(k) = values[k], k = 0..d."""
    size = len(values)
    mat = [[Fraction(k) ** j for j in range(size)] + [Fraction(values[k])] for k in range(size)]
    for col in range(size):
        pivot = next(r for r in range(col, size) if mat[r][col] != 0)
        mat[col], mat[pivot] = mat[pivot], mat[col]
        mat[col] = [val / mat[col][col] for val in mat[col]]
        for r in range(size):
            if r != col and mat[r][col] != 0:
                factor = mat[r][col]
                mat[r] = [a - factor * b for a, b in zip(mat[r], mat[col])]
    return [mat[r][size] for r in range(size)]


def evaluate(coeffs, k):
    return sum(c * Fraction(k) ** j for j, c in enumerate(coeffs))


def symmetrize(points):
    """The points and their negatives (W5' is stored as one point per +- pair)."""
    return sorted(set(points) | {tuple(-v for v in pt) for pt in points})


def is_symmetric(points):
    pts = set(points)
    return all(tuple(-v for v in pt) in pts for pt in pts)


def analyse(name, points, run_qhull=True, given_facets=None):
    """Full exact analysis of one polytope; returns a dict of results. given_facets: skip the n-subset search
    (used for products, whose facets are F x Q and P x F'); they are still re-verified exactly + by qhull."""
    dim = len(points[0])
    verts = np.array(points, dtype=np.int64)
    facets = sorted(given_facets) if given_facets is not None else sorted(candidate_facets(verts))
    result = {"name": name, "dim": dim, "points": len(points), "symmetric": is_symmetric(points),
              "facets": len(facets), "facets_exact_ok": verify_facets_exact(points, facets),
              "vertices": vertex_count(points, facets),
              "heights": sorted({offset for _, offset in facets})}
    result["qhull_facets"] = qhull_facet_count(points) if run_qhull else None
    counts = [1] + [count_points(points, facets, k, strict=False) for k in range(1, dim + 2)]
    coeffs = interpolate(counts[: dim + 1])
    result.update(counts=counts, coeffs=coeffs, extra_k_ok=(evaluate(coeffs, dim + 1) == counts[dim + 1]))
    interiors = [count_points(points, facets, k, strict=True) for k in (1, 2)]
    result["interior_1"], result["interior_2"] = interiors
    result["reciprocity_ok"] = all(evaluate(coeffs, -k) == (-1) ** dim * interiors[k - 1] for k in (1, 2))
    return result


def cube(dim):
    return [pt for pt in itertools.product((-1, 1), repeat=dim)]


def product_with_segment(points):
    """Vertices of P x [-1,1]."""
    return [pt + (sgn,) for pt in points for sgn in (-1, 1)]


def product_facets(points):
    """Facets of P x [-1,1]: (u, 0).x <= b for each facet u.x <= b of P, and +-x_{n+1} <= 1."""
    dim = len(points[0])
    base = candidate_facets(np.array(points, dtype=np.int64))
    lifted = {(normal + (0,), offset) for normal, offset in base}
    return lifted | {((0,) * dim + (1,), 1), ((0,) * dim + (-1,), 1)}


def polytope_T():
    """Proof chain sec. 6: T = conv{+-f_a +- f_b : a < b}, f_i = e_i (i <= 3), f_4 = (-1,-1,-1,2)."""
    frame = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (-1, -1, -1, 2)]
    pts = set()
    for a, b in itertools.combinations(range(4), 2):
        for sa, sb in itertools.product((1, -1), repeat=2):
            pts.add(tuple(sa * x + sb * y for x, y in zip(frame[a], frame[b])))
    return sorted(pts)


def polytope_X():
    """Proof chain sec. 6: X = conv{+-(1,0,0,0), +-(0,1,0,0), +-(1,1,3,0), +-(2,4,3,6)}."""
    base = [(1, 0, 0, 0), (0, 1, 0, 0), (1, 1, 3, 0), (2, 4, 3, 6)]
    return sorted(set(base) | {tuple(-v for v in pt) for pt in base})


def format_result(res):
    poly = ", ".join(str(c) for c in res["coeffs"])
    lines = [f"## {res['name']}  (n = {res['dim']})",
             f"- input points: {res['points']}; symmetric P = -P: {res['symmetric']}; vertices: {res['vertices']}",
             f"- facets: {res['facets']} (exact re-verification: {res['facets_exact_ok']}; qhull count: {res['qhull_facets']});"
             f" facet lattice heights: {res['heights']}",
             f"- L(k), k = 0..{res['dim'] + 1}: {res['counts']}",
             f"- Ehrhart coefficients g_0..g_{res['dim']}: ({poly})",
             f"- k = {res['dim'] + 1} matches the polynomial: {res['extra_k_ok']}; interior lattice points of P: "
             f"{res['interior_1']}, of 2P: {res['interior_2']}; reciprocity L(-1), L(-2): {res['reciprocity_ok']}"]
    return "\n".join(lines)


def main_report():
    """Analyse every 023 polytope and print the report body."""
    jobs = [("W_5 (w5_vertices.txt)", read_points(W5_FILE)),
            ("W (w_pairs.txt, 25 pairs, +- added)", symmetrize(read_points(W5MIN_FILE))),
            ("T (24-cell model, proof chain sec. 6)", polytope_T()),
            ("X (det-18 cross-polytope, proof chain sec. 6)", polytope_X()),
            ]
    for name, pts in jobs:
        print(format_result(analyse(name, pts, run_qhull=True)), flush=True)
        print(flush=True)
    w5 = read_points(W5_FILE)
    prod = analyse("W5 x [-1,1] (n = 6; facets = product rule, re-verified)", product_with_segment(w5),
                   run_qhull=True, given_facets=product_facets(w5))
    print(format_result(prod), flush=True)


def run_tests():
    """Known Ehrhart polynomials: cube (2k+1)^n, cross-polytope in R^2 and R^3, hexagon."""
    cube3 = analyse("cube3", cube(3))
    assert cube3["coeffs"] == [1, 6, 12, 8] and cube3["facets"] == 6 and cube3["vertices"] == 8, cube3
    cube4 = analyse("cube4", cube(4))
    assert cube4["coeffs"] == [1, 8, 24, 32, 16] and cube4["interior_1"] == 1 and cube4["reciprocity_ok"], cube4
    octa = analyse("octahedron", [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)])
    assert octa["coeffs"] == [1, Fraction(8, 3), 2, Fraction(4, 3)] and octa["facets"] == 8, octa
    hexagon = analyse("hexagon", [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)])
    assert hexagon["coeffs"] == [1, 3, 3] and hexagon["vertices"] == 6, hexagon
    square_with_mid = analyse("square+midpoints", cube(2) + [(1, 0), (-1, 0), (0, 1), (0, -1)])
    assert square_with_mid["vertices"] == 4 and square_with_mid["coeffs"] == [1, 4, 4], square_with_mid
    prism = analyse("cube3 x seg", product_with_segment(cube(3)))
    assert prism["coeffs"] == [1, 8, 24, 32, 16], prism
    octa_pts = [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]
    bip = analyse("octa x seg", product_with_segment(octa_pts), given_facets=product_facets(octa_pts))
    assert bip["facets"] == bip["qhull_facets"] == 10 and bip["facets_exact_ok"], bip
    assert bip["coeffs"][1] == Fraction(8, 3) + 2, bip
    print("ALL TESTS PASS")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--all", action="store_true", help="analyse W5, W5', T, X, W5 x [-1,1]")
    group.add_argument("--test", action="store_true", help="run the test suite")
    group.add_argument("--points", type=Path, help="analyse one vertex file (one point per line)")
    parser.add_argument("--symmetrize", action="store_true", help="with --points: add the negatives")
    args = parser.parse_args()
    if args.test:
        run_tests()
    elif args.points:
        pts = read_points(args.points)
        pts = symmetrize(pts) if args.symmetrize else pts
        print(format_result(analyse(str(args.points), pts)))
    else:
        main_report()


if __name__ == "__main__":
    main()
