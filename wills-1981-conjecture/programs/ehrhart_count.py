#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# ehrhart_count.py - exact Ehrhart polynomial of a lattice polytope by counting and interpolation (second program)
## version 0.20 - 20261102 - the version used for the runs reported in the paper
# Written independently: no other counter of this folder was read.
#
# Method (all exact; no floats anywhere in the result):
#   (1) FACETS: the facets of P = conv(V) are the extreme rays of the cone Y = {y : y.(1,v) >= 0 for all v in V}
#       (y = (h, -u) <-> facet u.x <= h). Extreme rays are found by the double-description method in integers,
#       with the combinatorial adjacency test. Each facet is checked afterwards (all v satisfy it; tight set has rank n).
#   (2) COUNT: #(kP cap Z^n) by enumerating x_1..x_{n-1} over a box and counting the x_n-interval exactly with integer
#       floor division. Strict interior: u.x <= k h - 1 (integers).
#   (3) FIT: Ehrhart-Macdonald reciprocity L(-k) = (-1)^n #int(kP) gives values at negative k; the degree-n polynomial is
#       solved exactly with Fractions; one or more EXTRA values are used only as a consistency check (loud failure).
# Usage: ehrhart_count.py --test | --family cube|cross|Q|P|simplex --dim N | --vertices FILE.json
import argparse
import itertools
import json
import math
import sys
from fractions import Fraction

import numpy as np

CHUNK_CELLS = 2_000_000     # (prefix rows) x (facets) int64 cells per numpy block: about 16 MB (memory guard)


# ---------------------------------------------------------------- exact linear algebra helpers
def integer_row(row):
    """The row scaled by the lcm of its denominators: an integer row with the same span (rank-preserving)."""
    if all(isinstance(xx, (int, np.integer)) for xx in row):
        return [int(xx) for xx in row]
    fracs = [Fraction(xx) for xx in row]
    scale = math.lcm(*(ff.denominator for ff in fracs)) if fracs else 1
    return [int(ff * scale) for ff in fracs]


def rank_of(rows):
    """Exact rank over Q of integer/Fraction rows: fraction-free forward elimination in Python ints (v0.20)."""
    mat = [integer_row(row) for row in rows]
    rank, ncols = 0, (len(mat[0]) if mat else 0)
    for col in range(ncols):
        pivot = next((rr for rr in range(rank, len(mat)) if mat[rr][col] != 0), None)
        if pivot is None:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        prow, pval = mat[rank], mat[rank][col]
        for rr in range(rank + 1, len(mat)):
            if mat[rr][col] != 0:
                factor = mat[rr][col]
                newrow = [pval * aa - factor * bb for aa, bb in zip(mat[rr], prow)]
                common = math.gcd(*newrow)
                mat[rr] = [aa // common for aa in newrow] if common > 1 else newrow
        rank += 1
    return rank


def rank_of_fraction_reference(rows):
    """v0.10 rank (Gauss-Jordan over Fractions): kept ONLY as the --test oracle for rank_of."""
    mat = [[Fraction(xx) for xx in row] for row in rows]
    rank, ncols = 0, (len(mat[0]) if mat else 0)
    for col in range(ncols):
        pivot = next((rr for rr in range(rank, len(mat)) if mat[rr][col] != 0), None)
        if pivot is None:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        for rr in range(len(mat)):
            if rr != rank and mat[rr][col] != 0:
                factor = mat[rr][col] / mat[rank][col]
                mat[rr] = [aa - factor * bb for aa, bb in zip(mat[rr], mat[rank])]
        rank += 1
    return rank


def solve_exact(matrix, rhs):
    """Solve the square system matrix * sol = rhs exactly over Q; raise if singular."""
    size = len(matrix)
    aug = [[Fraction(xx) for xx in row] + [Fraction(bb)] for row, bb in zip(matrix, rhs)]
    for col in range(size):
        pivot = next((rr for rr in range(col, size) if aug[rr][col] != 0), None)
        if pivot is None:
            raise ValueError("singular system in solve_exact")
        aug[col], aug[pivot] = aug[pivot], aug[col]
        for rr in range(size):
            if rr != col and aug[rr][col] != 0:
                factor = aug[rr][col] / aug[col][col]
                aug[rr] = [aa - factor * bb for aa, bb in zip(aug[rr], aug[col])]
    return [aug[rr][size] / aug[rr][rr] for rr in range(size)]


def primitive(vec):
    """Divide an integer vector by the gcd of its entries."""
    gg = 0
    for xx in vec:
        gg = math.gcd(gg, int(xx))
    if gg == 0:
        raise ValueError("zero vector cannot be made primitive")
    return tuple(int(xx) // gg for xx in vec)


# ---------------------------------------------------------------- (1) facets by double description
def initial_basis(points):
    """Indices of dim-many linearly independent homogenized points, chosen greedily."""
    chosen = []
    for idx, pt in enumerate(points):
        if rank_of([points[jj] for jj in chosen] + [pt]) == len(chosen) + 1:
            chosen.append(idx)
        if len(chosen) == len(points[0]):
            return chosen
    raise ValueError("polytope is not full-dimensional")


def initial_rays(points, basis):
    """Extreme rays of {y : A0 y >= 0} = columns of A0^{-1}, scaled to primitive integer vectors."""
    dim = len(points[0])
    rays = []
    for jj in range(dim):
        unit = [1 if ii == jj else 0 for ii in range(dim)]
        col = solve_exact([points[ii] for ii in basis], unit)
        denom_lcm = 1
        for xx in col:
            denom_lcm = denom_lcm * xx.denominator // math.gcd(denom_lcm, xx.denominator)
        rays.append(primitive([xx * denom_lcm for xx in col]))
    return rays


def zero_mask(ray, points, indices):
    """Bitmask of the processed inequality indices that are tight at this ray."""
    mask = 0
    for idx in indices:
        if sum(aa * bb for aa, bb in zip(points[idx], ray)) == 0:
            mask |= 1 << idx
    return mask


def adjacent(idx_a, idx_b, all_masks, dim):
    """Combinatorial adjacency test for two extreme rays (by index) of a pointed cone in R^dim."""
    common = all_masks[idx_a] & all_masks[idx_b]
    if bin(common).count("1") < dim - 2:
        return False
    for idx_other, other in enumerate(all_masks):
        if idx_other != idx_a and idx_other != idx_b and (other & common) == common:
            return False
    return True


def dd_add_inequality(rays, masks, points, new_idx, dim):
    """One double-description step: intersect the current cone with points[new_idx].y >= 0."""
    row = points[new_idx]
    vals = [sum(aa * bb for aa, bb in zip(row, ray)) for ray in rays]
    plus = [ii for ii, vv in enumerate(vals) if vv > 0]
    minus = [ii for ii, vv in enumerate(vals) if vv < 0]
    keep = [ii for ii, vv in enumerate(vals) if vv >= 0]
    new_rays = [rays[ii] for ii in keep]
    new_masks = [masks[ii] | ((1 << new_idx) if vals[ii] == 0 else 0) for ii in keep]
    for ip in plus:
        for im in minus:
            if adjacent(ip, im, masks, dim):
                comb = [vals[ip] * bm - vals[im] * bp for bp, bm in zip(rays[ip], rays[im])]
                new_rays.append(primitive(comb))
                new_masks.append((masks[ip] & masks[im]) | (1 << new_idx))
    return new_rays, new_masks


def extreme_rays(rows):
    """Extreme rays of the pointed cone {y : row.y >= 0 for all rows} (double description, exact integers)."""
    dim = len(rows[0])
    basis = initial_basis(rows)
    rays = initial_rays(rows, basis)
    masks = [zero_mask(ray, rows, basis) for ray in rays]
    for idx in range(len(rows)):
        if idx not in basis:
            rays, masks = dd_add_inequality(rays, masks, rows, idx, dim)
    return rays


def facets_of(vertices):
    """Facets (u, h) with u.x <= h, u primitive, of conv(vertices) in R^n (full-dimensional), verified both ways."""
    rays = extreme_rays([tuple([1] + list(vv)) for vv in vertices])
    facets = sorted(set((tuple(-cc for cc in ray[1:]), ray[0]) for ray in rays))
    verify_facets(facets, vertices)
    verify_facets_complete(facets, vertices)
    return facets


def h_vertices(facets):
    """Vertices of {x : u.x <= h} by double description on (t, x): t h - u.x >= 0, t >= 0. Raises if unbounded."""
    nn = len(facets[0][0])
    rows = [tuple([height] + [-cc for cc in normal]) for normal, height in facets] + [tuple([1] + [0] * nn)]
    verts = set()
    for ray in extreme_rays(rows):
        if ray[0] <= 0:
            raise AssertionError(f"H-description is unbounded (ray {ray})")
        verts.add(tuple(Fraction(cc, ray[0]) for cc in ray[1:]))
    return verts


def verify_facets_complete(facets, vertices):
    """Loud check: the H-polytope of the facet list has no vertex outside the input points (so no facet is missing)."""
    extra = h_vertices(facets) - set(tuple(Fraction(xx) for xx in vv) for vv in vertices)
    if extra:
        raise AssertionError(f"facet list incomplete: H-polytope has extra vertices {sorted(extra)[:3]}")


def verify_facets(facets, vertices):
    """Loud check: every vertex satisfies every facet, and each facet's tight vertices span a hyperplane."""
    nn = len(vertices[0])
    for normal, height in facets:
        tight = []
        for vv in vertices:
            val = sum(aa * bb for aa, bb in zip(normal, vv))
            if val > height:
                raise AssertionError(f"vertex {vv} violates facet {normal} <= {height}")
            if val == height:
                tight.append([1] + list(vv))
        if rank_of(tight) != nn:
            raise AssertionError(f"facet {normal} <= {height} has tight rank {rank_of(tight)} != {nn}")


# ---------------------------------------------------------------- (2) exact lattice-point counting
def count_points(facets, vertices, kk, strict):
    """#{x in Z^n : u.x <= k h (or <= k h - 1 if strict) for all facets}, for an integer k >= 0."""
    nn = len(vertices[0])
    lows = [kk * min(vv[ii] for vv in vertices) for ii in range(nn)]
    highs = [kk * max(vv[ii] for vv in vertices) for ii in range(nn)]
    normals = np.array([ff[0] for ff in facets], dtype=np.int64)
    rhs = np.array([kk * ff[1] - (1 if strict else 0) for ff in facets], dtype=np.int64)
    sizes = tuple(highs[ii] - lows[ii] + 1 for ii in range(nn - 1))
    n_prefixes = math.prod(sizes)                    # = 1 when n == 1 (empty prefix)
    chunk = max(1, CHUNK_CELLS // max(1, len(facets)))
    offset = np.array(lows[:-1], dtype=np.int64)
    total = 0
    for start in range(0, n_prefixes, chunk):
        flat = np.arange(start, min(n_prefixes, start + chunk), dtype=np.int64)
        coords = np.unravel_index(flat, sizes) if sizes else ()
        prefixes = (np.stack(coords, axis=1) + offset) if sizes else np.zeros((len(flat), 0), dtype=np.int64)
        total += count_last_coordinate(prefixes, normals, rhs, lows[-1], highs[-1])
    return total


def count_last_coordinate(prefixes, normals, rhs, low_n, high_n):
    """For each prefix (x_1..x_{n-1}) count integers x_n with normals.x <= rhs, inside [low_n, high_n]."""
    slack = rhs[None, :] - prefixes @ normals[:, :-1].T          # rows x facets: c = rhs - u'.x'
    last = normals[:, -1]
    lower = np.full(prefixes.shape[0], low_n, dtype=np.int64)
    upper = np.full(prefixes.shape[0], high_n, dtype=np.int64)
    pos, neg, zer = last > 0, last < 0, last == 0
    if pos.any():
        upper = np.minimum(upper, (slack[:, pos] // last[pos]).min(axis=1))
    if neg.any():
        lower = np.maximum(lower, (-(slack[:, neg] // (-last[neg]))).max(axis=1))
    feasible = (slack[:, zer] >= 0).all(axis=1) if zer.any() else np.ones(prefixes.shape[0], dtype=bool)
    counts = np.where(feasible, np.maximum(upper - lower + 1, 0), 0)
    return int(counts.sum())


# ---------------------------------------------------------------- (3) exact polynomial fit
def ehrhart_values(facets, vertices, k_closed, k_interior):
    """Dict k -> L(k): closed counts for k in k_closed (k >= 0), reciprocity values at -k for k in k_interior."""
    nn = len(vertices[0])
    values = {}
    for kk in k_closed:
        values[kk] = count_points(facets, vertices, kk, strict=False)
    for kk in k_interior:
        values[-kk] = (-1) ** nn * count_points(facets, vertices, kk, strict=True)
    return values


def fit_polynomial(values, degree):
    """Exact coefficients g_0..g_degree from the first degree+1 sample points; the rest are checked."""
    ks = sorted(values, key=lambda kk: (abs(kk), -kk))
    fit_ks, check_ks = ks[: degree + 1], ks[degree + 1:]
    coeffs = solve_exact([[kk ** pp for pp in range(degree + 1)] for kk in fit_ks], [values[kk] for kk in fit_ks])
    for kk in check_ks:
        predicted = sum(cc * kk ** pp for pp, cc in enumerate(coeffs))
        if predicted != values[kk]:
            raise AssertionError(f"consistency check failed at k={kk}: predicted {predicted}, counted {values[kk]}")
    return coeffs, check_ks


def sample_plan(nn, extra):
    """Closed k = 0..a and interior k = 1..b with a + b + 1 = n + 1 + extra, balanced to keep boxes small."""
    needed = nn + 1 + extra
    k_closed_max = needed // 2
    k_interior_max = needed - 1 - k_closed_max
    return list(range(0, k_closed_max + 1)), list(range(1, k_interior_max + 1))


def main_ehrhart(vertices, extra=1):
    """Exact Ehrhart coefficients of conv(vertices); returns (coeffs, facets, values, checked_ks)."""
    facets = facets_of(vertices)
    k_closed, k_interior = sample_plan(len(vertices[0]), extra)
    values = ehrhart_values(facets, vertices, k_closed, k_interior)
    coeffs, checked = fit_polynomial(values, len(vertices[0]))
    return coeffs, facets, values, checked


# ---------------------------------------------------------------- families (test inputs)
def cube_vertices(nn):
    return [tuple(vv) for vv in itertools.product((-1, 1), repeat=nn)]


def cross_vertices(nn):
    out = []
    for ii in range(nn):
        for sign in (1, -1):
            out.append(tuple(sign if jj == ii else 0 for jj in range(nn)))
    return out


def q_vertices(nn):
    """Henze's Q_n = conv{C_{n-1} x 0, +-e_n}."""
    return [tuple(vv) + (0,) for vv in cube_vertices(nn - 1)] + [(0,) * (nn - 1) + (1,), (0,) * (nn - 1) + (-1,)]


def p_vertices(nn):
    """Henze's P_n = conv{C_{n-1} x 0, C*_{n-1} x {-1, 1}}."""
    base = [tuple(vv) + (0,) for vv in cube_vertices(nn - 1)]
    tops = [tuple(vv) + (hh,) for vv in cross_vertices(nn - 1) for hh in (1, -1)]
    return base + tops


def simplex_vertices(nn):
    return [(0,) * nn] + [tuple(1 if jj == ii else 0 for jj in range(nn)) for ii in range(nn)]


FAMILIES = {"cube": cube_vertices, "cross": cross_vertices, "Q": q_vertices, "P": p_vertices, "simplex": simplex_vertices}


# ---------------------------------------------------------------- self-tests
def bernoulli(index):
    """Exact Bernoulli number B_index with B_1 = -1/2."""
    bern = [Fraction(1)]
    for mm in range(1, index + 1):
        bern.append(-sum(math.comb(mm + 1, jj) * bern[jj] for jj in range(mm)) / (mm + 1))
    return bern[index]


def expected_cube(nn):
    return [Fraction(math.comb(nn, ii) * 2 ** ii) for ii in range(nn + 1)]


def expected_cross(nn):
    """L(k) = sum_i 2^i C(n,i) C(k,i); expand C(k,i) as a polynomial in k exactly."""
    coeffs = [Fraction(0)] * (nn + 1)
    for ii in range(nn + 1):
        poly = [Fraction(1)]
        for jj in range(ii):                       # prod_{j<i} (k - j) / i!
            poly = [Fraction(0)] + poly
            poly = [poly[pp] - jj * (poly[pp + 1] if pp + 1 < len(poly) else 0) for pp in range(len(poly))]
        for pp, cc in enumerate(poly):
            coeffs[pp] += Fraction(2 ** ii * math.comb(nn, ii)) * cc / math.factorial(ii)
    return coeffs


def test_rank_against_reference(n_cases=4000, seed=20261102):
    """rank_of (integer elimination) == the v0.10 Fraction oracle on random, low-rank and Fraction matrices."""
    rng = np.random.default_rng(seed)
    for case in range(n_cases):
        nrows, ncols = int(rng.integers(0, 12)), int(rng.integers(1, 7))
        base = rng.integers(-3, 4, size=(max(1, int(rng.integers(1, ncols + 1))), ncols))
        mix = rng.integers(-2, 3, size=(nrows, base.shape[0]))
        rows = [list(rr) for rr in (mix @ base)] if case % 2 else [list(rr) for rr in rng.integers(-5, 6, (nrows, ncols))]
        if case % 5 == 0:
            rows = [[Fraction(int(xx), int(rng.integers(1, 5))) for xx in rr] for rr in rows]
        assert rank_of(rows) == rank_of_fraction_reference(rows), f"rank mismatch on case {case}: {rows}"
    assert rank_of([]) == 0 and rank_of([[0, 0, 0]]) == 0 and rank_of([[2 ** 70, 1], [2 ** 71, 2]]) == 1


def run_tests():
    """Self-tests on polytopes with known Ehrhart polynomials; raises on any mismatch."""
    test_rank_against_reference()
    for nn in (1, 2, 3, 4, 5):
        assert main_ehrhart(cube_vertices(nn))[0] == expected_cube(nn), f"cube {nn}"
        assert main_ehrhart(cross_vertices(nn))[0] == expected_cross(nn), f"cross {nn}"
        simplex = main_ehrhart(simplex_vertices(nn))[0]
        expected = solve_exact([[kk ** pp for pp in range(nn + 1)] for kk in range(nn + 1)],
                               [math.comb(kk + nn, nn) for kk in range(nn + 1)])
        assert simplex == expected, f"simplex {nn}"
    for nn in (3, 4, 5, 6):
        g1 = main_ehrhart(q_vertices(nn))[0][1]
        assert g1 == 2 * (nn - 1) + (4 - 2 ** nn) * bernoulli(nn - 1), f"Henze Q_{nn} g1 {g1}"
    tri1 = [(-1, -1), (2, -1), (-1, 2)]
    tri2 = [(1, 0), (0, 1), (-1, -1)]
    prod = [aa + bb for aa in tri1 for bb in tri2]
    assert main_ehrhart(prod)[0] == [1, 6, Fraction(51, 4), Fraction(27, 2), Fraction(27, 4)], "Henze thesis T1xT2"
    print("ALL SELF-TESTS PASSED: rank_of = Fraction oracle on 4000 matrices, cube/cross/simplex n=1..5, Henze Q_3..Q_6 g1, Henze-thesis T1xT2 (n=4)")


def run_p7_test():
    """Henze's P_7 counterexample: published polynomial (EJC 2014 / thesis 4.4). Heavier (dimension 7)."""
    expected = [1, Fraction(1534, 105), Fraction(3188, 45), Fraction(7112, 45), Fraction(1756, 9),
                Fraction(7004, 45), Fraction(4952, 45), Fraction(15656, 315)]
    coeffs, facets, _values, checked = main_ehrhart(p_vertices(7), extra=0)
    assert coeffs == expected, f"P_7 mismatch: {coeffs}"
    print(f"P_7 PASSED: {len(facets)} facets, g1 = {coeffs[1]} > 14 (Henze's counterexample reproduced)")


# ---------------------------------------------------------------- CLI
def format_report(coeffs, facets, values, checked):
    lines = [f"facets: {len(facets)}", "values L(k): " + ", ".join(f"{kk}:{values[kk]}" for kk in sorted(values)),
             f"consistency-checked k: {checked}"]
    lines += [f"g_{ii} = {cc}" for ii, cc in enumerate(coeffs)]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Exact Ehrhart polynomial (second program)")
    parser.add_argument("--test", action="store_true", help="run self-tests (fast)")
    parser.add_argument("--test-p7", action="store_true", help="reproduce Henze's P_7 (dimension 7, slower)")
    parser.add_argument("--family", choices=sorted(FAMILIES))
    parser.add_argument("--dim", type=int)
    parser.add_argument("--vertices", help="JSON file: list of integer vertex lists")
    args = parser.parse_args()
    if args.test:
        run_tests()
    elif args.test_p7:
        run_p7_test()
    elif args.family:
        print(format_report(*main_ehrhart(FAMILIES[args.family](args.dim))))
    elif args.vertices:
        with open(args.vertices) as handle:
            verts = [tuple(int(xx) for xx in vv) for vv in json.load(handle)]
        print(format_report(*main_ehrhart(verts)))
    else:
        parser.error("give --test, --test-p7, --family with --dim, or --vertices")
        sys.exit(2)


if __name__ == "__main__":
    main()
