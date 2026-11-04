#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# boxes_walk_first.py - the rank-3 boxes, first program: all saturated symmetric full-dimensional sub-polytopes (G >= gmin) of one box,
## version 0.81 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# up to the box's lattice automorphism group; reports classes, point sets (orbit sums) and max g_1 per G; flags g_1 >= 8.
# RANK-4 CUT (default; --no-cut = old full walk): M(S) only grows when points are removed, so a rank-4 set and all its
# descendants are Case I/II (closed elsewhere); every rank-3 set is reached by a chain of rank-3 supersets (checked
# by a second reader; the cut commutes with the symmetry dedupe). Rank-3 sets fill the per-G lines; cut sets go to "CUT G" lines.
# Box points: data/boxes.jsonl ("points_wt", integer coords of the lattice).
# Walk: a saturated T inside a saturated S (T != S) misses a vertex v of conv S, so T lies in S minus {+-v}, and that set is
# saturated; hence the top-down walk "remove one vertex pair" reaches every sub-polytope. g_1 = (8G - 8 - #bd(2P)) / 12.
from pathlib import Path
import os

for _var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_var] = "1"  # one thread

import argparse  # noqa: E402
import itertools  # noqa: E402
import json  # noqa: E402
import sys  # noqa: E402
import time  # noqa: E402
from fractions import Fraction  # noqa: E402

import numpy as np  # noqa: E402
from scipy.spatial import ConvexHull, QhullError  # noqa: E402

BOX_FILE = str(Path(__file__).resolve().parent.parent / "data" / "boxes.jsonl")
TOL = 1e-9


def load_box(index):
    """Box points (tuples) of line `index` of the N10 box file."""
    lines = open(BOX_FILE).read().splitlines()
    return [tuple(p) for p in json.loads(lines[index])["points_wt"]]


def point_invariants(points):
    """A lattice-linear invariant per point: (#y with x+y in S, #y with x-y in S)."""
    pset = set(points)
    inv = []
    for x in points:
        plus = sum(1 for y in points if tuple(a + b for a, b in zip(x, y)) in pset)
        minus = sum(1 for y in points if tuple(a - b for a, b in zip(x, y)) in pset)
        inv.append((plus, minus))
    return inv


def lattice_basis(points):
    """Four points of the set forming a basis of Z^4 (|det| = 1)."""
    nonzero = [p for p in points if any(p)]
    for quad in itertools.combinations(nonzero, 4):
        if round(abs(np.linalg.det(np.array(quad, dtype=float)))) == 1:
            return list(quad)
    raise SystemExit("no lattice basis among the box points - cannot build the symmetry group")


def automorphisms(points):
    """All U in GL_4(Z) with U(S) = S, as index permutations of `points`."""
    index = {p: i for i, p in enumerate(points)}
    inv = point_invariants(points)
    basis = lattice_basis(points)
    pinv = np.linalg.inv(np.array(basis, dtype=float).T)
    classes = [[q for q, iv in zip(points, inv) if iv == inv[index[b]]] for b in basis]
    arr = np.array(points, dtype=float).T
    perms = set()
    for images in itertools.product(*classes):
        umat = np.array(images, dtype=float).T @ pinv
        if not np.allclose(umat, np.round(umat)) or round(abs(np.linalg.det(umat))) != 1:
            continue
        mapped = np.round(umat @ arr).astype(int).T
        perm = [index.get(tuple(m)) for m in mapped]
        if None not in perm:
            perms.add(tuple(perm))
    return np.array(sorted(perms))


def canonical(members, perms):
    """Smallest sorted index tuple among the images of a set of point indices (as bytes); also the orbit size."""
    images = np.sort(perms[:, list(members)], axis=1).astype(np.uint8)
    keys = {row.tobytes() for row in images}
    return min(keys), len(keys)


def full_dim(pts):
    return np.linalg.matrix_rank(np.array(pts, dtype=float)) == 4


def hull_or_none(pts):
    arr = np.array(pts, dtype=float)
    if np.linalg.matrix_rank(arr) < 4:
        return None
    try:
        return ConvexHull(arr)
    except QhullError:
        return None


NONZERO_W = np.array([w for w in itertools.product((-1, 0, 1), repeat=4) if any(w)], dtype=np.int64).T  # 4 x 80


def int_det(rows):
    """Exact determinant of a square integer matrix (fraction-free Bareiss elimination on Python ints)."""
    mat = [[int(x) for x in row] for row in rows]
    size, sign, prev = len(mat), 1, 1
    for k in range(size - 1):
        if mat[k][k] == 0:
            swap = next((r for r in range(k + 1, size) if mat[r][k] != 0), None)
            if swap is None:
                return 0
            mat[k], mat[swap], sign = mat[swap], mat[k], -sign
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                mat[i][j] = (mat[i][j] * mat[k][k] - mat[i][k] * mat[k][j]) // prev
        prev = mat[k][k]
    return sign * mat[-1][-1]


def gram_det(rows):
    """det(R R^T): non-zero iff the integer rows are linearly independent (exact)."""
    return int_det([[sum(int(a) * int(b) for a, b in zip(r1, r2)) for r2 in rows] for r1 in rows])


def int_rank(rows):
    """Exact rank of integer rows (greedy independent subset)."""
    basis = []
    for row in rows:
        if gram_det(basis + [row]) != 0:
            basis.append(row)
    return len(basis)


def adjugate(mat):
    """Exact adjugate of a square integer matrix: adj[j][i] = (-1)^(i+j) * minor(i, j)."""
    size = len(mat)
    adj = [[0] * size for _ in range(size)]
    for i in range(size):
        for j in range(size):
            minor = [[mat[r][c] for c in range(size) if c != j] for r in range(size) if r != i]
            adj[j][i] = (-1) ** (i + j) * int_det(minor)
    return adj


def width2_directions(pts):
    """M(S) = {u in Z^4 : |u.x| <= 1 for all x in S}, exactly, as rows. For 4 independent v_j in S (rows of V^T),
    u.v_j = w_j in {-1,0,1}, so u = adj(V^T) w / det(V^T); keep the integral u that are valid on all of S."""
    quad = []
    for pnt in pts:
        if gram_det(quad + [pnt]) != 0:
            quad.append(pnt)
        if len(quad) == 4:
            break
    if len(quad) < 4:
        raise SystemExit("RANK GUARD FAILED: the set has no 4 independent points (not full-dimensional)")
    det = int_det(quad)
    numer = np.array(adjugate(quad), dtype=np.int64) @ NONZERO_W
    cands = numer[:, np.all(numer % det == 0, axis=0)] // det
    valid = np.all(np.abs(np.array(pts, dtype=np.int64) @ cands) <= 1, axis=0)
    return cands[:, valid].T


def root_directions(points):
    """M(box) as a set of tuples; LOUD unless rank M(box) = 3."""
    dirs = width2_directions(points)
    rank = int_rank(dirs.tolist())
    if rank != 3:
        raise SystemExit(f"ROOT GUARD FAILED: rank M(box) = {rank}, expected 3")
    return {tuple(u) for u in dirs.tolist()}


def is_rank4(pts, root_dirs):
    """True iff rank M(S) = 4. LOUD if M(S) misses a direction of M(box) (it must contain it: S lies in the box)."""
    dirs = width2_directions(pts)
    if not root_dirs <= {tuple(u) for u in dirs.tolist()}:
        raise SystemExit("M GUARD FAILED: M(S) does not contain M(box) - the direction enumeration is wrong")
    return gram_det(dirs.T.tolist()) != 0 if len(dirs) >= 4 else False


def ehrhart_g1_g2(pts, hull):
    """(g_1, g_2) from G = L(1), L(2), I(2) = #int(2P) and L(-1) = 1, all counted with EXACT integer facets:
    g_1 = (8G - 8 - (L2 - I2)) / 12;  vol = ((L2 + I2)/2 - 1 - 2(G - 1)) / 12;  g_2 = (G - 1)/2 - vol.
    LOUD guards (exit non-zero): every facet valid for all points; L1 = G and int = {0} (saturation, W_4);
    vol from the counts = exact cone volume over qhull's simplices (catches a missing facet)."""
    arr = np.array(pts, dtype=np.int64)
    normals, rhs = exact_facets(arr, hull)
    check_exact_vertices(arr, normals, rhs, hull)
    gcount = len(pts)
    big_l1, int1 = lattice_counts(arr, normals, rhs, 1)
    if big_l1 != gcount or len(int1) != 1 or np.any(int1[0]):
        raise SystemExit(f"SATURATION GUARD FAILED: G = {gcount}, lattice points in hull = {big_l1}, interior = {int1.tolist()}")
    big_l2, int2 = lattice_counts(arr, normals, rhs, 2)
    big_i2 = len(int2)
    vol = (Fraction(big_l2 + big_i2, 2) - 1 - 2 * (gcount - 1)) / 12
    cone_vol = Fraction(sum(abs(int(round(np.linalg.det(arr[s].astype(float))))) for s in hull.simplices), 24)
    if vol != cone_vol:
        raise SystemExit(f"VOLUME GUARD FAILED: G = {gcount}, vol from counts {vol} != cone volume {cone_vol}")
    g1 = Fraction(8 * gcount - 8 - (big_l2 - big_i2), 12)
    return g1, Fraction(gcount - 1, 2) - vol


def exact_facets(arr, hull):
    """Integer facet normals n and right sides h (n.x <= h on P) from qhull's simplices; each checked exactly."""
    facets = set()
    for simplex in hull.simplices:
        base = arr[simplex[0]]
        diffs = (arr[simplex[1:]] - base).astype(object)
        normal = [(-1) ** col * int(np.linalg.det(np.delete(diffs, col, axis=1).astype(float)).round()) for col in range(4)]
        gcd = int(np.gcd.reduce(np.abs(normal)))
        if gcd == 0:
            continue  # degenerate piece of qhull's triangulation of a non-simplicial facet (zero volume)
        normal = [c // gcd for c in normal]
        rhs = int(np.dot(normal, base))
        if rhs < 0:
            normal, rhs = [-c for c in normal], -rhs
        facets.add((tuple(normal), rhs))
    normals = np.array([f[0] for f in facets], dtype=np.int64)
    rhs = np.array([f[1] for f in facets], dtype=np.int64)
    if np.any(arr @ normals.T > rhs) or np.any(rhs <= 0):
        raise SystemExit("FACET GUARD FAILED: a qhull facet is not a valid supporting hyperplane (exact check)")
    return normals, rhs


def check_exact_vertices(arr, normals, rhs, hull):
    """VERTEX GUARD: p is a vertex iff no other point is tight on every facet tight at p; must equal qhull's list
    (a non-vertex in the list gives an unsaturated child; a missed vertex would silently lose children)."""
    tight = arr @ normals.T == rhs
    exact = set()
    for pidx in range(len(arr)):
        covers = np.all(tight[:, tight[pidx]], axis=1)
        covers[pidx] = False
        if not covers.any():
            exact.add(pidx)
    if exact != set(int(v) for v in hull.vertices):
        raise SystemExit(f"VERTEX GUARD FAILED: exact vertices {sorted(exact)} != qhull {sorted(hull.vertices)}")


def lattice_counts(arr, normals, rhs, kdil):
    """(#lattice points of k P, array of lattice points of int(k P)), exact integer arithmetic."""
    lo, hi = kdil * arr.min(axis=0), kdil * arr.max(axis=0)
    grid = np.array(list(itertools.product(*[range(lo[i], hi[i] + 1) for i in range(4)])), dtype=np.int64)
    vals = grid @ normals.T
    inside = np.all(vals <= kdil * rhs, axis=1)
    strict = np.all(vals < kdil * rhs, axis=1)
    return int(inside.sum()), grid[strict]


def children(members, points, hull):
    """Child index sets: remove one vertex pair +-v of conv(S)."""
    index = {p: i for i, p in enumerate(points)}
    verts = {members[i] for i in hull.vertices}  # hull indices refer to pts = points[members]
    for vid in verts:
        neg = index[tuple(-c for c in points[vid])]
        if vid < neg:
            yield tuple(m for m in members if m not in (vid, neg))


def evaluate(members, points, perms, stats, flagged):
    """Exact g_1, g_2 of one kept set (all guards); updates the per-G row and the flags; returns the hull."""
    pts = [points[i] for i in members]
    hull = hull_or_none(pts)
    g1, g2 = ehrhart_g1_g2(pts, hull)
    orbit = canonical(members, perms)[1]
    row = stats.setdefault(len(members), [0, 0, Fraction(0), Fraction(0)])
    row[0], row[1], row[2], row[3] = row[0] + 1, row[1] + orbit, max(row[2], g1), max(row[3], g2)
    if g1 >= 8:
        flagged.append((len(members), g1, sorted(pts)))
    return hull


def walk(points, gmin, perms, root_dirs, out=None):
    """Level-by-level walk; root_dirs None = no cut. Returns {G: [classes, point sets, max g_1, max g_2]} over the
    kept sets, {G: [classes, point sets]} over the cut (rank-4) sets, and the flagged sets."""
    full = tuple(range(len(points)))
    level = {canonical(full, perms)[0]: full}
    stats, cuts, flagged = {}, {}, []
    while level:
        nxt = {}
        for members in level.values():
            if root_dirs is not None and is_rank4([points[i] for i in members], root_dirs):
                row = cuts.setdefault(len(members), [0, 0])
                row[0], row[1] = row[0] + 1, row[1] + canonical(members, perms)[1]
                continue
            hull = evaluate(members, points, perms, stats, flagged)
            for child in children(list(members), points, hull):
                if len(child) >= gmin and full_dim([points[i] for i in child]):
                    nxt.setdefault(canonical(child, perms)[0], child)
        gnow = len(next(iter(level.values())))
        emit([f"  [progress {time.strftime('%H:%M:%S')}] level G {gnow} done: {len(level)} classes "
              f"({cuts.get(gnow, [0])[0]} cut), max g_1 {stats[gnow][2] if gnow in stats else '-'}; "
              f"next level {len(nxt)} classes"], out)
        level = nxt
    return stats, cuts, flagged


def report(index, points, perms, results, seconds, cut, out):
    """Report lines; the per-G format is parsed by the comparison program - keep it (CUT/mode lines do not match it)."""
    stats, cuts, flagged = results
    lines = [f"box {index}: G {len(points)}, |Aut| = {len(perms)}, {seconds:.1f}s",
             "  mode: " + ("RANK-4 CUT - per-G lines = rank-3 sets only; rank-4 sets in the CUT lines" if cut
                           else "NO CUT - per-G lines = all sets")]
    for gcount in sorted(stats, reverse=True):
        ncls, nsets, mg1, mg2 = stats[gcount]
        lines.append(f"  G {gcount:3d}: classes {ncls:7d}  point sets {nsets:9d}  max g_1 {mg1}  max g_2 {mg2}")
    lines.append(f"  TOTAL classes {sum(r[0] for r in stats.values())}, point sets {sum(r[1] for r in stats.values())}, "
                 f"max g_1 {max(r[2] for r in stats.values())}, max g_2 {max(r[3] for r in stats.values())}; "
                 f"flagged (g_1 >= 8): {len(flagged)}")
    for gcount in sorted(cuts, reverse=True):
        lines.append(f"  CUT G {gcount:3d}: rank-4 classes {cuts[gcount][0]:7d}  point sets {cuts[gcount][1]:9d}")
    if cut:
        lines.append(f"  TOTAL CUT: rank-4 classes {sum(r[0] for r in cuts.values())}, "
                     f"point sets {sum(r[1] for r in cuts.values())} (Case I/II: closed by C1 + R2 and R4)")
    lines += [f"  FLAG {row}" for row in flagged]
    lines.append(f"RESULT box {index} G {len(points)}: {'PASS (no g_1 >= 8)' if not flagged else 'FLAGGED'}")
    emit(lines, out)


def emit(lines, out):
    for line in lines:
        print(line, flush=True)
    if out:
        with open(out, "a") as handle:
            handle.write("\n".join(lines) + "\n")


def main_box_walk(index, gmin, cut, out=None):
    """Walk one box (cut = True: rank-4 cut); the root guard (rank M(box) = 3) runs in both modes."""
    start = time.time()
    points = load_box(index)
    perms = automorphisms(points)
    root_dirs = root_directions(points)
    results = walk(points, gmin, perms, root_dirs if cut else None, out)
    report(index, points, perms, results, time.time() - start, cut, out)
    return results


# --test targets: rank-3 point sets per G = the second and third exact programs; cut sets per G = their
# "visited" minus rank-3 (box 4: 36-28, 120-64, 284-108; box 5: 10-6, 39-15, 80-20). No cut: the frozen v0.71 numbers.
CUT_TARGETS = {4: ({39: 1, 37: 8, 35: 28, 33: 64, 31: 108}, {35: 8, 33: 56, 31: 176}, Fraction(5)),
               5: ({37: 1, 35: 6, 33: 15, 31: 20}, {35: 4, 33: 24, 31: 60}, Fraction(16, 3))}
NO_CUT_TARGETS = {4: (483, Fraction(5)), 5: (220, Fraction(16, 3))}


def test_guards():
    """The direction enumeration and the root guard on the cube [-1,1]^4: M = {+-e_i} exactly, rank 4 -> guard fires."""
    cube = list(itertools.product((-1, 0, 1), repeat=4))
    dirs = {tuple(u) for u in width2_directions(cube).tolist()}
    assert dirs == {tuple(s * (i == j) for j in range(4)) for i in range(4) for s in (1, -1)}, dirs
    try:
        root_directions(cube)
    except SystemExit as err:
        assert "ROOT GUARD FAILED: rank M(box) = 4" in str(err), err
    else:
        raise AssertionError("root guard did not fire on the rank-4 cube")
    assert int_det([[2, 1], [1, 1]]) == 1 and int_det([[0, 1], [1, 0]]) == -1 and int_rank([[1, 2], [2, 4]]) == 1


def run_tests():
    """Guards; cut mode on boxes 4, 5 (rank-3 sets and cut sets per G, max g_1); no-cut regression (483, 220)."""
    test_guards()
    for index, (want_r3, want_cut, want_g1) in CUT_TARGETS.items():
        stats, cuts, flagged = main_box_walk(index, 31, True)
        got = ({g: r[1] for g, r in stats.items()}, {g: r[1] for g, r in cuts.items()}, max(r[2] for r in stats.values()))
        assert got == (want_r3, want_cut, want_g1) and not flagged, (index, got, len(flagged))
    for index, (want_sets, want_g1) in NO_CUT_TARGETS.items():
        stats, cuts, flagged = main_box_walk(index, 31, False)
        got = (sum(r[1] for r in stats.values()), max(r[2] for r in stats.values()), cuts)
        assert got == (want_sets, want_g1, {}) and not flagged, (index, got, len(flagged))
    print("TESTS PASS (guards; CUT: boxes 4, 5 rank-3 point sets 209 / 42 per G as the second and third programs, cut 240 / 88, "
          "max g_1 5 and 16/3; NO CUT: 483 and 220 point sets)")


def main():
    parser = argparse.ArgumentParser(description="Box walk, first program.")
    parser.add_argument("--test", action="store_true", help="run the small-box tests (seconds)")
    parser.add_argument("--box", type=int, help="box index 0..5 in boxes_list_first.jsonl (large boxes: via the gate only)")
    parser.add_argument("--gmin", type=int, default=31, help="smallest G to keep (default 31)")
    parser.add_argument("--out", help="also append the report lines to this file")
    parser.add_argument("--no-cut", action="store_true", help="old full walk (no rank-4 cut); the unit command lines "
                        "give no flag, so they get the cut")
    args = parser.parse_args()
    if args.test:
        run_tests()
    elif args.box is not None:
        main_box_walk(args.box, args.gmin, not args.no_cut, args.out)
    else:
        sys.exit("give --test or --box N")


if __name__ == "__main__":
    main()
