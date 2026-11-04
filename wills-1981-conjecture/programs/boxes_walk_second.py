#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# boxes_walk_second.py - the rank-3 boxes, second program: top-down walks of all six boxes with the cut at rank 4
## version 0.50 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# Top-down walk from the full box by vertex-pair removals. Box points come from boxes_list_second.py (my independent box
# list), in a Gamma x Z basis. Every saturated cs subset S of the box with #S >= min_g is reached from the full box by
# removing vertex pairs (each child stays saturated; a saturated T inside S misses a vertex pair of conv S). Invariants
# exact (n = 4 identities, generic_walk.invariants) + the 4-part exact guard on every evaluated set.
# SYMMETRY (v0.50): Aut(box) = all U in GL_4(Z) with U(box) = box, found by backtracking over the images of 4 independent
# box vertices (exact vertex invariants of boxes_list_second, exact integer U, det +-1, U(box) = box checked). Sets are
# deduped per level by the least packed image under Aut(box); a class's point-set count = its number of distinct images.
# Children of a class representative cover the children of its whole orbit (g maps children of S onto children of gS).
# RANK-4 CUT (L9 in walk form): M(S) grows as S shrinks, so a rank-4 set has only
# rank-4 descendants (Case I or II, closed elsewhere); every rank-3 set is reached through rank-3 supersets only. Rank is
# invariant under Aut(box), so the cut commutes with the dedupe. A rank-4 class is counted (CUT) and not expanded.
# Output: LEVEL line per G (rank-3 classes and point sets), CUT line per G, FLAG lines for g_1 >= 8 or g_2 >= 24, then
# per box: CLASSES line, CUT summary, and ONE summary line in point sets (format parsed by the comparison program - keep it).
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 nice -n 19 python3 boxes_walk_second.py --box N --min-g 31
#      (symmetry ON and cut ON; --no-symmetry walks point sets as v0.40; --no-cut walks every set as v0.30)
import argparse
import itertools
import sys
import time
from fractions import Fraction

import numpy as np

from generic_walk import invariants
from case3_reverse_search import fast_facets
from boxes_list_second import box_points, cube_points, exact_vertex_invariant

H_Z3 = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
H_D2 = ((1, 0, 0), (0, 1, 0), (0, 1, 2))  # d = 2: Gamma = {z_2 = z_3 mod 2}
HALF, THIRD, QUARTER = Fraction(1, 2), Fraction(1, 3), Fraction(1, 4)
# box number -> (name, H, a', G); from the output of boxes_list_second.py; numbering 0-3 as in the first program (G 69, 61, 63, 67)
BOXES = {
    0: ("G69", H_Z3, (HALF, HALF, Fraction(0)), 69),
    1: ("G61", H_Z3, (HALF, QUARTER, QUARTER), 61),
    2: ("G63", H_Z3, (2 * THIRD, THIRD, THIRD), 63),
    3: ("G67", H_Z3, (HALF, HALF, HALF), 67),
    4: ("G39", H_D2, (HALF, HALF, Fraction(0)), 39),
    5: ("G37", H_D2, (HALF, QUARTER, QUARTER), 37),
}
G1_BOUND, G2_BOUND = 8, 24  # Wills for n = 4: g_1 <= 8, g_2 <= 24
W_ALL = np.array(list(itertools.product((-1, 0, 1), repeat=4)), dtype=np.int64)  # values of u on 4 points of S
NEG_INF = Fraction(-99)


def build_box(number):
    name, hmat, shift, expected_g = BOXES[number]
    points, _ = cube_points(hmat)
    box = box_points(points, shift)
    assert len(box) == expected_g, f"box {number} ({name}): {len(box)} points, expected {expected_g}"
    return name, box


def int_rank(rows):
    """Exact rank of integer rows (fraction-free elimination on Python ints)."""
    mat = [[int(v) for v in row] for row in rows]
    rank = 0
    for col in range(len(mat[0]) if mat else 0):
        piv = next((r for r in range(rank, len(mat)) if mat[r][col] != 0), None)
        if piv is None:
            continue
        mat[rank], mat[piv] = mat[piv], mat[rank]
        prow = mat[rank]
        for r in range(rank + 1, len(mat)):
            if mat[r][col] != 0:
                fac = mat[r][col]
                mat[r] = [prow[col] * a - fac * b for a, b in zip(mat[r], prow)]
        rank += 1
    return rank


def det3(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1]) - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def det_and_adjugate(vmat):
    """Exact det and adjugate of a 4 x 4 integer matrix (lists of Python ints): adj[j][i] = (-1)^(i+j) minor(i, j)."""
    adj = [[0] * 4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            minor = [[vmat[r][c] for c in range(4) if c != j] for r in range(4) if r != i]
            adj[j][i] = (-1) ** (i + j) * det3(minor)
    det = sum(vmat[0][j] * adj[j][0] for j in range(4))
    return det, adj


def independent_four(rows):
    chosen = []
    for row in rows:
        if int_rank(chosen + [row]) == len(chosen) + 1:
            chosen.append(row)
            if len(chosen) == 4:
                return chosen
    raise AssertionError("set is not full-dimensional")


def rank_m(pts):
    """Exact rank of M(S), S = pts (box coordinates). V = 4 independent points of S as columns; u in M(S) has
    w = V^T u in {-1,0,1}^4, so u = adj(V)^T w / det V (complete candidate list); keep the integral u with abs(u.x) <= 1
    on all of S; rank by exact integer elimination."""
    cols = independent_four(pts.tolist())
    det, adj = det_and_adjugate([[cols[c][r] for c in range(4)] for r in range(4)])
    assert det != 0
    numer = W_ALL @ np.array(adj, dtype=np.int64)  # row w -> w^T adj(V) = (adj(V)^T w)^T
    cands = numer[np.all(numer % det == 0, axis=1)] // det
    alive = cands[np.all(np.abs(pts @ cands.T) <= 1, axis=0)]
    return int_rank(alive.tolist())


def exact_map(src_cols, dst_cols):
    """The integer U with U src = dst (4 x 4, columns = points), or None if U is not integral or |det U| != 1."""
    det, adj = det_and_adjugate(src_cols)
    numer = [[sum(dst_cols[r][k] * adj[k][c] for k in range(4)) for c in range(4)] for r in range(4)]
    if any(v % det != 0 for row in numer for v in row):
        return None
    umat = [[v // det for v in row] for row in numer]
    return umat if abs(det_and_adjugate(umat)[0]) == 1 else None


def automorphisms(box):
    """All U in GL_4(Z) with U(box) = box, as point permutations perm[i] = index of U box[i]. Complete: U is linear, so it
    is fixed by the images of 4 independent vertices; images of vertices are vertices with the same exact invariant and
    the same pairwise lattice lengths, and every such assignment is tried."""
    verts, inv = exact_vertex_invariant(box)
    base = [verts[k] for k in independent_rows_idx([box[v].tolist() for v in verts])]
    src_cols = [[int(box[base[c]][r]) for c in range(4)] for r in range(4)]
    lookup = {tuple(p): i for i, p in enumerate(box)}
    perms = []

    def pair_len(i, j):
        return int(np.gcd.reduce(np.abs(box[i] - box[j])))

    def extend(chosen):
        if len(chosen) == 4:
            umat = exact_map(src_cols, [[int(box[chosen[c]][r]) for c in range(4)] for r in range(4)])
            if umat is None:
                return
            images = [tuple(int(v) for v in np.array(umat, dtype=np.int64) @ p) for p in box]
            if all(img in lookup for img in images):
                perms.append([lookup[img] for img in images])
            return
        k = len(chosen)
        for cand in verts:
            if cand in chosen or inv[cand] != inv[base[k]]:
                continue
            if any(pair_len(cand, chosen[j]) != pair_len(base[k], base[j]) for j in range(k)):
                continue
            extend(chosen + [cand])

    extend([])
    perms = np.array(sorted(set(map(tuple, perms))), dtype=np.int64)
    assert any(np.array_equal(p, np.arange(len(box))) for p in perms), "identity missing"
    return perms


def independent_rows_idx(rows):
    chosen, idx = [], []
    for k, row in enumerate(rows):
        if int_rank(chosen + [row]) == len(chosen) + 1:
            chosen.append(row)
            idx.append(k)
            if len(chosen) == 4:
                return idx
    raise AssertionError("box vertices do not span R^4")


def images_packed(mask, perms):
    """Packed bit rows of all images g(S), g in the group (row g: image[perms[g][i]] = mask[i])."""
    images = np.zeros((len(perms), mask.size), dtype=bool)
    images[np.arange(len(perms))[:, None], perms] = mask[None, :]
    return np.packbits(images, axis=1)


def canonical(mask, perms):
    packed = images_packed(mask, perms)
    return min(row.tobytes() for row in packed)


def orbit_size(mask, perms):
    return len({row.tobytes() for row in images_packed(mask, perms)})


def unpack(key, size):
    return np.unpackbits(np.frombuffer(key, dtype=np.uint8))[:size].astype(bool)


def guard_fail(name, mask, why):
    print(f"GUARD FAIL box {name}: {why}; points {np.flatnonzero(mask).tolist()}", flush=True)
    sys.exit(3)


def exact_guard(box, mask, qhull_verts, name):
    """Exact integer checks of one set S (= box[mask]); exits 3 on any failure. F = integer facet inequalities a.x <= b.
    (1) every inequality of F holds on S (so conv S lies inside the polyhedron of F);
    (2) the box points inside the polyhedron of F are exactly S - all lattice points of conv S are box points, so S is
        saturated; (3) exactly one box point, the origin, is strictly inside every inequality (one interior point);
    (4) exact vertices = points p of S such that no other q in S is tight on every inequality tight at p. Any p in the
        relative interior of a face of dim >= 1 is caught by a vertex q of that face, so these are true vertices; they must
        equal qhull's list (a non-vertex in qhull's list would make an unsaturated child)."""
    normals, rhs, _ = fast_facets(box[mask])
    values = box @ normals.T
    inside, strict = np.all(values <= rhs, axis=1), np.all(values < rhs, axis=1)
    if not np.all(inside[mask]):
        guard_fail(name, mask, "an integer facet inequality fails on S")
    if not np.array_equal(inside, mask):
        guard_fail(name, mask, f"NOT SATURATED: {int(inside.sum())} box points in conv S, {int(mask.sum())} in S")
    if strict.sum() != 1 or np.any(box[strict]):
        guard_fail(name, mask, f"{int(strict.sum())} interior lattice points (must be the origin only)")
    idx = np.flatnonzero(mask)
    tight = (values[idx] == rhs).astype(np.int64)
    shared, own = tight @ tight.T, tight.sum(axis=1)
    covered = (shared == own[:, None]).sum(axis=1) > 1  # another q is tight wherever p is
    exact_verts = set(idx[~covered].tolist())
    if exact_verts != {int(v) for v in qhull_verts}:
        guard_fail(name, mask, f"qhull vertices {sorted(int(v) for v in qhull_verts)} != exact {sorted(exact_verts)}")


def is_cut(box, mask, name):
    """True iff rank M(S) = 4 (cut); rank 3 -> False; anything else is impossible inside a box (loud)."""
    rank = rank_m(box[mask])
    if rank not in (3, 4):
        guard_fail(name, mask, f"rank M = {rank} (inside a box it must be 3 or 4)")
    return rank == 4


class Level:
    """Counts of one level: kept (rank 3, or all if the cut is off) and cut, in classes and point sets; maxima."""

    def __init__(self):
        self.kept_classes = self.kept_sets = self.cut_classes = self.cut_sets = 0
        self.best1 = self.best2 = NEG_INF


def walk_level(box, neg, perms, frontier, min_g, name, level_g, cut):
    """One level of class representatives (canonical keys): returns (next level keys, Level counts)."""
    children, stats = set(), Level()
    for key in frontier:
        mask = unpack(key, len(box))
        assert int(mask.sum()) == level_g, (name, int(mask.sum()), level_g)
        orbit = orbit_size(mask, perms)
        if cut and is_cut(box, mask, name):
            stats.cut_classes, stats.cut_sets = stats.cut_classes + 1, stats.cut_sets + orbit
            continue
        (count, vol, g3, g1, g2), verts = invariants(box, mask)
        exact_guard(box, mask, verts, name)
        stats.kept_classes, stats.kept_sets = stats.kept_classes + 1, stats.kept_sets + orbit
        stats.best1, stats.best2 = max(stats.best1, g1), max(stats.best2, g2)
        if g1 >= G1_BOUND or g2 >= G2_BOUND:
            print(f"FLAG box {name}: G {count} g_1 {g1} g_2 {g2} points {np.flatnonzero(mask).tolist()}", flush=True)
        if count - 2 >= min_g:
            for v in {int(min(w, neg[w])) for w in verts}:
                child = mask.copy()
                child[[v, int(neg[v])]] = False
                children.add(canonical(child, perms))
    return children, stats


def walk_box(name, box, perms, min_g, cut):
    """Per-G dicts (kept sets, kept classes, cut sets, cut classes) and the maxima over kept sets."""
    lookup = {tuple(p): i for i, p in enumerate(box)}
    neg = np.array([lookup[tuple(-p)] for p in box])
    full = np.ones(len(box), dtype=bool)
    if cut and rank_m(box) != 3:
        guard_fail(name, full, f"root box has rank M = {rank_m(box)}, must be 3")
    frontier, level_g = {canonical(full, perms)}, len(box)
    sets, classes, cut_sets, cut_classes = {}, {}, {}, {}
    best1, best2, t0 = NEG_INF, NEG_INF, time.time()
    while frontier:
        frontier_next, st = walk_level(box, neg, perms, frontier, min_g, name, level_g, cut)
        if st.kept_classes:
            sets[level_g], classes[level_g] = st.kept_sets, st.kept_classes
        if st.cut_classes:
            cut_sets[level_g], cut_classes[level_g] = st.cut_sets, st.cut_classes
        best1, best2 = max(best1, st.best1), max(best2, st.best2)
        kind = "rank-3" if cut else "all"
        print(f"LEVEL box {name}: G {level_g}: {kind} classes {st.kept_classes}, {kind} point sets {st.kept_sets}, "
              f"max g_1 {st.best1}, max g_2 {st.best2}, elapsed {time.time() - t0:.1f} s", flush=True)
        if cut:
            print(f"CUT box {name}: G {level_g}: rank-4 classes {st.cut_classes}, rank-4 point sets {st.cut_sets}",
                  flush=True)
        frontier, level_g = frontier_next, level_g - 2
    return [dict(sorted(d.items())) for d in (sets, classes, cut_sets, cut_classes)] + [best1, best2]


def summary_line(name, size, min_g, per_g, best1, best2):
    return (f"box {name}: G = {size}; point sets with G >= {min_g}: {sum(per_g.values())} per G {per_g}; "
            f"max g_1 = {best1}, max g_2 = {best2}")


def group_for(box, symmetry):
    return automorphisms(box) if symmetry else np.arange(len(box), dtype=np.int64)[None, :]


def main_walk(number, min_g, cut, symmetry):
    name, box = build_box(number)
    perms = group_for(box, symmetry)
    print(f"MODE box {name}: symmetry {'ON' if symmetry else 'OFF'} (group order {len(perms)}), "
          f"rank-4 cut {'ON' if cut else 'OFF'}", flush=True)
    sets, classes, cut_sets, cut_classes, best1, best2 = walk_box(name, box, perms, min_g, cut)
    print(f"CLASSES box {name}: {'rank-3' if cut else 'all'} classes {sum(classes.values())} per G {classes}", flush=True)
    if cut:
        print(f"CUT box {name}: rank-4 classes cut {sum(cut_classes.values())} per G {cut_classes}; rank-4 point sets "
              f"cut {sum(cut_sets.values())} per G {cut_sets}", flush=True)
        print("RANK-CUT MODE: the summary below counts RANK-3 point sets only; maxima are over rank-3 sets", flush=True)
    print(summary_line(name, len(box), min_g, sets, best1, best2), flush=True)


def check_box(number, cut, symmetry, sets_exp, cut_sets_exp, g1_exp):
    name, box = build_box(number)
    perms = group_for(box, symmetry)
    sets, classes, cut_sets, cut_classes, best1, best2 = walk_box(name, box, perms, 31, cut)
    assert (sets, cut_sets, best1) == (sets_exp, cut_sets_exp, g1_exp), (number, cut, symmetry, sets, cut_sets, best1)
    if not symmetry:
        assert classes == sets and cut_classes == cut_sets
    mode = f"{'SYM  ' if symmetry else 'NOSYM'} {'CUT  ' if cut else 'NOCUT'}"
    print(f"{mode} {summary_line(name, len(box), 31, sets, best1, best2)} | classes {sum(classes.values())} "
          f"{classes}; cut classes {sum(cut_classes.values())}")
    return classes, cut_classes


def main_test():
    """|Aut| of boxes 0-3 = the first program's 32, 8, 12, 96. For boxes 4, 5, every mode (symmetry on/off x cut on/off) gives the
    point-set counts measured at 09:47 (rank-3 209 / 42, cut 240 / 88; no cut 483 / 220). Guard negative tests."""
    orders = {number: len(automorphisms(build_box(number)[1])) for number in BOXES}
    print(f"|Aut| per box: {orders}")
    assert [orders[n] for n in (0, 1, 2, 3)] == [32, 8, 12, 96], orders
    expect_cut = {4: ({31: 108, 33: 64, 35: 28, 37: 8, 39: 1}, {31: 176, 33: 56, 35: 8}, Fraction(5)),
                  5: ({31: 20, 33: 15, 35: 6, 37: 1}, {31: 60, 33: 24, 35: 4}, Fraction(16, 3))}
    expect_all = {4: ({31: 318, 33: 120, 35: 36, 37: 8, 39: 1}, {}, Fraction(5)),
                  5: ({31: 160, 33: 49, 35: 10, 37: 1}, {}, Fraction(16, 3))}
    for number in (4, 5):
        for symmetry in (True, False):
            check_box(number, True, symmetry, *expect_cut[number])
            check_box(number, False, symmetry, *expect_all[number])
    guard_must_fire()
    print("TEST PASS (|Aut| 32 8 12 96; boxes 4, 5 in all 4 modes: rank-3 209 / 42, cut 240 / 88, all 483 / 220; "
          "guard fires)")


def guard_must_fire():
    """Negative tests: on box 0 remove a NON-vertex pair (unsaturated set), then pass a vertex list with a non-vertex."""
    name, box = build_box(0)
    full = np.ones(len(box), dtype=bool)
    _, verts = invariants(box, full)
    lookup = {tuple(p): i for i, p in enumerate(box)}
    inner = next(i for i, p in enumerate(box) if i not in set(verts.tolist()) and np.any(p))
    holed = full.copy()
    holed[[inner, lookup[tuple(-box[inner])]]] = False
    for mask, fake_verts in ((holed, None), (full, np.append(verts, inner))):
        if fake_verts is None:
            _, fake_verts = invariants(box, mask)
        try:
            exact_guard(box, mask, fake_verts, name + "-negative-test")
        except SystemExit as exc:
            assert exc.code == 3
            continue
        raise AssertionError("guard did not fire")


def main():
    parser = argparse.ArgumentParser(description="rank-3 box walks, second program")
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--box", type=int, choices=sorted(BOXES))
    parser.add_argument("--min-g", type=int)
    parser.add_argument("--no-cut", action="store_true", help="walk every set (v0.30 behaviour); default: rank-4 cut ON")
    parser.add_argument("--no-symmetry", action="store_true", help="point sets, no dedupe (v0.40); default: symmetry ON")
    args = parser.parse_args()
    if args.test:
        main_test()
        return
    if args.box is None or args.min_g is None:
        parser.error("--box and --min-g are required (no defaults)")
    main_walk(args.box, args.min_g, not args.no_cut, not args.no_symmetry)


if __name__ == "__main__":
    main()
