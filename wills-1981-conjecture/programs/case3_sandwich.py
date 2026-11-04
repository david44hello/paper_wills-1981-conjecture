#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# case3_sandwich.py - Case III, second program: sandwich search per frame lattice (modes FULL, rank cut)
## version 1.00 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# Written independently of the first program (not read).
# Setting (Path C): P in W_4 with a max-det frame v_1..v_4 (|det| = D). In c-coordinates (c = x H^{-1}, H = frame
# rows) P cap Z^4 becomes S subset of L cap [-1,1]^4, L = Z^4 H^{-1} (index D), +-e_i in S, and
#   (i)   every 4 points of S have |det_c| <= 1   <=>  (frame included) every k x k minor (k = 1..4) of the non-frame
#         points has |.| <= 1; in y = D c integer coordinates: |k-minor| <= D^k;
#   (iii) int conv(S) cap L = {0}.
# Both (i) and (iii) are closed under subsets, so admissible sets form a down-closed family; we enumerate its MAXIMAL members
# of size >= GMIN by a Bron-Kerbosch-type backtrack (correct for down-closed families: C' u X' = all y addable to S + x).
# Part A (this version): reconnaissance with (i) only - number/sizes of maximal (i)-sets per L, and (iii) status of each.
import argparse
import itertools
import json
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ehrhart_count as ehr  # noqa: E402
import frame_lattices_orbits as ll  # noqa: E402

PAIRS2 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
COMPL = {(0, 1): (2, 3), (0, 2): (1, 3), (0, 3): (1, 2), (1, 2): (0, 3), (1, 3): (0, 2), (2, 3): (0, 1)}
LAPLACE_SIGN = {(0, 1): 1, (0, 2): -1, (0, 3): 1, (1, 2): 1, (1, 3): -1, (2, 3): 1}
TRIPLES3 = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]


class Lattice:
    """One lattice L (orbit representative): box points, classes, Stab(L), minors."""

    def __init__(self, det, hmat):
        self.det = det
        self.hmat = hmat
        _dd, self.cosets = ll.coset_set(hmat)
        self.box = self.box_points()                       # integer y = D c, |y_i| <= D
        self.frame = [tuple(det if kk == ii else 0 for kk in range(4)) for ii in range(4)]
        frame_set = set(self.frame) | {tuple(-xx for xx in ff) for ff in self.frame}
        self.classes = [yy for yy in self.box if any(yy) and yy not in frame_set and self.is_rep(yy)]
        self.yarr = np.array(self.classes, dtype=np.int64)
        self.stab = self.stabilizer()

    @staticmethod
    def is_rep(yy):
        first = next(xx for xx in yy if xx != 0)
        return first > 0

    def box_points(self):
        out = []
        for ee in self.cosets:
            choices = [[vv for vv in (ee[ii] - 2 * self.det, ee[ii] - self.det, ee[ii], ee[ii] + self.det)
                        if -self.det <= vv <= self.det] for ii in range(4)]
            out.extend(itertools.product(*choices))
        return sorted(set(out))

    def stabilizer(self):
        coset_keys = set(self.cosets)
        out = []
        for sigma, signs in ll.SIGNED_PERMS:
            img = {tuple((signs[jj] * ee[sigma[jj]]) % self.det for jj in range(4)) for ee in self.cosets}
            if img == coset_keys:
                out.append((sigma, signs))
        return out

    def to_x(self, yy):
        """x = c H = (y / D) H, an integer vector (c in L)."""
        out = []
        for col in range(4):
            val = Fraction(sum(yy[rr] * self.hmat[rr][col] for rr in range(4)), self.det)
            assert val.denominator == 1
            out.append(int(val))
        return tuple(out)


def plucker(arr_a, arr_b):
    """2x2 minors (6 per pair) of row pairs (a, b): shape (..., 6)."""
    return np.stack([arr_a[..., ii] * arr_b[..., jj] - arr_a[..., jj] * arr_b[..., ii] for ii, jj in PAIRS2], axis=-1)


class Admissibility:
    """Condition (i) for class sets, exact int64 (entries |y_i| <= 18, minors far below 2^63)."""

    def __init__(self, lat):
        self.lat = lat
        dd = lat.det
        self.b2, self.b3, self.b4 = dd ** 2, dd ** 3, dd ** 4
        yy = lat.yarr
        self.p2 = plucker(yy[:, None, :], yy[None, :, :])                 # N x N x 6
        self.pair_ok = (np.abs(self.p2) <= self.b2).all(axis=2)

    def minor3_ok(self, xi, cand, sset):
        """For each y in cand: all 3x3 minors of (x, y, s) <= D^3 for all s in sset."""
        if not sset:
            return np.ones(len(cand), dtype=bool)
        p_xy = self.p2[xi, cand]                                          # |C| x 6
        svec = self.lat.yarr[sset]                                        # |S| x 4
        ok = np.ones(len(cand), dtype=bool)
        idx = {pp: kk for kk, pp in enumerate(PAIRS2)}
        for (aa, bb, cc) in TRIPLES3:
            # minor on columns a<b<c of rows (x, y, s) = s_a P_bc - s_b P_ac + s_c P_ab
            val = (svec[None, :, aa] * p_xy[:, None, idx[(bb, cc)]] - svec[None, :, bb] * p_xy[:, None, idx[(aa, cc)]]
                   + svec[None, :, cc] * p_xy[:, None, idx[(aa, bb)]])
            ok &= (np.abs(val) <= self.b3).all(axis=1)
        return ok

    def det4_ok(self, xi, cand, sset):
        """For each y in cand: det(x, y, s, t) <= D^4 for all s < t in sset (Laplace on rows 1-2 / 3-4)."""
        if len(sset) < 2:
            return np.ones(len(cand), dtype=bool)
        pairs = np.array(list(itertools.combinations(sset, 2)))
        p_st = self.p2[pairs[:, 0], pairs[:, 1]]                          # |pairs| x 6
        idx = {pp: kk for kk, pp in enumerate(PAIRS2)}
        weights = np.zeros((6, 6), dtype=np.int64)
        for pp, sign in LAPLACE_SIGN.items():
            weights[idx[pp], idx[COMPL[pp]]] = sign
        dets = self.p2[xi, cand] @ weights @ p_st.T                        # |C| x |pairs|
        return (np.abs(dets) <= self.b4).all(axis=1)

    def filter(self, xi, cand, sset):
        """Candidates y (indices) such that S + x + y satisfies (i), given S + x and S + y already do."""
        cand = np.asarray(cand, dtype=np.int64)
        if cand.size == 0:
            return cand
        keep = self.pair_ok[xi, cand]
        keep &= self.minor3_ok(xi, cand, sset)
        keep &= self.det4_ok(xi, cand, sset)
        return cand[keep]


def maximal_sets(adm, kmin, limit):
    """Bron-Kerbosch over the down-closed family of (i)-admissible class sets; yields maximal sets of size >= kmin."""
    nn = len(adm.lat.classes)
    out = []

    def rec(sset, cand, excl):
        if len(out) >= limit:
            return
        if len(sset) + len(cand) < kmin:
            return
        if not len(cand) and not len(excl):
            out.append(tuple(sset))
            return
        cand = list(cand)
        excl = list(excl)
        while cand:
            xi = cand.pop(0)
            new_c = adm.filter(xi, cand, sset)
            new_x = adm.filter(xi, excl, sset)
            rec(sset + [xi], list(new_c), list(new_x))
            excl.append(xi)
            if len(sset) + len(cand) < kmin:
                return

    rec([], list(range(nn)), [])
    return out


def points_of(lat, classes_idx):
    pts = [tuple(-xx for xx in ff) for ff in lat.frame] + list(lat.frame) + [(0, 0, 0, 0)]
    for ii in classes_idx:
        yy = lat.classes[ii]
        pts += [yy, tuple(-xx for xx in yy)]
    return pts


def interior_count(lat, yset):
    """#(int conv(S) cap L) by the exact counter in x-coordinates (L <-> Z^4)."""
    xs = [lat.to_x(yy) for yy in yset]
    facets = ehr.facets_of(xs)
    return ehr.count_points(facets, xs, 1, strict=True), ehr.count_points(facets, xs, 1, strict=False)


def recon(gmin, limit, dets):
    reps = json.loads(Path(str(Path(__file__).resolve().parent.parent / "data" / "frame_lattices.json")).read_text())
    kmin = (gmin - 1) // 2 - 4                      # non-frame classes needed for |S| = 1 + 2(4 + k) >= gmin
    for rep in reps:
        if dets and rep["D"] not in dets:
            continue
        lat = Lattice(rep["D"], rep["H"])
        adm = Admissibility(lat)
        sets = maximal_sets(adm, kmin, limit)
        stats = []
        for ss in sets[:50]:
            pts = points_of(lat, ss)
            n_int, n_all = interior_count(lat, pts)
            stats.append((len(pts), n_all, n_int))
        print(f"D={rep['D']:2d} box={rep['box_points']:3d} classes={len(lat.classes):3d} |Stab|={len(lat.stab):3d} "
              f"maximal(i)-sets(>= {gmin} pts)={len(sets)}{'+' if len(sets) >= limit else ''} "
              f"first (|S|, G(conv), #int): {stats[:6]}", flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--recon", action="store_true")
    parser.add_argument("--gmin", type=int, default=31)
    parser.add_argument("--limit", type=int, default=2000)
    parser.add_argument("--dets", type=int, nargs="*")
    parser.add_argument("--bfs", action="store_true")
    parser.add_argument("--topdown", action="store_true")
    parser.add_argument("--sandwich", action="store_true")
    parser.add_argument("--node-budget", type=int, default=10 ** 8)
    parser.add_argument("--only-index", type=int, default=None)
    parser.add_argument("--rank-prune", action="store_true")
    parser.add_argument("--dump-leaves", default=None, help="append one JSON line per leaf to this file")
    parser.add_argument("--branch-rule", choices=["auto", "norm", "fewest", "critical", "hybrid"], default="auto")
    parser.add_argument("--rank-cut", type=int, default=4, help="with --rank-prune: cut when rank M(B) >= this (4 = L9)")
    parser.add_argument("--max-states", type=int, default=10 ** 7)
    args = parser.parse_args()
    if args.recon:
        recon(args.gmin, args.limit, args.dets)
    if args.bfs:
        run_bfs(args.dets, args.gmin, args.max_states)
    if args.topdown:
        run_topdown(args.dets, args.gmin, sys.stdout)
    if args.sandwich:
        run_sandwich(args.dets, args.gmin, sys.stdout, args.node_budget, args.only_index, args.rank_prune, args.rank_cut,
                     args.branch_rule, args.dump_leaves)



# ================================================================ part B (v0.20): bottom-up level BFS over A(L)
# States: saturated admissible sets S, stored as frozensets of non-frame class indices K (S = {0, +-e_i} u {+-y_k}).
# Children: K + {y} with K + y passing (i) (exact minors, vectorized) and conv(S u {+-y}) passing (iii) and (sat)
# (exact hull + every box point tested). Complete by L8 (4). Dedupe: canonical form under Stab(L) per level.
# Prune: if |S| + 2 |Omega_(i)(S)| < GMIN then no descendant reaches GMIN (L8 (5), Omega within Omega_(i)).

SIGNS4 = np.array([1, -1, 1, -1], dtype=np.int64)


def minors3_of_triples(yarr, triples):
    """For rows (s, t, u): the four 3x3 minors deleting column a (a = 0..3), shape (T, 4)."""
    out = []
    for aa in range(4):
        cols = [cc for cc in range(4) if cc != aa]
        sub = yarr[triples][:, :, cols]                                   # T x 3 x 3
        det = (sub[:, 0, 0] * (sub[:, 1, 1] * sub[:, 2, 2] - sub[:, 1, 2] * sub[:, 2, 1])
               - sub[:, 0, 1] * (sub[:, 1, 0] * sub[:, 2, 2] - sub[:, 1, 2] * sub[:, 2, 0])
               + sub[:, 0, 2] * (sub[:, 1, 0] * sub[:, 2, 1] - sub[:, 1, 1] * sub[:, 2, 0]))
        out.append(det)
    return np.stack(out, axis=1)


def addable_i(adm, kset, cand):
    """Candidates y (indices) with K + y passing (i), given K passes."""
    cand = np.asarray(cand, dtype=np.int64)
    kk = list(kset)
    if cand.size == 0 or not kk:
        return cand
    yy = adm.lat.yarr
    keep = adm.pair_ok[np.ix_(cand, kk)].all(axis=1)
    if len(kk) >= 2:
        pairs = np.array(list(itertools.combinations(kk, 2)))
        p_st = adm.p2[pairs[:, 0], pairs[:, 1]]                            # pairs x 6
        idx = {pp: ii for ii, pp in enumerate(PAIRS2)}
        for (aa, bb, cc) in TRIPLES3:                                      # minor of rows (y, s, t) on cols a<b<c
            val = (yy[cand][:, None, aa] * p_st[None, :, idx[(bb, cc)]] - yy[cand][:, None, bb] * p_st[None, :, idx[(aa, cc)]]
                   + yy[cand][:, None, cc] * p_st[None, :, idx[(aa, bb)]])
            keep &= (np.abs(val) <= adm.b3).all(axis=1)
    if len(kk) >= 3:
        triples = np.array(list(itertools.combinations(kk, 3)))
        mins = minors3_of_triples(yy, triples) * SIGNS4[None, :]           # T x 4 (cofactor signs along row y)
        dets = yy[cand] @ mins.T                                            # det(y, s, t, u) for all triples
        keep &= (np.abs(dets) <= adm.b4).all(axis=1)
    return cand[keep]


class Walker2:
    def __init__(self, lat, adm):
        self.lat, self.adm = lat, adm
        self.box_x = np.array([lat.to_x(yy) for yy in lat.box], dtype=np.int64)
        self.box_index = {yy: ii for ii, yy in enumerate(lat.box)}
        self.frame_pts = [tuple(ss * xx for xx in ff) for ff in lat.frame for ss in (1, -1)]
        self.class_perm = self.class_permutations()

    def class_permutations(self):
        index = {yy: ii for ii, yy in enumerate(self.lat.classes)}
        perms = []
        for sigma, signs in self.lat.stab:
            row = []
            for yy in self.lat.classes:
                img = tuple(signs[jj] * yy[sigma[jj]] for jj in range(4))
                row.append(index[img] if img in index else index[tuple(-xx for xx in img)])
            perms.append(row)
        return np.array(perms, dtype=np.int64)

    def canonical(self, kset):
        arr = np.array(sorted(kset), dtype=np.int64)
        return min(tuple(sorted(row)) for row in self.class_perm[:, arr]) if arr.size else ()

    def points(self, kset):
        pts = [(0, 0, 0, 0)] + self.frame_pts
        for kk in kset:
            yy = self.lat.classes[kk]
            pts += [yy, tuple(-xx for xx in yy)]
        return pts

    def hull_ok(self, kset, base_vertices=None, new_class=None):
        """(iii) and (sat) for S(K), exact: facets in x-coordinates, every box point tested.
        If base_vertices (x-coords of the parent hull's vertices) and new_class are given, the hull is built from
        base_vertices + {+-y} only (conv(S u {+-y}) = conv(vert(conv S) u {+-y})). Returns (ok, vertices_x)."""
        if base_vertices is None:
            hull_in = [self.lat.to_x(yy) for yy in self.points(kset)]
        else:
            yy = self.lat.classes[new_class]
            hull_in = list(base_vertices) + [self.lat.to_x(yy), self.lat.to_x(tuple(-xx for xx in yy))]
        rays = ehr.extreme_rays([tuple([1] + list(vv)) for vv in hull_in])
        facets = sorted(set((tuple(-cc for cc in ray[1:]), ray[0]) for ray in rays))
        ehr.verify_facets(facets, hull_in)
        normals = np.array([ff[0] for ff in facets], dtype=np.int64)
        heights = np.array([ff[1] for ff in facets], dtype=np.int64)
        vals = self.box_x @ normals.T
        n_inside = int((vals <= heights[None, :]).all(axis=1).sum())
        n_strict = int((vals < heights[None, :]).all(axis=1).sum())
        size = 1 + 2 * (4 + len(kset))
        if not (n_inside == size and n_strict == 1):
            return False, None
        hin = np.array(hull_in, dtype=np.int64)
        tight = (hin @ normals.T) == heights[None, :]
        verts = [tuple(hull_in[ii]) for ii in range(len(hull_in))
                 if ehr.rank_of([list(normals[jj]) for jj in np.flatnonzero(tight[ii])]) == 4]
        return True, sorted(set(verts))


def bfs_lattice(lat, gmin, log, max_states):
    adm = Admissibility(lat)
    walker = Walker2(lat, adm)
    k0 = frozenset(ii for ii, yy in enumerate(lat.classes) if sum(abs(xx) for xx in yy) == lat.det)   # R_L = C cap L
    ok0, verts0 = walker.hull_ok(k0)
    assert ok0, "R_L must be admissible"
    level = {walker.canonical(k0): (k0, verts0)}
    kneed = (gmin - 1) // 2 - 4
    rows, best, flagged, total = [], None, [], 0
    while level:
        nxt = {}
        gg = 1 + 2 * (4 + len(next(iter(level.values()))[0]))
        n_pruned = n_hulls = 0
        for _key, (kset, verts) in level.items():
            total += 1
            if total > max_states:
                raise RuntimeError(f"state budget {max_states} exceeded")
            if gg >= gmin:
                coeffs = ehr.main_ehrhart(verts, extra=1)[0]
                if best is None or coeffs[1] > best:
                    best = coeffs[1]
                if coeffs[1] >= 8:
                    flagged.append((gg, [str(cc) for cc in coeffs], sorted(kset)))
            cand = [ii for ii in range(len(lat.classes)) if ii not in kset]
            cand = addable_i(adm, kset, cand)
            if len(kset) + len(cand) < kneed:
                n_pruned += 1
                continue
            for yy in cand:
                child = kset | {int(yy)}
                ckey = walker.canonical(child)
                if ckey in nxt:
                    continue
                n_hulls += 1
                ok, cverts = walker.hull_ok(child, verts, int(yy))
                if ok:
                    nxt[ckey] = (child, cverts)
        rows.append((gg, len(level), n_pruned))
        print(f"  D={lat.det} G={gg}: states {len(level)}, pruned {n_pruned}, hulls {n_hulls}, "
              f"max g_1 so far {best}", file=log, flush=True)
        level = nxt
    return rows, best, flagged, total


def walker_x(walker, kset):
    return [walker.lat.to_x(yy) for yy in walker.points(kset)]


def run_bfs(dets, gmin, max_states):
    reps = json.loads(Path(str(Path(__file__).resolve().parent.parent / "data" / "frame_lattices.json")).read_text())
    for rep in reps:
        if dets and rep["D"] not in dets:
            continue
        lat = Lattice(rep["D"], rep["H"])
        rows, best, flagged, total = bfs_lattice(lat, gmin, sys.stdout, max_states)
        print(f"D={rep['D']} box={rep['box_points']} |Stab|={len(lat.stab)}: total states {total}; "
              f"max g_1 (G >= {gmin}) = {best}; flagged g_1 >= 8: {[(ff[0], ff[1]) for ff in flagged]}", flush=True)



# ================================================================ part C (v0.40): TOP-DOWN from maximal sets (plan v2)
# VALID(K) := (i) and (iii) for S(K) (down-closed). Maximal valid sets are saturated (multilinearity of det; same hull).
# Maximal sets: BK over VALID with symmetry at the root (orbit representatives of the root candidates under Stab(L):
# every maximal M has an image containing a representative), shortcut (a): if S u Cand is valid it is the only maximal
# set of the branch, output iff no e in Excl extends it. Outputs de-duplicated by canonical form.
# Walk: levels by G from the top; children = remove one non-frame vertex pair (no validity test needed, L8 (3)).

def facets_and_vertices(xs):
    rays = ehr.extreme_rays([tuple([1] + list(vv)) for vv in xs])
    facets = sorted(set((tuple(-cc for cc in ray[1:]), ray[0]) for ray in rays))
    ehr.verify_facets(facets, xs)
    normals = np.array([ff[0] for ff in facets], dtype=np.int64)
    heights = np.array([ff[1] for ff in facets], dtype=np.int64)
    xarr = np.array(xs, dtype=np.int64)
    tight = (xarr @ normals.T) == heights[None, :]
    verts = sorted(set(tuple(xs[ii]) for ii in range(len(xs))
                       if ehr.rank_of([list(normals[jj]) for jj in np.flatnonzero(tight[ii])]) == 4))
    return facets, normals, heights, verts


class Searcher:
    def __init__(self, lat, gmin):
        self.lat, self.gmin = lat, gmin
        self.adm = Admissibility(lat)
        self.walker = Walker2(lat, self.adm)
        self.kneed = (gmin - 1) // 2 - 4
        self.hulls = 0

    def strict_inside(self, normals, heights):
        vals = self.walker.box_x @ normals.T
        return int((vals < heights[None, :]).all(axis=1).sum())

    def valid_add(self, kset, verts, yy):
        """VALID(K + y) given VALID(K): (i) by minors, (iii) by the hull of verts + {+-y}. Returns new vertices or None."""
        if addable_i(self.adm, kset, [yy]).size == 0:
            return None
        cls = self.lat.classes[yy]
        xs = list(verts) + [self.lat.to_x(cls), self.lat.to_x(tuple(-xx for xx in cls))]
        self.hulls += 1
        _f, normals, heights, nverts = facets_and_vertices(xs)
        return nverts if self.strict_inside(normals, heights) == 1 else None

    def valid_set(self, kset):
        """VALID(K) from scratch (used by the shortcut): (i) incrementally, (iii) by one hull. Returns vertices or None."""
        order = sorted(kset)
        for jj in range(1, len(order)):
            if addable_i(self.adm, frozenset(order[:jj]), [order[jj]]).size == 0:
                return None
        xs = [self.lat.to_x(yy) for yy in self.walker.points(frozenset(order))]
        self.hulls += 1
        _f, normals, heights, verts = facets_and_vertices(xs)
        return verts if self.strict_inside(normals, heights) == 1 else None

    def maximal_sets(self, log):
        k0 = frozenset(ii for ii, yy in enumerate(self.lat.classes) if sum(abs(xx) for xx in yy) == self.lat.det)
        verts0 = self.valid_set(k0)
        assert verts0 is not None, "R_L must be valid"
        cand0 = [yy for yy in range(len(self.lat.classes)) if yy not in k0 and self.valid_add(k0, verts0, yy) is not None]
        found = {}
        if not cand0:
            found[self.walker.canonical(k0)] = (k0, verts0)
            return found
        reps, seen = [], set()
        for yy in cand0:                                   # orbit representatives of cand0 under Stab(L)
            orb = set(int(xx) for xx in self.walker.class_perm[:, yy])
            if not orb & seen:
                reps.append(yy)
            seen |= orb
        print(f"  root: |R_L| classes {len(k0)}, root candidates {len(cand0)}, orbit reps {len(reps)}", file=log, flush=True)
        for xx in reps:
            kset = k0 | {xx}
            verts = self.valid_add(k0, verts0, xx)
            cand = [yy for yy in cand0 if yy != xx and self.valid_add(kset, verts, yy) is not None]
            self.bk(kset, verts, cand, [], found)
        return found

    def bk(self, kset, verts, cand, excl, found):
        if len(kset) + len(cand) < self.kneed:
            return
        whole = self.valid_set(kset | frozenset(cand)) if cand else verts
        if whole is not None:                             # shortcut (a)
            top = kset | frozenset(cand)
            if not any(self.valid_add(top, whole, ee) is not None for ee in excl):
                key = self.walker.canonical(top)
                found.setdefault(key, (top, whole))
            return
        cand = list(cand)
        done = []
        while cand:
            xx = cand.pop(0)
            nverts = self.valid_add(kset, verts, xx)
            assert nverts is not None
            nk = kset | {xx}
            ncand = [yy for yy in cand if self.valid_add(nk, nverts, yy) is not None]
            nexcl = [yy for yy in excl + done if self.valid_add(nk, nverts, yy) is not None]
            self.bk(nk, nverts, ncand, nexcl, found)
            done.append(xx)
            if len(kset) + len(cand) < self.kneed:
                return

    def case_iv(self, verts):
        """M(P) = {0}? u = H^{-1} s (s in {-1,0,1}^4) integral with |u.x| <= 1 on all vertices (x-coordinates)."""
        hm = self.lat.hmat
        for ss in itertools.product((-1, 0, 1), repeat=4):
            if not any(ss):
                continue
            uu = ehr.solve_exact([list(row) for row in hm], list(ss))        # H u = s  (rows of H are the frame v_i)
            if all(xx.denominator == 1 for xx in uu):
                ui = [int(xx) for xx in uu]
                if all(abs(sum(aa * bb for aa, bb in zip(ui, vv))) <= 1 for vv in verts):
                    return False
        return True

    def walk(self, maximal, log):
        """Top-down levels; returns per-level rows and the record lists."""
        frame_x = {self.lat.to_x(pp) for pp in self.walker.frame_pts}
        by_level = defaultdict_list()
        for key, (kset, verts) in maximal.items():
            by_level[1 + 2 * (4 + len(kset))][key] = kset
        top = max(by_level) if by_level else 0
        rows, rec = [], {"best_g1": None, "best_g2": None, "g1_8": [], "vol16": [], "caseIV_G49": [], "states": 0}
        gg = top
        while gg >= self.gmin:
            level = by_level.get(gg, {})
            nxt = by_level.setdefault(gg - 2, {})
            for key, kset in level.items():
                xs = [self.lat.to_x(yy) for yy in self.walker.points(kset)]
                facets, _n, _h, verts = facets_and_vertices(xs)
                self.hulls += 1
                k_closed, k_interior = ehr.sample_plan(4, 1)
                values = ehr.ehrhart_values(facets, verts, k_closed, k_interior)
                assert values[1] == len(xs) and values[-1] == 1, "walk state not saturated / not in W_4"
                coeffs, _chk = ehr.fit_polynomial(values, 4)
                rec["states"] += 1
                rec["best_g1"] = coeffs[1] if rec["best_g1"] is None else max(rec["best_g1"], coeffs[1])
                rec["best_g2"] = coeffs[2] if rec["best_g2"] is None else max(rec["best_g2"], coeffs[2])
                if coeffs[1] >= 8:
                    rec["g1_8"].append((gg, [str(cc) for cc in coeffs]))
                if coeffs[4] == 16:
                    rec["vol16"].append((gg, [str(cc) for cc in coeffs]))
                if gg >= 49 and self.case_iv(verts):
                    rec["caseIV_G49"].append((gg, [str(cc) for cc in coeffs]))
                if gg - 2 >= self.gmin:
                    xindex = {self.lat.to_x(self.lat.classes[kk]): kk for kk in kset}
                    xindex.update({self.lat.to_x(tuple(-cc for cc in self.lat.classes[kk])): kk for kk in kset})
                    for vv in verts:
                        if vv in frame_x:
                            continue
                        child = kset - {xindex[vv]}
                        ckey = self.walker.canonical(child)
                        if ckey not in nxt:
                            nxt[ckey] = child
            rows.append((gg, len(level)))
            print(f"  walk G={gg}: states {len(level)}, best g_1 {rec['best_g1']}, hulls so far {self.hulls}",
                  file=log, flush=True)
            gg -= 2
        return rows, rec


def defaultdict_list():
    from collections import defaultdict
    return defaultdict(dict)


def run_topdown(dets, gmin, log):
    reps = json.loads(Path(str(Path(__file__).resolve().parent.parent / "data" / "frame_lattices.json")).read_text())
    for rep in reps:
        if dets and rep["D"] not in dets:
            continue
        lat = Lattice(rep["D"], rep["H"])
        srch = Searcher(lat, gmin)
        maximal = srch.maximal_sets(log)
        sizes = sorted((1 + 2 * (4 + len(kk)) for kk, _v in maximal.values()), reverse=True)
        print(f"D={rep['D']} H={rep['H']} |Stab|={len(lat.stab)} box={rep['box_points']}: maximal sets (G >= {gmin}) "
              f"{len(maximal)}, sizes {sizes[:12]}, hulls {srch.hulls}", file=log, flush=True)
        rows, rec = srch.walk(maximal, log)
        print(f"RESULT D={rep['D']} H={rep['H']}: #maximal {len(maximal)}; #states G >= {gmin}: {rec['states']}; "
              f"max g_1 {rec['best_g1']}; max g_2 {rec['best_g2']}; g_1 >= 8: {rec['g1_8']}; vol = 16: {rec['vol16']}; "
              f"Case IV with G >= 49: {rec['caseIV_G49']}; hulls {srch.hulls}", file=log, flush=True)



# ================================================================ part D (v0.50): SANDWICH FACTORY restricted to W_4
# After Averkov-Schymura (Math. Program. 2023, sec. 5) / Averkov-Borger-Soprunov: sandwiches (A, B) of class sets,
# A <= B, both saturated, A VALID ((i) + (iii)), every y in B passes (i) with A. Branch on v in B \ A:
#   include: A' = conv(A u {+-v}) cap L (one hull; it also tests (iii)); if A' escapes B: dead; B' = (i)-reduction of B by A'
#   exclude: B'' = B minus v.
# Prune |B| < GMIN points. Leaf A = B: output if saturated (always, as A is built by saturation) and |A| >= GMIN.
# Each admissible saturated S >= R_L with G >= GMIN is on exactly one root-to-leaf path (membership decides each branch).
# Sandwiches are de-duplicated up to Stab(L) (canonical pair key).

class Sandwich:
    def __init__(self, lat, gmin):
        self.lat, self.gmin = lat, gmin
        self.srch = Searcher(lat, gmin)
        self.adm, self.walker = self.srch.adm, self.srch.walker
        self.kneed = (gmin - 1) // 2 - 4
        self.box_classes = self.box_class_map()
        self.norm = np.abs(self.lat.yarr).sum(axis=1)
        self.nodes = 0
        self.rank_prune = False
        self.rank_cut = 4
        self.branch_rule = "auto"
        self.dump = None
        self.n_rank_cut = 0
        self.dual_u = self.dual_candidates()

    def dual_candidates(self):
        """u in {-1,0,1}^4 \\ 0 lying in L* (u.y = 0 mod D on every coset y): the only possible members of M(S) (L9)."""
        out = [uu for uu in itertools.product((-1, 0, 1), repeat=4)
               if any(uu) and all(sum(aa * bb for aa, bb in zip(uu, ee)) % self.lat.det == 0 for ee in self.lat.cosets)]
        return np.array(out, dtype=np.int64).reshape(-1, 4)

    def branch_point(self, aset, bset, rest):
        """Branching point in B minus A. ANY choice keeps the sandwich complete (S contains v or not); the rule only
        changes speed. Alive u = in M(A) but not in M(B). Rules: norm = largest norm; fewest = a violator (in B minus A) of
        the alive u with the fewest violators; critical = like fewest but only over the alive u that would lift
        rank M(B) to the cut (u outside span M(B) while rank M(B) = cut - 1), else largest norm; hybrid = critical,
        else fewest; auto = v0.80
        (fewest in rank-cut-1 mode, norm otherwise)."""
        rule = self.branch_rule
        if rule == "auto":
            rule = "fewest" if (self.rank_prune and self.rank_cut == 1) else "norm"
        pool = self.alive_pool(aset, bset, rule) if (rule != "norm" and self.dual_u.size) else []
        if len(pool):
            rest_sorted = sorted(rest)
            viol = np.abs(self.lat.yarr[rest_sorted] @ self.dual_u[pool].T) > self.lat.det
            counts = viol.sum(axis=0)
            assert counts.min() >= 1, "an alive u (not in M(B)) has a violator in B, hence in B minus A"
            col = int(np.argmin(counts))
            choices = [rest_sorted[ii] for ii in np.flatnonzero(viol[:, col])]
            return max(choices, key=lambda yy: (int(self.norm[yy]), -yy))
        return max(rest, key=lambda yy: (int(self.norm[yy]), -yy))

    def alive_pool(self, aset, bset, rule):
        """Indices (into dual_u) of the alive candidates the rule may branch on."""
        in_a = (np.abs(self.lat.yarr[sorted(aset)] @ self.dual_u.T) <= self.lat.det).all(axis=0)
        in_b = (np.abs(self.lat.yarr[sorted(bset)] @ self.dual_u.T) <= self.lat.det).all(axis=0)
        alive = np.flatnonzero(in_a & ~in_b)
        if rule == "fewest":
            return alive
        members_b = [list(uu) for uu in self.dual_u[in_b]]
        rank_b = ehr.rank_of(members_b) if members_b else 0
        critical = np.array([], dtype=np.int64)
        if rank_b == self.rank_cut - 1:
            critical = np.array([ii for ii in alive if ehr.rank_of(members_b + [list(self.dual_u[ii])]) > rank_b],
                                dtype=np.int64)
        if rule == "hybrid" and not len(critical):
            return alive
        return critical

    def rank_m(self, kset):
        """rank of M(S) = {u in L* : |u.c| <= 1 on S} (the frame bounds |u_i| <= 1 are built into dual_u)."""
        if self.dual_u.size == 0:
            return 0
        if kset:
            vals = np.abs(self.lat.yarr[sorted(kset)] @ self.dual_u.T)
            members = self.dual_u[(vals <= self.lat.det).all(axis=0)]
        else:
            members = self.dual_u
        return ehr.rank_of([list(uu) for uu in members]) if len(members) else 0

    def box_class_map(self):
        """For each box point (row of walker.box_x): its class index, or -1 for 0 and the frame."""
        index = {yy: ii for ii, yy in enumerate(self.lat.classes)}
        out = []
        for yy in self.lat.box:
            neg = tuple(-xx for xx in yy)
            out.append(index.get(yy, index.get(neg, -1)))
        return np.array(out, dtype=np.int64)

    def saturate(self, avert, vclass):
        """conv(A u {+-v}) from A's vertices: returns (classes inside, #strict-inside box points, vertices)."""
        cls = self.lat.classes[vclass]
        xs = list(avert) + [self.lat.to_x(cls), self.lat.to_x(tuple(-xx for xx in cls))]
        _f, normals, heights, verts = facets_and_vertices(xs)
        vals = self.walker.box_x @ normals.T
        inside = (vals <= heights[None, :]).all(axis=1)
        strict = int((vals < heights[None, :]).all(axis=1).sum())
        inside_classes = frozenset(int(cc) for cc in self.box_classes[inside] if cc >= 0)
        return inside_classes, strict, verts

    def i_ok_extension(self, aset, new):
        """(i) for aset u new, given (i) for aset: add the new classes one by one."""
        cur = set(aset)
        for yy in sorted(new):
            if addable_i(self.adm, frozenset(cur), [yy]).size == 0:
                return False
            cur.add(yy)
        return True

    def reduce(self, aset, bset):
        rest = [yy for yy in bset if yy not in aset]
        keep = addable_i(self.adm, aset, rest) if rest else np.array([], dtype=np.int64)
        return frozenset(aset) | frozenset(int(xx) for xx in keep)

    def key(self, aset, bset):
        arr_a = np.array(sorted(aset), dtype=np.int64)
        arr_b = np.array(sorted(bset), dtype=np.int64)
        best = None
        for row in self.walker.class_perm:
            kk = (tuple(sorted(row[arr_a])) if arr_a.size else (), tuple(sorted(row[arr_b])))
            if best is None or kk < best:
                best = kk
        return best

    def run(self, log, node_budget):
        k0 = frozenset(ii for ii, yy in enumerate(self.lat.classes) if sum(abs(xx) for xx in yy) == self.lat.det)
        xs0 = [self.lat.to_x(yy) for yy in self.walker.points(k0)]
        _f, normals0, heights0, verts0 = facets_and_vertices(xs0)
        assert self.srch.strict_inside(normals0, heights0) == 1
        b0 = self.reduce(k0, frozenset(range(len(self.lat.classes))))
        stack = [(k0, b0, verts0)]
        seen = set()
        leaves = {}
        while stack:
            aset, bset, avert = stack.pop()
            if len(bset) < self.kneed:
                continue
            kk = self.key(aset, bset)
            if kk in seen:
                continue
            seen.add(kk)
            if self.rank_prune and self.rank_m(bset) >= self.rank_cut:   # L9: every S in [A, B] has rank M >= rank M(B)
                self.n_rank_cut += 1
                continue
            self.nodes += 1
            if self.nodes > node_budget:
                raise RuntimeError(f"node budget {node_budget} exceeded")
            if aset == bset:
                leaves.setdefault(self.walker.canonical(aset), (aset, avert))
                continue
            rest = [yy for yy in bset if yy not in aset]
            vv = self.branch_point(aset, bset, rest)
            # exclude branch
            stack.append((aset, bset - {vv}, avert))
            # include branch
            inside, strict, nvert = self.saturate(avert, vv)
            self.srch.hulls += 1
            if strict != 1 or not inside <= bset:
                continue
            new = inside - aset
            if not self.i_ok_extension(aset, new):
                continue
            stack.append((inside, self.reduce(inside, bset), nvert))
            if self.nodes % 2000 == 0:
                print(f"    nodes {self.nodes}, leaves {len(leaves)}, stack {len(stack)}, hulls {self.srch.hulls}",
                      file=log, flush=True)
        return leaves

    def evaluate(self, leaves):
        rec = {"states": 0, "best_g1": None, "best_g2": None, "g1_8": [], "vol16": [], "caseIV_G49": [],
               "per_G": {}, "rank": {}}
        for _key, (kset, _verts) in leaves.items():
            xs = [self.lat.to_x(yy) for yy in self.walker.points(kset)]
            facets, _n, _h, verts = facets_and_vertices(xs)
            k_closed, k_interior = ehr.sample_plan(4, 1)
            values = ehr.ehrhart_values(facets, verts, k_closed, k_interior)
            assert values[1] == len(xs) and values[-1] == 1, "leaf not saturated / not in W_4"
            coeffs, _chk = ehr.fit_polynomial(values, 4)
            gg = len(xs)
            rec["states"] += 1
            rec["per_G"][gg] = rec["per_G"].get(gg, 0) + 1
            rk = self.rank_m(kset)
            rec["rank"][rk] = rec["rank"].get(rk, 0) + 1
            rec["best_g1"] = coeffs[1] if rec["best_g1"] is None else max(rec["best_g1"], coeffs[1])
            rec["best_g2"] = coeffs[2] if rec["best_g2"] is None else max(rec["best_g2"], coeffs[2])
            if coeffs[1] >= 8:
                rec["g1_8"].append((gg, [str(cc) for cc in coeffs]))
            if coeffs[4] == 16:
                rec["vol16"].append((gg, [str(cc) for cc in coeffs]))
            if gg >= 49 and self.srch.case_iv(verts):
                rec["caseIV_G49"].append((gg, [str(cc) for cc in coeffs]))
            if self.dump is not None:
                self.dump.write(json.dumps({"D": self.lat.det, "G": gg, "rank": rk, "coeffs": [str(cc) for cc in coeffs],
                                            "points_x": [list(map(int, xx)) for xx in xs]}) + "\n")
        return rec


def run_sandwich(dets, gmin, log, node_budget, only_index, rank_prune=False, rank_cut=4, branch_rule="auto",
                 dump_path=None):
    import time
    reps = json.loads(Path(str(Path(__file__).resolve().parent.parent / "data" / "frame_lattices.json")).read_text())
    for num, rep in enumerate(reps):
        if dets and rep["D"] not in dets:
            continue
        if only_index is not None and num != only_index:
            continue
        lat = Lattice(rep["D"], rep["H"])
        sw = Sandwich(lat, gmin)
        sw.rank_prune = rank_prune
        sw.rank_cut = rank_cut
        sw.branch_rule = branch_rule
        sw.dump = open(dump_path, "a") if dump_path else None
        t_start = time.time()
        leaves = sw.run(log, node_budget)
        rec = sw.evaluate(leaves)
        if sw.dump is not None:
            sw.dump.close()
        secs = time.time() - t_start
        print(f"RESULT #{num} D={rep['D']} H={rep['H']} |Stab|={len(lat.stab)} box={rep['box_points']}: nodes {sw.nodes}; "
              f"leaves (classes, G >= {gmin}) {rec['states']} per G {dict(sorted(rec['per_G'].items()))}; "
              f"max g_1 {rec['best_g1']}; max g_2 {rec['best_g2']}; g_1 >= 8: {rec['g1_8']}; vol 16: {rec['vol16']}; "
              f"Case IV G >= 49: {rec['caseIV_G49']}; hulls {sw.srch.hulls}; rank M histogram {dict(sorted(rec['rank'].items()))}; "
              f"rank_prune {rank_prune} cut-at-rank>={rank_cut} (cuts {sw.n_rank_cut}); seconds {secs:.0f}", file=log, flush=True)


if __name__ == "__main__":
    main()
