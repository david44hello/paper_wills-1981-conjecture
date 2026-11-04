#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# case3_reverse_search.py - Case III, first program: reverse search per frame lattice; exact integer facets (fast_facets)
## version 0.20 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# States: saturated cs S (frame points; all lattice points of conv S lie in the frame) containing C_L = sat conv{+-v_i},
#   (i) every 4 points |det| <= D, (iii) int conv S cap Z^4 = {0}. Up to Stab(L) (signed perms of frame coordinates fixing L).
# parent(S) = canon(S minus its canonical vertex pair) - the vertex pair (outside +-v_i) of smallest index in canonical S.
# Omega(S) = pair reps x with S u {+-x} passing (i) and (iii); Omega(child) is inside Omega(S) (monotone), so it is inherited.
# Prune: |S| + 2|Omega(S)| < MIN_G => no descendant reaches MIN_G. g_1, g_2 computed only for G >= MIN_G (n = 4 identities).
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 case3_reverse_search.py --index 9 --which 0 --max-seconds 840
import argparse
import itertools
import sys
import time
from fractions import Fraction

import numpy as np
from scipy.spatial import ConvexHull

from dual_lattice_l1 import min_l1_dual
from case2_walk import hnf_lattices
from case3_frame_setup import frame_setup


def fast_facets(points):
    """Exact integer facets (a, b), a.x <= b, of conv(points); 0 interior assumed. One batch of 3x3 dets."""
    hull = ConvexHull(points.astype(float))
    simp = points[hull.simplices]
    diffs = (simp[:, 1:, :] - simp[:, :1, :]).astype(float)
    cof = np.stack([((-1) ** c) * np.rint(np.linalg.det(np.delete(diffs, c, axis=2))) for c in range(4)], axis=1)
    cof = cof.astype(np.int64)
    gcd = np.gcd.reduce(np.abs(cof), axis=1)
    keep = gcd > 0
    cof, simp, gcd = cof[keep] // gcd[keep][:, None], simp[keep], gcd[keep]
    rhs = np.einsum("ij,ij->i", cof, simp[:, 0, :])
    sign = np.where(rhs < 0, -1, 1)
    cof, rhs = cof * sign[:, None], rhs * sign
    assert np.all(rhs > 0), "origin on a facet"
    uniq, idx = np.unique(np.hstack([cof, rhs[:, None]]), axis=0, return_index=True)
    return uniq[:, :4], uniq[:, 4], hull


class PathC:
    def __init__(self, hmat, min_g):
        self.frame, self.neg, self.perms, self.det, self.vmat = frame_setup(hmat)
        self.size = len(self.frame)
        self.min_g = min_g
        lookup = {tuple(p): i for i, p in enumerate(self.frame)}
        self.frame_vertex = np.zeros(self.size, dtype=bool)
        for v in np.vstack([self.vmat, -self.vmat]):
            self.frame_vertex[lookup[tuple(v)]] = True
        self.stats = dict(states=0, pruned=0, maximal=0, child_tests=0, hulls_child=0, t_child=0.0, t_rest=0.0,
                          evaluated=0, best_g1=Fraction(-99), best_g2=Fraction(-99), flagged=[])

    def canon(self, mask):
        images = np.zeros((len(self.perms), self.size), dtype=bool)
        images[np.arange(len(self.perms))[:, None], self.perms] = mask[None, :]
        packed = np.packbits(images, axis=1)
        best = min(range(len(self.perms)), key=lambda g: packed[g].tobytes())
        return images[best], self.perms[best], packed[best].tobytes()

    def vertex_pairs(self, mask):
        hull = ConvexHull(self.frame[mask].astype(float))
        idx = np.flatnonzero(mask)[hull.vertices]
        return sorted({min(i, self.neg[i]) for i in idx}), hull

    def parent_key(self, mask):
        pairs, _ = self.vertex_pairs(mask)
        free = [p for p in pairs if not self.frame_vertex[p]]
        rep = free[0]
        child = mask.copy()
        child[rep] = child[self.neg[rep]] = False
        return self.canon(child)[2]

    def evaluate(self, mask):
        from generic_walk import invariants
        pts = self.frame[mask]
        (count, vol, g3, g1, g2), _ = invariants(pts, np.ones(len(pts), dtype=bool))
        st = self.stats
        st["evaluated"] += 1
        st["best_g1"], st["best_g2"] = max(st["best_g1"], g1), max(st["best_g2"], g2)
        if g1 >= 8 or g2 >= 24:
            st["flagged"].append((count, str(g1), str(g2), np.flatnonzero(mask).tolist()))

    def run(self, max_seconds):
        start_pts = np.vstack([self.vmat, -self.vmat])
        normals, rhs, _ = fast_facets(start_pts)
        root = np.all(self.frame @ normals.T <= rhs, axis=1)
        root, _, root_key = self.canon(root)
        omega0 = [i for i in range(self.size) if i < self.neg[i] and not root[i]]
        self.deadline = time.time() + max_seconds
        stack = [(root, root_key, omega0)]
        while stack and time.time() < self.deadline:
            mask, key, omega_parent = stack.pop()
            stack.extend(self.expand(mask, key, omega_parent))
        self.stats["complete"] = not stack
        return self.stats

    def expand(self, mask, key, omega_parent):
        st = self.stats
        t0 = time.time()
        st["states"] += 1
        count = int(mask.sum())
        pairs, hull = self.vertex_pairs(mask)
        reps = self.frame[[p for p in pairs]].astype(float)
        triples = np.array(list(itertools.combinations(range(len(reps)), 3)))
        tri = reps[triples]  # (t, 3, 4)
        kvec = np.stack([((-1) ** c) * np.linalg.det(np.delete(tri, c, axis=2)) for c in range(4)], axis=1)
        if count >= self.min_g:
            self.evaluate(mask)
        t1 = time.time()
        st["t_rest"] += t1 - t0
        omega, sat_children = [], []
        base = self.frame[mask]
        for x in omega_parent:
            if mask[x]:
                continue
            st["child_tests"] += 1
            if np.max(np.abs(kvec @ self.frame[x])) > self.det + 1e-6:
                continue
            st["hulls_child"] += 1
            normals, rhs, _ = fast_facets(np.vstack([base, self.frame[x], -self.frame[x]]))
            values = self.frame @ normals.T
            if np.all(values < rhs, axis=1).sum() != 1:
                continue
            omega.append(x)
            inside = np.all(values <= rhs, axis=1)
            if inside.sum() == count + 2:
                sat_children.append(x)
        st["t_child"] += time.time() - t1
        if not omega:
            st["maximal"] += 1
            return []
        if count + 2 * len(omega) < self.min_g:
            st["pruned"] += 1
            return []
        t2 = time.time()
        out, seen_children = [], set()
        for x in sat_children:
            child = mask.copy()
            child[x] = child[self.neg[x]] = True
            cmask, perm, ckey = self.canon(child)
            if ckey in seen_children or self.parent_key(cmask) != key:
                continue
            seen_children.add(ckey)
            # perm maps old index i -> perm[i] (images[g][perm[g][i]] = mask[i]); carry Omega into canonical coordinates
            mapped = sorted({min(perm[i], self.neg[perm[i]]) for i in omega if i != x})
            out.append((cmask, ckey, mapped))
        st["t_rest"] += time.time() - t2
        return out


def main():
    parser = argparse.ArgumentParser(description="PATH C program 1: reverse search")
    parser.add_argument("--index", type=int, required=True)
    parser.add_argument("--which", type=int, required=True)
    parser.add_argument("--max-seconds", type=float, required=True)
    parser.add_argument("--min-g", type=int, default=31)
    args = parser.parse_args()
    valid = [h for h in hnf_lattices(args.index) if min_l1_dual(h, args.index)[0] >= 1]
    hmat = valid[args.which]
    solver = PathC(hmat, args.min_g)
    t0 = time.time()
    stats = solver.run(args.max_seconds)
    stats["seconds"] = round(time.time() - t0, 1)
    stats["states_per_s"] = round(stats["states"] / max(stats["seconds"], 1e-9), 2)
    flagged = stats.pop("flagged")
    print(f"D={args.index} frame #{args.which} H={hmat.tolist()} frame_pts={solver.size} |Stab|={len(solver.perms)}: {stats}")
    print(f"flagged (g1 >= 8 or g2 >= 24): {len(flagged)}", flagged[:3])


if __name__ == "__main__":
    main()
