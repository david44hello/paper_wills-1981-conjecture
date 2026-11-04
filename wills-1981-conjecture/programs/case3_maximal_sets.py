#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# case3_maximal_sets.py - Case III, first program: all maximal admissible sets per frame lattice by branching, then the top-down walk
## version 0.20 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# valid(set) := its saturation (frame points in the hull) has only 0 inside and every 4 points |det| <= D. Hereditary on
# saturated sets, so maximal sets are found by BK on (S, Cand, Excl), Cand/Excl = pairs addable to S alone:
#   shortcut: sat(S u Cand) valid -> it is the branch's only maximal set (output unless some e in Excl extends it);
#   prune: sat(S u Cand u {e}) valid for some e in Excl -> cut; a child whose saturation contains an Excl pair -> cut.
# Raw (non-symmetric) maximal sets are deduped by canonical key at the end. Top-down children need no W_4 test.
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 case3_maximal_sets.py --index 1 --which 0 --min-g 1
import argparse
import itertools
import time
from fractions import Fraction

import numpy as np
from scipy.spatial import ConvexHull

from dual_lattice_l1 import min_l1_dual
from case2_walk import hnf_lattices
from case3_frame_setup import frame_setup
from case3_reverse_search import fast_facets
from generic_walk import invariants
from maximal_members import l6_case


class MaxSets:
    def __init__(self, hmat):
        self.frame, self.neg, self.perms, self.det, self.vmat = frame_setup(hmat)
        self.size = len(self.frame)
        lookup = {tuple(p): i for i, p in enumerate(self.frame)}
        self.frame_vertex = np.zeros(self.size, dtype=bool)
        for v in np.vstack([self.vmat, -self.vmat]):
            self.frame_vertex[lookup[tuple(v)]] = True
        self.hulls = 0

    def saturate_valid(self, mask):
        """Saturated mask of conv(frame[mask]) if valid (only 0 inside, all 4-dets <= D), else None."""
        self.hulls += 1
        normals, rhs, hull = fast_facets(self.frame[mask])
        values = self.frame @ normals.T
        if np.all(values < rhs, axis=1).sum() != 1:
            return None
        sat = np.all(values <= rhs, axis=1)
        verts = self.frame[mask][hull.vertices]
        reps = np.array(sorted({tuple(v) if tuple(v) > tuple(-v) else tuple(-v) for v in verts}), dtype=float)
        if len(reps) >= 4:
            quads = np.array(list(itertools.combinations(range(len(reps)), 4)))
            if np.max(np.abs(np.linalg.det(reps[quads]))) > self.det + 1e-6:
                return None
        return sat

    def with_pairs(self, mask, pairs):
        out = mask.copy()
        for x in pairs:
            out[x] = out[self.neg[x]] = True
        return out

    def addable(self, mask, pool):
        """Pairs in pool (not in mask) whose single addition keeps validity, with the saturated result."""
        res = {}
        for x in pool:
            if mask[x]:
                continue
            sat = self.saturate_valid(self.with_pairs(mask, [x]))
            if sat is not None:
                res[x] = sat
        return res

    def canon_key(self, mask):
        images = np.zeros((len(self.perms), self.size), dtype=bool)
        images[np.arange(len(self.perms))[:, None], self.perms] = mask[None, :]
        return min(row.tobytes() for row in np.packbits(images, axis=1))

    def find_maximal(self):
        root = self.saturate_valid(np.vstack([self.frame_vertex]).reshape(-1))
        pool = [i for i in range(self.size) if i < self.neg[i] and not root[i]]
        cand = self.addable(root, pool)
        found = {}
        self.bk(root, cand, {}, found)
        return found

    def bk(self, mask, cand, excl, found):
        if not cand:
            if not excl:
                found.setdefault(self.canon_key(mask), mask)
            return
        top = self.saturate_valid(self.with_pairs(mask, list(cand)))
        if top is not None:  # shortcut: the only maximal set of this branch
            if not any(top[e] for e in excl) and not self.addable(top, list(excl)):
                found.setdefault(self.canon_key(top), top)
            return
        cand_items = list(cand.items())
        excl = dict(excl)
        remaining = dict(cand)
        stab = self.perms[np.all(mask[self.perms] == mask[None, :], axis=1)]  # g with g(S) = S (perm acts on indices)
        covered = set()
        for x, child in cand_items:
            del remaining[x]
            if x in covered:  # a symmetric image of an earlier branch: covered by symmetry, goes to Excl
                excl[x] = child
                continue
            covered.update(int(min(g[x], self.neg[g[x]])) for g in stab)
            if any(child[e] for e in excl):
                excl[x] = child
                continue
            pool = [y for y in list(remaining) + list(excl) if not child[y]]
            ok = self.addable(child, pool)
            c_cand = {y: s for y, s in ok.items() if y in remaining}
            c_excl = {y: s for y, s in ok.items() if y in excl}
            self.bk(child, c_cand, c_excl, found)
            excl[x] = child

    def walk_down(self, maximal, min_g):
        """Union of top-down walks from all maximal sets (children: remove a vertex pair outside +-v_i)."""
        seen = {}
        frontier = {}
        for key, mask in maximal.items():
            frontier[key] = mask
        seen.update(frontier)
        best1, best2, flagged, vol16, case4 = Fraction(-99), Fraction(-99), [], [], []
        evaluated = 0
        while frontier:
            nxt = {}
            for key, mask in frontier.items():
                pts = self.frame[mask]
                (count, vol, g3, g1, g2), vidx = invariants(pts, np.ones(len(pts), dtype=bool))
                if count >= min_g:
                    evaluated += 1
                    best1, best2 = max(best1, g1), max(best2, g2)
                    if g1 >= 8 or g2 >= 24:
                        flagged.append((count, str(g1), str(g2), str(vol)))
                    if vol == 16:
                        vol16.append((count, str(g1)))
                    if count >= 49 and l6_case(pts)[0] == "IV":
                        case4.append((count, str(g1), str(vol)))
                for v in {min(i, self.neg[i]) for i in np.flatnonzero(mask)[vidx]}:
                    if self.frame_vertex[v]:
                        continue
                    child = mask.copy()
                    child[v] = child[self.neg[v]] = False
                    if child.sum() < min_g:
                        continue
                    ckey = self.canon_key(child)
                    if ckey not in seen:
                        seen[ckey] = child
                        nxt[ckey] = child
            frontier = nxt
        return dict(states=len(seen), evaluated=evaluated, best_g1=best1, best_g2=best2, flagged=flagged,
                    vol16=sorted(set(vol16)), case4_G49=case4)


def main():
    parser = argparse.ArgumentParser(description="PATH C plan v2, program 1")
    parser.add_argument("--index", type=int, required=True)
    parser.add_argument("--which", type=int, required=True)
    parser.add_argument("--min-g", type=int, default=31)
    args = parser.parse_args()
    valid = [h for h in hnf_lattices(args.index) if min_l1_dual(h, args.index)[0] >= 1]
    hmat = valid[args.which]
    solver = MaxSets(hmat)
    t0 = time.time()
    maximal = solver.find_maximal()
    t1 = time.time()
    sizes = sorted(int(m.sum()) for m in maximal.values())
    print(f"D={args.index} #{args.which} H={hmat.tolist()} frame={solver.size} |Stab|={len(solver.perms)}: "
          f"#maximal (up to Stab) = {len(maximal)}, sizes {sizes}, hulls {solver.hulls}, {t1 - t0:.1f} s", flush=True)
    walk = solver.walk_down(maximal, args.min_g)
    print(f"  walk (G >= {args.min_g}): {walk}, {time.time() - t1:.1f} s")


if __name__ == "__main__":
    main()
