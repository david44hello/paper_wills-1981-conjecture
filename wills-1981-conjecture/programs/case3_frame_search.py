#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# case3_frame_search.py - Case III, first program: the search of case3_maximal_sets.py with the cut at rank M(S) > K
## version 0.50 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# M(S) = {u in Z^4 : |u.x| <= 1 for all x in S}. S contains +-v_i (rows of V), so V u in {-1,0,1}^4: at most 81 candidates u.
# S <= S' => M(S') <= M(S) => rank M(S') <= rank M(S): {rank 4} is DOWNWARD closed (Case I + II), {rank <= 3} UPWARD closed.
# BK cut: node (S, Cand) with rank M(S u Cand) = 4 -> every maximal set of the branch lies in S u Cand -> rank 4 -> cut.
#   (M depends only on conv, so the shortcut set sat(S u Cand) has the same rank as S u Cand.)
# Walk cut: a child of rank 4 is neither counted nor expanded (all its subsets have rank 4).
# Every rank <= 3 state lies under a rank <= 3 maximal set, and the top-down path between them keeps rank <= 3: nothing is lost.
# Cross-checks: --test (D = 1, D = 2: pruned count = unpruned rank <= 3 count; rank = maximal_members.l6_case rank on every state).
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 case3_frame_search.py --only 4 5 --rank-prune on --out x.jsonl --check-l6 0
from pathlib import Path
import argparse
import itertools
import json
import time
from fractions import Fraction

import numpy as np
from scipy.spatial import ConvexHull

from frame_census import my_frame
from generic_walk import invariants
from maximal_members import l6_case
from case3_maximal_sets import MaxSets

LLIST = str(Path(__file__).resolve().parent.parent / "data" / "frame_lattices.json")
FULL_RANK = 4
CACHE_MAX = 2_000_000  # saturate_valid cache entries (packed bits, ~200 bytes each); cleared when full


def dual_candidates(vmat):
    """All integer u with V u in {-1,0,1}^4 (rows of V = frame vectors v_i), exact."""
    out = []
    for w in itertools.product((-1, 0, 1), repeat=4):
        u = np.rint(np.linalg.solve(vmat.astype(float), np.array(w, dtype=float))).astype(np.int64)
        if np.array_equal(vmat @ u, np.array(w)):
            out.append(u)
    return np.array(out, dtype=np.int64)


class RankMaxSets(MaxSets):
    def __init__(self, hmat, max_rank):
        assert type(max_rank) is int and 0 <= max_rank <= FULL_RANK, f"max_rank must be an int 0..4, got {max_rank!r}"
        super().__init__(hmat)
        self.max_rank = max_rank
        self.dual = dual_candidates(self.vmat)
        self.frame_dual = self.frame @ self.dual.T
        self.rank_cuts_bk = 0
        self.sat_cache = {}
        self.cache_hits = 0
        self.det_rejects = 0

    def saturate_valid(self, mask):
        """pathc3 saturate_valid with a cache keyed by the packed mask (self.hulls counts real hulls only)."""
        key = np.packbits(mask).tobytes()
        if key in self.sat_cache:
            self.cache_hits += 1
            packed = self.sat_cache[key]
            return None if packed is None else np.unpackbits(packed, count=self.size).astype(bool)
        sat = super().saturate_valid(mask)
        if len(self.sat_cache) >= CACHE_MAX:
            self.sat_cache.clear()
        self.sat_cache[key] = None if sat is None else np.packbits(sat)
        return sat

    def triple_normals(self, mask):
        """Integer k (one per triple a, b, c of vertex reps of conv S) with k.x = det(x, a, b, c)."""
        pts = self.frame[mask]
        verts = pts[ConvexHull(pts.astype(float)).vertices]
        reps = np.array(sorted({tuple(v) if tuple(v) > tuple(-v) else tuple(-v) for v in verts}), dtype=float)
        tri = reps[np.array(list(itertools.combinations(range(len(reps)), 3)))]
        cof = np.stack([((-1) ** col) * np.linalg.det(np.delete(tri, col, axis=2)) for col in range(4)], axis=1)
        return np.rint(cof).astype(np.int64)

    def addable(self, mask, pool):
        """Exact pre-filter: x with |det(x, a, b, c)| > D for vertex reps a, b, c of S makes S u {+-x} invalid (no hull)."""
        pool = [x for x in pool if not mask[x]]
        if not pool:
            return {}
        worst = np.max(np.abs(self.frame[pool] @ self.triple_normals(mask).T), axis=1)
        survivors = [x for x, value in zip(pool, worst) if value <= self.det]
        self.det_rejects += len(pool) - len(survivors)
        return super().addable(mask, survivors)

    def m_rank(self, mask):
        inside = np.all(np.abs(self.frame_dual[mask]) <= 1, axis=0)
        members = self.dual[inside]
        return int(np.linalg.matrix_rank(members.astype(float))) if np.any(members) else 0

    def bk(self, mask, cand, excl, found):
        if self.max_rank < FULL_RANK and self.m_rank(self.with_pairs(mask, list(cand))) > self.max_rank:
            self.rank_cuts_bk += 1
            return
        super().bk(mask, self.killers_first(mask, cand), excl, found)

    def killers_first(self, mask, cand):
        """cand re-ordered: most alive u (u in M(S)) killed first; stable for ties. BK is exact in any order."""
        if not cand:
            return cand
        alive = np.all(np.abs(self.frame_dual[mask]) <= 1, axis=0)
        keys = list(cand)
        kills = (np.abs(self.frame_dual[keys][:, alive]) > 1).sum(axis=1)
        return {keys[j]: cand[keys[j]] for j in sorted(range(len(keys)), key=lambda j: -kills[j])}

    def walk_down(self, maximal, min_g, check_l6):
        """Top-down walk from the maximal sets (keeping +-v_i); sets with rank M > max_rank are cut."""
        seen = dict(maximal)
        frontier = dict(maximal)
        st = dict(evaluated=0, by_rank={}, g1_by_rank={}, g2_by_rank={}, best_g1=Fraction(-99), best_g2=Fraction(-99), best_g1_le3=Fraction(-99),
                  best_g2_le3=Fraction(-99), flagged=[], vol16=[], case4_G49=[], rank_cut_walk=0, l6_checked=0)
        while frontier:
            nxt = {}
            for mask in frontier.values():
                vidx = self.record(mask, min_g, check_l6, st)
                for v in {min(i, self.neg[i]) for i in np.flatnonzero(mask)[vidx]}:
                    if self.frame_vertex[v]:
                        continue
                    child = mask.copy()
                    child[v] = child[self.neg[v]] = False
                    if child.sum() < min_g:
                        continue
                    ckey = self.canon_key(child)
                    if ckey in seen:
                        continue
                    seen[ckey] = child
                    if self.max_rank < FULL_RANK and self.m_rank(child) > self.max_rank:
                        st["rank_cut_walk"] += 1
                        continue
                    nxt[ckey] = child
            frontier = nxt
        st["states"] = len(seen) - st["rank_cut_walk"]
        return st

    def record(self, mask, min_g, check_l6, st):
        pts = self.frame[mask]
        (count, vol, g3, g1, g2), vidx = invariants(pts, np.ones(len(pts), dtype=bool))
        if count < min_g:
            return vidx
        rank = self.m_rank(mask)
        if st["l6_checked"] < check_l6 or count >= 49:
            assert l6_case(pts)[1] == rank, f"m_rank {rank} != l6_case rank {l6_case(pts)}"
            st["l6_checked"] += 1
        st["evaluated"] += 1
        st["by_rank"][rank] = st["by_rank"].get(rank, 0) + 1
        st["g1_by_rank"][rank] = max(st["g1_by_rank"].get(rank, Fraction(-99)), g1)
        st["g2_by_rank"][rank] = max(st["g2_by_rank"].get(rank, Fraction(-99)), g2)
        st["best_g1"], st["best_g2"] = max(st["best_g1"], g1), max(st["best_g2"], g2)
        if rank < FULL_RANK:
            st["best_g1_le3"], st["best_g2_le3"] = max(st["best_g1_le3"], g1), max(st["best_g2_le3"], g2)
        if g1 >= 8 or g2 >= 24:
            st["flagged"].append((count, str(g1), str(g2), str(vol), rank))
        if vol == 16:
            st["vol16"].append((count, str(g1), rank))
        if count >= 49 and rank == 0:
            st["case4_G49"].append((count, str(g1), str(vol)))
        return vidx


def run_lattice(idx, entry, max_rank, min_g, check_l6):
    hmat = my_frame(entry)
    solver = RankMaxSets(hmat, max_rank)
    t0 = time.time()
    maximal = solver.find_maximal()
    t1 = time.time()
    walk = solver.walk_down(maximal, min_g, check_l6)
    max_ranks = {}
    for mask in maximal.values():
        rr = solver.m_rank(mask)
        max_ranks[rr] = max_ranks.get(rr, 0) + 1
    return dict(idx=idx, D=entry["D"], H=hmat.tolist(), rank_prune=max_rank < FULL_RANK, max_rank=max_rank,
                frame=solver.size, stab=len(solver.perms),
                n_maximal=len(maximal), maximal_by_rank=max_ranks, max_sizes=sorted(int(m.sum()) for m in maximal.values())[-3:],
                states_G31=walk["evaluated"], by_rank=walk["by_rank"], states=walk["states"],
                max_g1_by_rank={rr: str(v) for rr, v in walk["g1_by_rank"].items()},
                max_g2_by_rank={rr: str(v) for rr, v in walk["g2_by_rank"].items()},
                max_g1=str(walk["best_g1"]), max_g2=str(walk["best_g2"]), max_g1_rank_le3=str(walk["best_g1_le3"]),
                max_g2_rank_le3=str(walk["best_g2_le3"]), flagged=walk["flagged"], vol16=sorted(set(walk["vol16"])),
                case4_G49=walk["case4_G49"], hulls=solver.hulls, cache_hits=solver.cache_hits, det_rejects=solver.det_rejects,
                rank_cuts_bk=solver.rank_cuts_bk,
                rank_cut_walk=walk["rank_cut_walk"], l6_checked=walk["l6_checked"],
                sec_max=round(t1 - t0, 1), sec_walk=round(time.time() - t1, 1))


def main_runs(only, max_rank, min_g, check_l6, out):
    entries = json.load(open(LLIST))
    for idx in only:
        row = run_lattice(idx, entries[idx], max_rank, min_g, check_l6)
        with open(out, "a") as fh:
            fh.write(json.dumps(row) + "\n")
        print(json.dumps(row)[:400], flush=True)


def main_test():
    """#0 (D = 1, all rank 4), #1 (D = 2), #38 (D = 18, X = Case IV): every pruned count = the matching part of the full run."""
    entries = json.load(open(LLIST))
    for idx in (0, 1, 38):
        off = run_lattice(idx, entries[idx], FULL_RANK, 1, 10 ** 6)
        assert off["l6_checked"] == off["states_G31"]
        for max_rank in (3, 0):
            on = run_lattice(idx, entries[idx], max_rank, 1, 10 ** 6)
            expected = sum(cnt for rr, cnt in off["by_rank"].items() if rr <= max_rank)
            print(f"#{idx} D={off['D']}: full {off['states_G31']} by rank {off['by_rank']}; max_rank {max_rank}: "
                  f"{on['states_G31']} by rank {on['by_rank']}; hulls full {off['hulls']} pruned {on['hulls']}")
            assert on["states_G31"] == expected and all(rr <= max_rank for rr in on["by_rank"]), "prune lost or kept wrong sets"
    print("TEST PASS")


def main():
    parser = argparse.ArgumentParser(description="Path C program 1 with the L9 rank prune")
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--only", type=int, nargs="+", help="frame_lattices.json indices #0..#38")
    parser.add_argument("--max-rank", type=int, choices=range(FULL_RANK + 1),
                        help="keep sets with rank M(S) <= this: 3 = L9 mode, 0 = Case IV only, 4 = no prune")
    parser.add_argument("--min-g", type=int)
    parser.add_argument("--check-l6", type=int, help="cross-check m_rank with l6_case on the first N states (and all G >= 49)")
    parser.add_argument("--out")
    args = parser.parse_args()
    if args.test:
        main_test()
        return
    if None in (args.only, args.max_rank, args.min_g, args.check_l6, args.out):
        parser.error("--only, --max-rank, --min-g, --check-l6 and --out are all required (no defaults)")
    main_runs(args.only, args.max_rank, args.min_g, args.check_l6, args.out)


if __name__ == "__main__":
    main()
