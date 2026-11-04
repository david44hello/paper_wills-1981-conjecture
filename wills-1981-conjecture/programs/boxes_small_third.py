#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# boxes_small_third.py - the small boxes, third program: exact count of rank-3 and rank-4 point sets per G, no symmetry
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# Walk over POINT SETS (no symmetry), children = remove an EXACT vertex pair (integer facets, rank-4 active normals), with the
# full walk (no cut); per G: all sets, rank 3, rank 4; plus the sets a cut walk would visit (rank-4 sets not expanded).
from pathlib import Path
import os
for _var in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_var] = "1"
import json
import sys
from collections import defaultdict

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ehrhart_count as ehr                    # noqa: E402
import width2_survey as sv            # noqa: E402

BOX_FILE = str(Path(__file__).resolve().parent.parent / "data" / "boxes.jsonl")


def exact_vertices(pts):
    facets = ehr.facets_of(pts)
    return [pp for pp in pts if ehr.rank_of([list(nn) for nn, hh in facets
                                             if sum(aa * bb for aa, bb in zip(nn, pp)) == hh]) == 4]


def rank_m(pts):
    dirs = sv.width2_directions(pts)
    return ehr.rank_of([list(uu) for uu in dirs]) if dirs else 0


def children(pset):
    pts = sorted(pset)
    for vv in exact_vertices(pts):
        neg = tuple(-xx for xx in vv)
        if vv < neg:
            child = pset - {vv, neg}
            if ehr.rank_of([list(pp) for pp in child]) == 4:
                yield child


def walk(points, gmin):
    level = {frozenset(points)}
    rows = {}
    reach_cut = {frozenset(points)}          # sets the CUT walk visits
    while level:
        gg = len(next(iter(level)))
        nxt, nxt_cut, stats = set(), set(), defaultdict(int)
        for pset in level:
            rk = rank_m(sorted(pset))
            stats[f"rank{rk}"] += 1
            visited = pset in reach_cut
            stats["visited_cut"] += visited
            kids = list(children(pset)) if gg - 2 >= gmin else []
            nxt.update(kids)
            if visited and rk == 3:
                nxt_cut.update(kids)
        rows[gg] = dict(stats, all=len(level))
        level, reach_cut = nxt, nxt_cut
    return rows


def main():
    lines = open(BOX_FILE).read().splitlines()
    for index in (4, 5):
        points = [tuple(pp) for pp in json.loads(lines[index])["points_wt"]]
        rows = walk(points, 31)
        for gg in sorted(rows, reverse=True):
            print(f"box {index} G {gg}: {rows[gg]}", flush=True)
        tot = lambda key: sum(rr.get(key, 0) for rr in rows.values())
        print(f"box {index} TOTAL: all {tot('all')}, rank 3 {tot('rank3')}, rank 4 {tot('rank4')}, "
              f"visited by the cut walk {tot('visited_cut')}", flush=True)


if __name__ == "__main__":
    main()
