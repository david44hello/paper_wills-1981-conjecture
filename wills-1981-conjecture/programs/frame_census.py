#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# frame_census.py - census of maximal sets per frame lattice; the frame of a set (used to re-check each frame lattice)
## version 0.10 - 20261102 - the version used for the runs reported in the paper
from pathlib import Path
import json
import random
from collections import Counter

import numpy as np

from dual_lattice_l1 import min_l1_dual
from case3_frame_setup import frame_setup
from ehrhart_exact import facets_of
from maximal_members import l6_case
from generic_walk import invariants
from scipy.spatial import ConvexHull
import itertools


def my_frame(entry):
    for cand in (np.array(entry["H"]), np.array(entry["H"]).T):
        if min_l1_dual(cand, entry["D"])[0] >= 1:
            return cand
    raise SystemExit(f"neither H nor H^T passes the W_4 test: {entry}")


def grow_once(frame, neg, det, vmat, rng):
    def saturate(points):
        normals, rhs = facets_of(points)
        values = frame @ normals.T
        if np.all(values < rhs, axis=1).sum() != 1:
            return None
        return np.all(values <= rhs, axis=1)

    def det_ok(mask, new_pt):
        pts = frame[mask]
        verts = pts[ConvexHull(pts.astype(float)).vertices]
        reps = np.array(sorted({tuple(v) if tuple(v) > tuple(-v) else tuple(-v) for v in verts}), dtype=float)
        triples = np.array(list(itertools.combinations(range(len(reps)), 3)))
        stack = np.concatenate([np.repeat(new_pt[None, None, :].astype(float), len(triples), axis=0), reps[triples]], axis=1)
        return bool(np.all(np.abs(np.linalg.det(stack)) <= det + 1e-6))

    mask = saturate(np.vstack([vmat, -vmat]))
    order = [i for i in range(len(frame)) if i < neg[i]]
    rng.shuffle(order)
    for rep in order:
        if mask[rep] or not det_ok(mask, frame[rep]):
            continue
        child = saturate(np.vstack([frame[mask], frame[rep], frame[neg[rep]]]))
        if child is not None:
            mask = child
    return frame[mask]


def main_census(runs, seed):
    rng = random.Random(seed)
    tally = Counter()
    for entry in json.load(open(str(Path(__file__).resolve().parent.parent / "data" / "frame_lattices.json"))):
        hmat = my_frame(entry)
        frame, neg, perms, det, vmat = frame_setup(hmat)
        for _ in range(runs):
            pts = grow_once(frame, neg, det, vmat, rng)
            (count, vol, g3, g1, g2), _ = invariants(pts, np.ones(len(pts), dtype=bool))
            case, rank = l6_case(pts)
            key = (case, rank, count, str(vol), str(g1), str(g2))
            if key not in tally:
                print(f"D={det}: NEW maximal-in-frame set: case {case} (rank {rank}) G={count} vol={vol} g1={g1} g2={g2}", flush=True)
            tally[key] += 1
    print("CENSUS (case, rankM, G, vol, g1, g2): count")
    for key, cnt in sorted(tally.items(), key=lambda kv: -float(eval(kv[0][4]))):
        print(f"  {key}: {cnt}")


if __name__ == "__main__":
    main_census(30, 2)
