#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# case3_run_all.py - Case III, first program: run case3_frame_search.py over the 39 frame lattices, one JSON line per lattice
## version 0.40 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# Rows = case3_frame_search.run_lattice: idx (llist index #0..#38), rank_prune, states_G31 (= sets with rank M <= 3 and G >= min_g),
# by_rank, max_g1, max_g2, flags, hulls, seconds. Calibration of the prune (exact): pathc4_calib.jsonl (#4, #5, #12, both modes).
# Full-mode (no prune) rows from v0.10: case3_first_full.jsonl.
# Run: OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 19 python3 case3_run_all.py --dmin 1 --dmax 7 --out pathc3_results.jsonl
import argparse
import json
from pathlib import Path

from case3_frame_search import LLIST, run_lattice

MAX_RANK = 3  # L9: Path C covers the sets with rank M(S) <= 3 only
CHECK_L6 = 200     # per lattice: m_rank cross-checked against maximal_members.l6_case on the first 200 states (and every G >= 49)


def done_indices(out):
    """Lattice indices already finished in any L9 result file next to `out` (case3_first_rank3*.jsonl)."""
    done = set()
    for path in Path(out).resolve().parent.glob("case3_first_rank3*.jsonl"):
        done |= {json.loads(line)["idx"] for line in path.read_text().splitlines() if line.strip()}
    return done


def main_all(dmin, dmax, out, min_g):
    entries = json.load(open(LLIST))
    order = sorted((i for i, e in enumerate(entries) if dmin <= e["D"] <= dmax),
                   key=lambda i: (entries[i]["D"], entries[i]["box_points"]))
    finished = done_indices(out)
    for idx in order:
        if idx in finished:
            print(f"#{idx} already in {out}: skipped", flush=True)
            continue
        row = run_lattice(idx, entries[idx], MAX_RANK, min_g, CHECK_L6)
        with open(out, "a") as fh:
            fh.write(json.dumps(row) + "\n")
        print(json.dumps(row)[:400], flush=True)


def main():
    parser = argparse.ArgumentParser(description="Path C program 1 (L9 mode) over all lattices")
    parser.add_argument("--dmin", type=int, required=True)
    parser.add_argument("--dmax", type=int, required=True)
    parser.add_argument("--out", required=True)
    parser.add_argument("--min-g", type=int, default=31)
    args = parser.parse_args()
    main_all(args.dmin, args.dmax, args.out, args.min_g)


if __name__ == "__main__":
    main()
