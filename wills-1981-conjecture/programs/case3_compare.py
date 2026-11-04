#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# case3_compare.py - compare the two Case III programs lattice by lattice
## version 0.40 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
"""Reads the lattice list (data/frame_lattices.json), case3_first_rank3*.jsonl (program 1, top-down) and
case3_second_rank3.txt (program 2, sandwich search) from the current folder. Prints one row per lattice orbit: the two counts of admissible
saturated sets with G >= 31 (up to Stab(L)), the two max g_1 values, and AGREE / DIFF / pending. Any g_1 >= 8 flag
is printed loudly. Read-only: it writes nothing."""
import argparse
import json
import re
import sys
from pathlib import Path

LLIST = Path(str(Path(__file__).resolve().parent.parent / "data" / "frame_lattices.json"))
PROG1_DIR = Path(".")
MODES = {  # mode -> (program 1 glob in PROG1_DIR, program 2 results file); all case3_first_rank3* files = L9 mode
    "full": ("case3_first_full.jsonl", Path("case3_second_full.txt")),
    "rank3": ("case3_first_rank3*.jsonl", Path("case3_second_rank3.txt")),
}
RESULT_RE = re.compile(r"^RESULT #(\d+) D=(\d+) H=(\[\[.*?\]\]) \|Stab\|=(\d+) box=(\d+): .*?leaves \(classes, G >= 31\) "
                       r"(\d+) per G .*?; max g_1 (\S+); max g_2 (\S+); g_1 >= 8: (\[.*?\]);")


def key_of(hnf):
    return json.dumps(hnf)


def load_lattices():
    return [(idx, rec["D"], key_of(rec["H"]), rec["box_points"]) for idx, rec in enumerate(json.loads(LLIST.read_text()))]


def load_prog1(glob):
    out = {}
    for path in sorted(PROG1_DIR.glob(glob)):
        for line in path.read_text().splitlines():
            if line.strip():
                rec = json.loads(line)
                key = key_of(rec["H"])
                if key in out and out[key][0] != rec["states_G31"]:
                    raise RuntimeError(f"program 1 has two different results for {key} (in {path})")
                out[key] = (rec["states_G31"], rec["max_g1"], rec["flagged"])
    return out


def load_prog2(path):
    out = {}
    if path.exists():
        for line in path.read_text().splitlines():
            match = RESULT_RE.match(line)
            if match:
                hnf = json.loads(match.group(3))
                out[key_of(hnf)] = (int(match.group(6)), match.group(7), match.group(9))
    return out


def verdict(row1, row2):
    if row1 is None or row2 is None:
        return "pending"
    return "AGREE" if row1[0] == row2[0] else "DIFF"


def main_diff(mode):
    glob1, path2 = MODES[mode]
    prog1, prog2 = load_prog1(glob1), load_prog2(path2)
    print(f"mode {mode}: program 1 = {PROG1_DIR}/{glob1}, program 2 = {path2}")
    unmatched1 = set(prog1) - {key for _, _, key, _ in load_lattices()}
    print(f"{'#':>3} {'D':>3} {'box':>4} | {'prog1 G>=31':>11} {'max g1':>7} | {'prog2 G>=31':>11} {'max g1':>7} | verdict")
    counts = {"AGREE": 0, "DIFF": 0, "pending": 0}
    for idx, dval, key, box in load_lattices():
        row1, row2 = prog1.get(key), prog2.get(key)
        state = verdict(row1, row2)
        counts[state] += 1
        cell1 = f"{row1[0]:>11} {str(row1[1]):>7}" if row1 else f"{'-':>11} {'-':>7}"
        cell2 = f"{row2[0]:>11} {str(row2[1]):>7}" if row2 else f"{'-':>11} {'-':>7}"
        flags = [fl for fl in (row1[2] if row1 else [], row2[2] if row2 else "[]") if fl not in ([], "[]")]
        print(f"{idx:>3} {dval:>3} {box:>4} | {cell1} | {cell2} | {state}" + (f"   !!! g_1 >= 8: {flags}" if flags else ""))
    print("summary:", counts, "| prog1 rows not matched to the list:", len(unmatched1))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", required=True, choices=sorted(MODES), help="full Path C, or L9 rank <= 3 mode")
    args = parser.parse_args()
    main_diff(args.mode)


if __name__ == "__main__":
    sys.exit(main())
