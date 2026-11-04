#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# w_deletions.py - exact g_1 of W minus each one of its 25 vertex pairs
## version 0.10 - 20261104 - the version used for the runs reported in the paper
# Uses the exact analyser of w_ehrhart_check.py (read-only import).
# Usage: w_deletions.py --run   |   w_deletions.py --test
import argparse
import sys
from pathlib import Path

CHECKER_DIR = Path(str(Path(__file__).resolve().parent.parent / "data"))
PAIRS_FILE = CHECKER_DIR / "w_pairs.txt"
sys.path.insert(0, str(CHECKER_DIR))
import w_ehrhart_check as checker  # noqa: E402
import numpy as np  # noqa: E402


def deletion_polytope(pairs, index):
    """Vertices (both signs) of W5' with pair number `index` removed."""
    kept = pairs[:index] + pairs[index + 1:]
    return checker.symmetrize(kept)


def analyse_deletion(pairs, index):
    """One exact row: (index, deleted pair, full-dim?, vertices, g_1, sole interior point?, checks ok?)."""
    pts = deletion_polytope(pairs, index)
    if np.linalg.matrix_rank(np.array(pts, dtype=np.int64)) < len(pts[0]):
        return {"index": index, "pair": pairs[index], "full_dim": False}
    res = checker.analyse(f"W5' minus pair {index}", pts, run_qhull=True)
    checks_ok = res["facets_exact_ok"] and res["extra_k_ok"] and res["reciprocity_ok"] \
        and res["facets"] == res["qhull_facets"]
    return {"index": index, "pair": pairs[index], "full_dim": True, "vertices": res["vertices"],
            "g1": res["coeffs"][1], "interior_1": res["interior_1"], "checks_ok": checks_ok}


def print_rows(rows):
    print("| # | deleted pair +-v | full-dim | vertices | g_1 (exact) | int. pts of P | exact checks |")
    print("|---|---|---|---|---|---|---|")
    for row in rows:
        if not row["full_dim"]:
            print(f"| {row['index']} | {row['pair']} | NO | - | - | - | - |")
            continue
        print(f"| {row['index']} | {row['pair']} | yes | {row['vertices']} | {row['g1']} | {row['interior_1']} |"
              f" {row['checks_ok']} |")
    full = [row for row in rows if row["full_dim"]]
    print(f"\nMAX g_1 over the {len(full)} full-dimensional deletions: {max(row['g1'] for row in full)}")
    print(f"ALL <= 10: {all(row['g1'] <= 10 for row in full)}; ALL exact checks ok: "
          f"{all(row['checks_ok'] for row in full)}; ALL have 0 as the only interior point: "
          f"{all(row['interior_1'] == 1 for row in full)}")


def main_deletions():
    pairs = checker.read_points(PAIRS_FILE)
    assert len(pairs) == 25, len(pairs)
    whole = checker.analyse("W5'", checker.symmetrize(pairs), run_qhull=False)
    print(f"W5' itself: g_1 = {whole['coeffs'][1]} (must be 101/10)", flush=True)
    rows = []
    for index in range(len(pairs)):
        rows.append(analyse_deletion(pairs, index))
        print(f"done {index}", file=sys.stderr, flush=True)
    print_rows(rows)


def run_tests():
    pairs = [(1, 0), (0, 1), (1, 1)]  # hexagon; deleting (1,1) leaves the square conv(+-e1, +-e2)
    row = analyse_deletion(pairs, 2)
    assert row["full_dim"] and row["g1"] == 2 and row["vertices"] == 4, row
    row = analyse_deletion([(1, 0), (0, 1)], 0)
    assert not row["full_dim"], row
    print("ALL TESTS PASS")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--run", action="store_true")
    group.add_argument("--test", action="store_true")
    args = parser.parse_args()
    if args.test:
        run_tests()
    else:
        main_deletions()


if __name__ == "__main__":
    main()
