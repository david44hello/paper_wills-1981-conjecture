#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# boxes_compare.py - per-level comparison of the two box-walk programs
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
"""Usage: boxes_compare.py --p1 <first program's log> --p2 <second program's log>   |   --test
Exit 0 = every level AGREES; exit 1 = any DIFF or a level present in one program only."""
import argparse
import re
import sys

P1_LEVEL = re.compile(r"^\s+G\s+(\d+): classes\s+(\d+)\s+point sets\s+(\d+)\s+max g_1 (\S+)\s+max g_2 (\S+)")
P1_CUT = re.compile(r"^\s+CUT G\s+(\d+): rank-4 classes\s+(\d+)\s+point sets\s+(\d+)")
P2_LEVEL = re.compile(r"^LEVEL box G\d+: G (\d+): rank-3 classes (\d+), rank-3 point sets (\d+), "
                      r"max g_1 (\S+), max g_2 ([^,]+),")
P2_CUT = re.compile(r"^CUT box G\d+: G (\d+): rank-4 classes (\d+), rank-4 point sets (\d+)")


def parse_lines(lines, level_re, cut_re):
    """Return {G: {'level': (classes, sets, g1, g2), 'cut': (classes, sets)}} from one log."""
    table = {}
    for line in lines:
        hit = level_re.match(line)
        if hit:
            gg = int(hit.group(1))
            table.setdefault(gg, {})['level'] = (int(hit.group(2)), int(hit.group(3)), hit.group(4), hit.group(5))
            continue
        hit = cut_re.match(line)
        if hit:
            gg = int(hit.group(1))
            table.setdefault(gg, {})['cut'] = (int(hit.group(2)), int(hit.group(3)))
    return table


def normalise_cut(table):
    """A missing CUT line in program 1 means 0 cut at that level (it prints only non-zero levels)."""
    for row in table.values():
        row.setdefault('cut', (0, 0))
    return table


def compare_tables(tab1, tab2):
    """Return list of (G, verdict, row1, row2); verdict AGREE / DIFF / ONLY1 / ONLY2."""
    out = []
    for gg in sorted(set(tab1) | set(tab2), reverse=True):
        if gg not in tab2:
            out.append((gg, 'ONLY1', tab1[gg], None))
        elif gg not in tab1:
            out.append((gg, 'ONLY2', None, tab2[gg]))
        else:
            verdict = 'AGREE' if tab1[gg] == tab2[gg] else 'DIFF'
            out.append((gg, verdict, tab1[gg], tab2[gg]))
    return out


def run_test():
    p1 = ["  G  61: classes       1  point sets         1  max g_1 6  max g_2 44/3",
          "  G  59: classes       3  point sets         8  max g_1 6  max g_2 44/3",
          "  CUT G  59: rank-4 classes       1  point sets         2"]
    p2 = ["LEVEL box G61: G 61: rank-3 classes 1, rank-3 point sets 1, max g_1 6, max g_2 44/3, elapsed 0.0 s",
          "CUT box G61: G 61: rank-4 classes 0, rank-4 point sets 0",
          "LEVEL box G61: G 59: rank-3 classes 3, rank-3 point sets 8, max g_1 6, max g_2 44/3, elapsed 0.0 s",
          "CUT box G61: G 59: rank-4 classes 1, rank-4 point sets 2"]
    res = compare_tables(normalise_cut(parse_lines(p1, P1_LEVEL, P1_CUT)), parse_lines(p2, P2_LEVEL, P2_CUT))
    assert [r[1] for r in res] == ['AGREE', 'AGREE'], res
    p2_bad = [line.replace("point sets 2", "point sets 3") for line in p2]
    res = compare_tables(normalise_cut(parse_lines(p1, P1_LEVEL, P1_CUT)), parse_lines(p2_bad, P2_LEVEL, P2_CUT))
    assert [r[1] for r in res] == ['AGREE', 'DIFF'], res
    print("--test PASS")


def main_diff(path1, path2):
    with open(path1) as fh:
        tab1 = normalise_cut(parse_lines(fh, P1_LEVEL, P1_CUT))
    with open(path2) as fh:
        tab2 = parse_lines(fh, P2_LEVEL, P2_CUT)
    results = compare_tables(tab1, tab2)
    for gg, verdict, row1, row2 in results:
        print(f"G {gg:3d}: {verdict:5s}  p1 {row1}  p2 {row2}")
    bad = [r for r in results if r[1] != 'AGREE']
    print(f"levels {len(results)}, AGREE {len(results) - len(bad)}, not-AGREE {len(bad)}")
    return 0 if (results and not bad) else 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--p1')
    parser.add_argument('--p2')
    parser.add_argument('--test', action='store_true')
    args = parser.parse_args()
    if args.test:
        run_test()
        return 0
    if not (args.p1 and args.p2):
        parser.error("--p1 and --p2 are both required (or --test)")
    return main_diff(args.p1, args.p2)


if __name__ == '__main__':
    sys.exit(main())
