#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# case1_compare.py - per-level comparison of the two Case I walks: classes, max g_1, max g_2 per G
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# Labels such as L6 or Path C in the comments: see the glossary at the top of check_claims.py.
# Run: python3 case1_compare.py --first case1_first.log --second case1_second/rows.jsonl
import argparse
import json
import re

MINE_LINE = re.compile(r"G=(\d+): classes (\d+) .*max g1 (\S+) = .*max g2 (\S+) = ")


def read_first(path):
    rows = {}
    for line in open(path):
        match = MINE_LINE.match(line)
        if match:
            rows[int(match.group(1))] = (int(match.group(2)), match.group(3), match.group(4))
    return rows


def read_second(path):
    rows = {}
    for line in open(path):
        row = json.loads(line)
        rows[row["G"]] = (row["classes"], row["max_g1"], row["max_g2"])
    return rows


def main_diff(first_path, second_path):
    first, theirs = read_first(first_path), read_second(second_path)
    both = sorted(set(first) & set(theirs), reverse=True)
    bad = [g for g in both if first[g] != theirs[g]]
    for g in both:
        print(f"G {g}: {'AGREE ' if first[g] == theirs[g] else 'DIFFER'} first {first[g]}  second {theirs[g]}")
    print(f"levels compared {len(both)}, DIFFER {len(bad)} {bad}; first only {sorted(set(first) - set(theirs))}, "
          f"second only {sorted(set(theirs) - set(first))}")


def main_test():
    assert MINE_LINE.match("G=63: classes 1628 (total 2853); level max g1 7 = 7.0000, max g2 19 = 19.0000; next").groups() \
        == ("63", "1628", "7", "19")
    print("TEST PASS (log line parsed)")


def main():
    parser = argparse.ArgumentParser(description="Case I walk diff, first vs second program")
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--first")
    parser.add_argument("--second")
    args = parser.parse_args()
    if args.test:
        main_test()
        return
    if args.first is None or args.second is None:
        parser.error("--first and --second are required")
    main_diff(args.first, args.second)


if __name__ == "__main__":
    main()
