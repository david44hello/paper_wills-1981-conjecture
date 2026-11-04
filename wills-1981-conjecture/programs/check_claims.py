#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# check_claims.py - read the outputs of one claim (out/<claim>/ or expected/<claim>/) and check every number the paper states
## version 1.00 - 20261104 - first release
#
# Glossary. Comments in the other programs use labels from the working notes behind the paper. In the paper's own terms
# (numbers as in the expanded version; Sections 1-7 are numbered as in the paper itself):
#   L0          Lemma 4.1: L_P(1) = G and L_P(-1) = 1 give g_1 + g_3 = g_2 + g_4 = (G - 1)/2 (n = 4).
#   L3          Lemma 4.3: if G <= 29, then g_1 < 8.
#   L4          the frame: lattice points v_1, ..., v_4 of P with |det| as large as possible (Section 5).
#   L6          the cases of Section 5: Case I, M(P) contains a basis; Case II, r(P) = 4 and no basis (with the index
#               bound of Computation 2); Case III, r(P) <= 3.
#   L8          Lemma 5.1 (frame lattices and the sets A(Lambda)) and Lemma 6.1 (the downward walk reaches every set).
#   L9          M reverses inclusion, so a set with r = 4 and all its subsets may be cut (Computation 5).
#   Path C      the search over the frame lattices, i.e. Case III (Computations 4, 5 and 6).
#   Case IV     the sets with M(S) = {0}, i.e. r = 0: T, X and R_41 (Section 7, Computation 6).
#   N10         Theorem 8.2: a set with r = 3 lies in one of six boxes (Computations 7 and 8).
#   N9, Q1      an earlier list of four boxes (G = 69, 67, 63, 63), used only as a test control.
#   R2, C1      Computation 1 for G >= 63 and for 31 <= G <= 61;  R4: Computation 3.
# In the box programs, L1 and L2 (or L(1), L(2)) are lattice-point counts, not labels.
"""Usage: check_claims.py <claim> <folder>   |   --test

Prints one line per stated number, "OK" or "FAIL", and exits 1 if any line fails. The numbers below are the paper's."""
import ast
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

DATA = Path(__file__).resolve().parent.parent / "data"
EXPECTED = Path(__file__).resolve().parent.parent / "expected"
W_POLY = ["1", "101/10", "127/12", "139/6", "557/12", "386/15"]
W_COUNTS = [1, 117, 1815, 10765, 39927, 112639, 265705]
T_POLY, X_POLY = ["1", "8", "8", "16", "16"], ["1", "8", "4", "8", "12"]
CASE1_CLASSES, CASE3_CLASSES = 2547694, 588592
INDEX_MAX = {2: 45, 3: 27, 4: 27, 5: 17, 6: 15, 7: 11, 8: 17, 9: 9, 10: 9, 12: 9, 16: 9}
FRAMES_PER_D = {1: 1, 2: 11, 3: 24, 4: 73, 5: 56, 6: 160, 7: 96, 8: 229, 9: 72, 10: 96, 12: 128, 16: 86, 18: 8}
ORBITS_PER_D = {1: 1, 2: 3, 3: 2, 4: 7, 5: 2, 6: 4, 7: 1, 8: 9, 9: 2, 10: 1, 12: 2, 16: 4, 18: 1}
SANDWICH = re.compile(r"^RESULT #(\d+) D=(\d+) .*?leaves \(classes, G >= 31\) (\d+) per G (\{.*?\}); max g_1 (\S+); "
                      r"max g_2 (\S+); g_1 >= 8: (\[.*?\]);.*?rank M histogram (\{.*?\})")


class Report:
    def __init__(self):
        self.lines = []

    def check(self, ok, text):
        self.lines.append((bool(ok), text))

    def print_and_exit(self, claim):
        for ok, text in self.lines:
            print(f"{'OK  ' if ok else 'FAIL'} {text}")
        failed = sum(1 for ok, _ in self.lines if not ok)
        print(f"{claim}: {len(self.lines) - failed} of {len(self.lines)} checks OK" + ("" if not failed else f", {failed} FAILED"))
        sys.exit(1 if failed else 0)


def fr(text):
    return Fraction(str(text))


def jsonl(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def sandwich_rows(path):
    rows = {}
    for line in Path(path).read_text().splitlines():
        match = SANDWICH.match(line)
        if match:
            idx, dval, leaves, per_g, g1, g2, flags, hist = match.groups()
            rows[int(idx)] = {"D": int(dval), "leaves": int(leaves), "per_g": ast.literal_eval(per_g),
                              "max_g1": g1, "max_g2": g2, "flags": ast.literal_eval(flags), "hist": ast.literal_eval(hist)}
    return rows


def normaliz(path):
    text = Path(path).read_text()
    lines = text.splitlines()
    at = lines.index("Hilbert polynomial:")
    denom = int(re.search(r"common denominator = (\d+)", lines[at + 2]).group(1))
    return {"points": int(re.search(r"^(\d+) lattice points in polytope", text, re.M).group(1)),
            "hyperplanes": int(re.search(r"^(\d+) support hyperplanes", text, re.M).group(1)),
            "poly": [str(Fraction(int(num), denom)) for num in lines[at + 1].split()]}


def latte(path):
    """The Ehrhart polynomial printed by latte-count --ehrhart-polynomial, as coefficient strings g_0, g_1, ..."""
    line = re.search(r"^Ehrhart polynomial:(.*)$", Path(path).read_text(), re.M).group(1)
    terms = {int(power): str(Fraction(coeff.strip())) for coeff, power in re.findall(r"\+ ([^*]+)\* t\^(\d+)", line)}
    return [terms.get(power, "0") for power in range(max(terms) + 1)]


def analyser_blocks(path):
    """Blocks of w_ehrhart_check.py output, keyed by their '## ' title line."""
    blocks, title = {}, None
    for line in Path(path).read_text().splitlines():
        if line.startswith("## "):
            title = line[3:]
            blocks[title] = []
        elif title is not None:
            blocks[title].append(line)
    return {key: "\n".join(val) for key, val in blocks.items()}


def analyser_numbers(block):
    poly = re.search(r"Ehrhart coefficients g_0\.\.g_\d: \(([^)]*)\)", block).group(1)
    counts = re.search(r"L\(k\), k = 0\.\.\d: \[([^\]]*)\]", block).group(1)
    facets = re.search(r"facets: (\d+)", block).group(1)
    heights = re.search(r"facet lattice heights: \[([^\]]*)\]", block).group(1)
    interior = re.search(r"interior lattice points of P: (\d+), of 2P: (\d+)", block).groups()
    return {"poly": [p.strip() for p in poly.split(",")], "counts": [int(c) for c in counts.split(",")],
            "facets": int(facets), "heights": [int(h) for h in heights.split(",")],
            "interior": tuple(int(i) for i in interior), "flags": block}


def check_w(report, folder):
    blocks = analyser_blocks(folder / "w_first.txt")
    (only,) = blocks.values()
    first = analyser_numbers(only)
    report.check(first["poly"] == W_POLY, f"W, first program: L_W coefficients {', '.join(first['poly'])}")
    report.check(first["counts"] == W_COUNTS, f"W, first program: L_W(0..6) = {first['counts']}")
    report.check(first["facets"] == 92, f"W, first program: {first['facets']} facets")
    report.check(first["interior"] == (1, 243), f"W, first program: interior points of W, 2W = {first['interior']}")
    report.check("vertices: 50" in only, "W, first program: 50 vertices")
    nz = normaliz(folder / "w.out")
    report.check(nz["poly"] == W_POLY, f"W, Normaliz: L_W coefficients {', '.join(nz['poly'])}")
    report.check(nz["points"] == 117 and nz["hyperplanes"] == 92, f"W, Normaliz: G = {nz['points']}, {nz['hyperplanes']} facets")
    report.check(latte(folder / "latte_w.txt") == W_POLY, "W, LattE integrale 1.7.6: the same polynomial")
    report.check(latte(EXPECTED / "theorem-1.3" / "latte_w_recorded.log") == W_POLY,
                 "W, LattE: the recorded run of November 3 (latte_w_recorded.log) gives the same polynomial")
    final = re.search(r"MINIMAL .*?: (\d+) pairs; g = (\[.*?\])", (folder / "w_reduction.txt").read_text())
    report.check(final and final.group(1) == "25" and ast.literal_eval(final.group(2)) == W_POLY,
                 "W, exact counter of the search: the greedy reduction of W_5 ends at 25 pairs with L_W as above")
    same = (folder / "witness_n5_min_pairs.txt").read_text() == (DATA / "w_pairs.txt").read_text()
    report.check(same, "W, exact counter of the search: its 25 pairs equal data/w_pairs.txt")
    big_g, two_w, int_two_w, vol = first["counts"][1], first["counts"][2], first["interior"][1], fr(nz["poly"][5])
    g1 = (4 * (big_g + 1) + 24 * vol - Fraction(two_w + int_two_w, 2)) / 6
    report.check((big_g, two_w, int_two_w, vol, g1) == (117, 1815, 243, Fraction(386, 15), Fraction(101, 10)),
                 f"W: the four numbers G = {big_g}, #2W = {two_w}, #int 2W = {int_two_w}, vol = {vol} give g_1 = {g1} > 10")


def case1_first_levels(path):
    pattern = re.compile(r"^G=(\d+): classes (\d+) \(total (\d+)\); level max g1 (\S+) .*?max g2 (\S+) ")
    return {int(m.group(1)): (int(m.group(2)), m.group(4), m.group(5))
            for m in map(pattern.match, Path(path).read_text().splitlines()) if m}


def check_case1(report, folder):
    first = case1_first_levels(folder / "case1_first.log")
    second = {row["G"]: (row["classes"], row["max_g1"], row["max_g2"]) for row in jsonl(folder / "case1_second/rows.jsonl")}
    for name, levels in (("first", first), ("second", second)):
        total = sum(classes for classes, _, _ in levels.values())
        report.check(total == CASE1_CLASSES and min(levels) == 31, f"Case I, {name} program: {total:,} classes, G = 81..31")
        others = [g for g, (_, g1, _) in levels.items() if g != 81 and fr(g1) >= 8]
        report.check(levels[81] == (1, "8", "24") and not others,
                     f"Case I, {name} program: g_1 <= 8; g_1 = 8 only at G = 81 (one class, the full set)")
    report.check(first == second, f"Case I: the two programs agree on all {len(first)} levels (classes, max g_1, max g_2)")
    flagged = jsonl(folder / "case1_second/flagged.jsonl")
    report.check(len(flagged) == 1, "Case I, second program: exactly one flagged class (the full set {-1,0,1}^4)")


def check_case3(report, folder):
    first = {row["idx"]: row for row in jsonl(folder / "case3_first_rank3.jsonl")}
    second = sandwich_rows(folder / "case3_second_rank3.txt")
    report.check(sorted(first) == list(range(39)) and sorted(second) == list(range(39)), "Case III: both programs cover all 39 lattices")
    tot1 = sum(row["states_G31"] for row in first.values())
    tot2 = sum(row["leaves"] for row in second.values())
    report.check(tot1 == CASE3_CLASSES, f"Case III, first program: {tot1:,} classes")
    report.check(tot2 == CASE3_CLASSES, f"Case III, second program: {tot2:,} classes")
    same = all(first[idx]["states_G31"] == second[idx]["leaves"] for idx in range(39))
    report.check(same, "Case III: the two programs agree on every lattice")
    max1 = max(fr(row["max_g1"]) for row in first.values() if row["max_g1"] is not None)
    max2 = max(fr(row["max_g1"]) for row in second.values() if row["max_g1"] != "None")
    report.check(max1 == 8 and max2 == 8, f"Case III: g_1 <= 8 (first {max1}, second {max2})")
    eq1 = sorted(set(entry[0] for row in first.values() for entry in row["flagged"] if fr(entry[1]) == 8))
    eq2 = sorted(set(entry[0] for row in second.values() for entry in row["flags"]))
    report.check(eq1 == [33, 49] and eq2 == [33, 49], f"Case III: g_1 = 8 for exactly two sets, G = {eq1} and {eq2}")


def check_section7(report, folder):
    first = {row["idx"]: row for row in jsonl(folder / "case3_first_rank0.jsonl")}
    second = sandwich_rows(folder / "case3_second_rank0.txt")
    found1 = sorted((idx, row["states_G31"]) for idx, row in first.items() if row["states_G31"])
    found2 = sorted((idx, row["leaves"]) for idx, row in second.items() if row["leaves"])
    report.check(found1 == [(20, 1), (35, 1), (38, 1)], f"M(S) = {{0}}, first program: exactly three sets (lattices {found1})")
    report.check(found2 == [(20, 1), (35, 1), (38, 1)], f"M(S) = {{0}}, second program: exactly three sets (lattices {found2})")
    report.check([second[i]["per_g"] for i in (20, 35, 38)] == [{49: 1}, {41: 1}, {33: 1}], "M(S) = {0}: G = 49 (T), 41, 33 (X)")
    blocks = analyser_blocks(folder / "tx_first.txt")
    tee = analyser_numbers(next(val for key, val in blocks.items() if key.startswith("T ")))
    ex = analyser_numbers(next(val for key, val in blocks.items() if key.startswith("X")))
    report.check(tee["poly"] == T_POLY and tee["facets"] == 24 and tee["heights"] == [2], "T: L_T = 1 8 8 16 16; 24 facets at lattice distance 2")
    report.check(ex["poly"] == X_POLY and ex["facets"] == 16 and ex["heights"] == [3], "X: L_X = 1 8 4 8 12; 16 facets at lattice distance 3")
    for name, poly, points, facets in (("t", T_POLY, 49, 24), ("x", X_POLY, 33, 16)):
        nz = normaliz(folder / f"{name}.out")
        report.check(nz["poly"] == poly and nz["points"] == points and nz["hyperplanes"] == facets,
                     f"{name.upper()}, Normaliz: L = {' '.join(nz['poly'])}, G = {nz['points']}, {nz['hyperplanes']} facets")


def check_index(report, folder):
    first_text = (folder / "index_first.txt").read_text()
    first_total = int(re.search(r"sublattices of index 2\.\.16 examined: (\d+)", first_text).group(1))
    first_max = {int(d): int(n) for d, n in re.findall(r"index +(\d+): max \|Gamma cap cube\| among full-rank = (\d+)", first_text)}
    second_text = (folder / "index_second.txt").read_text()
    second_total = int(re.search(r"all sublattices of index 2\.\.16: (\d+)", second_text).group(1))
    second_max = ast.literal_eval(re.search(r"by d \(spanning only\): (\{.*\})", second_text).group(1))
    expected = {d: INDEX_MAX.get(d, 0) for d in range(2, 17)}
    report.check(first_total == 40406 and second_total == 40406, f"index bound: {first_total:,} and {second_total:,} sublattices")
    report.check(first_max == expected, "index bound, first program: maximum 45 for d = 2, at most 27 for d >= 3 (all maxima as in the paper)")
    report.check(second_max == INDEX_MAX, "index bound, second program: the same maxima")


def check_case2(report, folder):
    text = (folder / "case2_first.txt").read_text()
    rows = re.findall(r"^index 2 G0=(\d+) classes=(\d+) max g1=(\S+) ", text, re.M)
    by_points = sorted((int(g0), int(cls)) for g0, cls, _ in rows)
    report.check(by_points == [(39, 58)] * 4 + [(41, 27)] + [(45, 531)] * 6,
                 "Case II, first program: 11 lattices; 531 classes (6 lattices, Gamma_2), 58 (4, Gamma_3), 27 (1, Gamma_4)")
    report.check(max(fr(g1) for _, _, g1 in rows) == 6, "Case II, first program: g_1 <= 6")
    for mm, classes in ((2, 531), (3, 58), (4, 27)):
        level_rows = jsonl(folder / f"case2_second_m{mm}/rows.jsonl")
        total = sum(row["classes"] for row in level_rows)
        top = max(fr(row["max_g1"]) for row in level_rows)
        report.check(total == classes and top <= 6, f"Case II, second program, Gamma_{mm}: {total} classes, max g_1 = {top}")


def check_frames(report, folder):
    text = (folder / "frames_first.txt").read_text()
    first = {int(d): int(n) for d, n in re.findall(r"^D= ?(\d+): W_4 cross-polytopes +(\d+);", text, re.M)}
    report.check(sorted(first) == list(range(1, 25)) and {d: n for d, n in first.items() if n} == FRAMES_PER_D,
                 f"frame lattices, first program (D <= 24): {sum(first.values()):,} lattices, per D as in the paper")
    stats = json.loads((folder / "frames_second.json").read_text())["stats"]
    second = {int(d): row["in_W4"] for d, row in stats.items() if row["in_W4"]}
    report.check(second == FRAMES_PER_D, f"frame lattices, second program (D <= 23): {sum(second.values()):,} lattices, per D as in the paper")
    orbits = json.loads((folder / "frame_lattices.json").read_text())
    per_d = {}
    for rec in orbits:
        per_d[rec["D"]] = per_d.get(rec["D"], 0) + 1
    report.check(len(orbits) == 39 and per_d == ORBITS_PER_D, f"frame lattices: {len(orbits)} orbits, D in {sorted(per_d)}")
    same = (folder / "frame_lattices.json").read_text() == (DATA / "frame_lattices.json").read_text()
    report.check(same, "frame lattices: the orbit list equals data/frame_lattices.json (the input of Computation 5)")


TEST_PROGRAMS = ("ehrhart_exact ehrhart_count ehrhart_probe set_guard generic_walk case1_walk case1_compare case2_walk "
                 "walk_second index_bound_second case3_frame_search boxes_list_first boxes_list_second boxes_walk_first "
                 "boxes_walk_second boxes_compare w_ehrhart_check w_deletions").split()
W5_POLY = ["1", "301/30", "47/4", "53/2", "197/4", "397/15"]
W5_COUNTS = [1, 125, 1915, 11273, 41635, 117147, 275841]
BOXES = {69: ("6", "18", "28", "16"), 67: ("19/3", "52/3", "80/3", "47/3"), 63: ("6", "31/2", "25", "31/2"),
         61: ("6", "44/3", "24", "46/3"), 39: ("5", "11", "14", "8"), 37: ("16/3", "31/3", "38/3", "23/3")}
LARGE_BOXES = {0: (69, 160502, 2495033, "6", "18"), 1: (61, 19804, 75603, "6", "44/3"),
               2: (63, 66050, 389891, "37/6", "31/2"), 3: (67, 122559, 5691415, "19/3", "52/3")}


def check_tests(report, folder):
    codes = dict(line.split() for line in (folder / "test_exit_codes.txt").read_text().splitlines() if line.strip())
    for prog in TEST_PROGRAMS:
        path = folder / f"{prog}.test.txt"
        text = path.read_text() if path.exists() else ""
        last = text.strip().splitlines()[-1] if text.strip() else ""
        report.check(codes.get(prog) == "0" and "Traceback" not in text, f"{prog}.py --test (exit {codes.get(prog)}): {last[:100]}")


def rank_rows(folder, rho):
    first = {row["idx"]: row for row in jsonl(folder / f"case3_first_rank{rho}.jsonl")}
    return first, sandwich_rows(folder / f"case3_second_rank{rho}.txt")


def check_rank_cuts(report, folder):
    first, second = rank_rows(folder, 0)
    report.check({i: r["states_G31"] for i, r in first.items() if r["states_G31"]} == {20: 1, 35: 1, 38: 1}
                 and [first[i]["max_g1"] for i in (20, 35, 38)] == ["8", "20/3", "8"],
                 "rho = 0, first program: exactly T (g_1 = 8), the set R_41 (g_1 = 20/3) and X (g_1 = 8)")
    report.check({i: r["per_g"] for i, r in second.items() if r["leaves"]} == {20: {49: 1}, 35: {41: 1}, 38: {33: 1}},
                 "rho = 0, second program: the same three sets, G = 49, 41, 33")
    first, second = rank_rows(folder, 1)
    totals = {}
    for row in first.values():
        for rank, count in row["by_rank"].items():
            totals[rank] = totals.get(rank, 0) + count
    report.check(totals == {"0": 3, "1": 2} and first[20]["max_g1_by_rank"].get("1") == "7"
                 and first[35]["max_g1_by_rank"].get("1") == "17/3",
                 "rho = 1, first program: exactly five sets; the two of rank 1 are T' (g_1 = 7) and R_39 (g_1 = 17/3)")
    report.check({i: r["per_g"] for i, r in second.items() if r["leaves"]} == {20: {49: 1, 47: 1}, 35: {41: 1, 39: 1}, 38: {33: 1}},
                 "rho = 1, second program: the same five sets (T' has G = 47, R_39 has G = 39)")
    first, second = rank_rows(folder, 2)
    rank2 = {i: r["by_rank"].get("2", 0) for i, r in first.items()}
    top_g1 = max(fr(r["max_g1_by_rank"]["2"]) for r in first.values() if "2" in r.get("max_g1_by_rank", {}))
    top_g2 = max(fr(r["max_g2_by_rank"]["2"]) for r in first.values() if "2" in r.get("max_g2_by_rank", {}))
    report.check(sum(rank2.values()) == 7527 and top_g1 == Fraction(19, 3) and top_g2 == 14,
                 f"rho = 2, first program: {sum(rank2.values()):,} sets of rank 2, g_1 <= {top_g1}, g_2 <= {top_g2}")
    same = sorted(second) == list(range(39)) and all(second[i]["hist"].get(2, 0) == rank2[i] for i in range(39))
    report.check(same, "rho = 2: the two programs agree on the number of rank-2 sets of every lattice")
    dumped = sorted((row["G"], row["rank"], row["coeffs"]) for row in jsonl(folder / "r41_r39_points.jsonl"))
    report.check(dumped == [(39, 1, ["1", "17/3", "7", "40/3", "12"]), (41, 0, ["1", "20/3", "20/3", "40/3", "40/3"])],
                 "R_41 and R_39: points listed in r41_r39_points.jsonl, L = 1 20/3 20/3 40/3 40/3 and 1 17/3 7 40/3 12")


def check_boxes(report, folder):
    report.check((folder / "boxes.jsonl").read_text() == (DATA / "boxes.jsonl").read_text(),
                 "boxes, first program: its list equals data/boxes.jsonl (the input of Computation 8)")
    listed = [json.loads(line)["G_box"] for line in (DATA / "boxes.jsonl").read_text().splitlines()]
    report.check(listed == [69, 61, 63, 67, 39, 37], f"boxes, first program: six boxes, G = {listed}")
    text = (folder / "boxes_second.txt").read_text()
    counts = [tuple(map(int, m)) for m in re.findall(r"index \d+: (\d+) lattices Gamma, (\d+) with spanning", text)]
    report.check(counts == [(1, 1), (7, 4), (13, 4), (35, 7), (31, 0), (91, 0)],
                 "boxes, second program: sublattices of Z^3 of index 1..6: 1, 7, 13, 35, 31, 91; spanning 1, 4, 4, 7, 0, 0")
    report.check("raw (Gamma, a' mod Gamma*) boxes: 33" in text and re.search(r"CLASSES .*?: 6\b", text),
                 "boxes, second program: 33 boxes before identification, 6 classes")
    found = {int(g): (g1, g2, g3, vol) for g, vol, g3, g1, g2 in
             re.findall(r"G=(\d+) vol=(\S+) g3=(\S+) g1=(\S+) g2=(\S+) \|", text)}
    report.check(found == BOXES, "boxes, second program: G and (g_1, g_2, g_3, g_4) of the six classes as in the paper")


def check_box_walks(report, folder):
    for box, (big_g, classes, sets, g1, g2) in LARGE_BOXES.items():
        first = (folder / f"box{box}_first.log").read_text()
        second = (folder / f"box{box}_second.log").read_text()
        report.check(f"TOTAL classes {classes}, point sets {sets}, max g_1 {g1}, max g_2 {g2}; flagged (g_1 >= 8): 0" in first,
                     f"box G = {big_g}, first program: {classes:,} classes, {sets:,} point sets, max g_1 {g1}, max g_2 {g2}")
        report.check(f"rank-3 classes {classes} per G" in second
                     and re.search(rf"point sets with G >= 31: {sets} per G .*?max g_1 = {re.escape(g1)}, max g_2 = {re.escape(g2)}$",
                                   second, re.M),
                     f"box G = {big_g}, second program: the same numbers")
        compare = (folder / f"box{box}_compare.txt").read_text()
        levels = re.search(r"levels (\d+), AGREE (\d+), not-AGREE 0$", compare, re.M)
        report.check(levels and levels.group(1) == levels.group(2),
                     f"box G = {big_g}: the two programs agree on all {levels.group(1) if levels else '?'} levels")
    for box, big_g, rank3, everything, g1 in ((4, 39, 209, 483, "5"), (5, 37, 42, 220, "16/3")):
        cut = (folder / f"box{box}_second.log").read_text()
        nocut = (folder / f"box{box}_second_nocut.log").read_text()
        report.check(re.search(rf"point sets with G >= 31: {rank3} per G .*?max g_1 = {re.escape(g1)},", cut),
                     f"box G = {big_g}, second program: {rank3} sets with r = 3, max g_1 = {g1}")
        report.check(re.search(rf"point sets with G >= 31: {everything} per G ", nocut),
                     f"box G = {big_g}, second program without the cut: {everything} sets")
    third = (folder / "boxes_small_third.txt").read_text()
    report.check("box 4 TOTAL: all 483, rank 3 209," in third and "box 5 TOTAL: all 220, rank 3 42," in third,
                 "small boxes, third program (no symmetry): 209 and 42 sets with r = 3, of 483 and 220")


def check_x_maximal(report, folder):
    first = (folder / "x_first.txt").read_text()
    second = (folder / "x_second.txt").read_text()
    report.check("192 candidates, 0 addable" in first, "X, first program: 192 pairs outside X in the frame, none can be added")
    report.check(re.search(r"frame points 417 \| X points 33", second) is not None, "X, second program: 417 frame points, 33 in X")
    report.check("outside pairs 192 | pairs keeping W_4 (should be 0): 0 " in second,
                 "X, second program: for each of the 192 pairs, conv(X u {+-x}) has a second interior lattice point")


def check_w5(report, folder):
    counter = (folder / "w5_search_counter.txt").read_text()
    report.check(re.search(r"g = (\[.*?\])", counter) and ast.literal_eval(re.search(r"g = (\[.*?\])", counter).group(1)) == W5_POLY,
                 "W_5, exact counter of the search: L = 1 + 301/30 k + 47/4 k^2 + 53/2 k^3 + 197/4 k^4 + 397/15 k^5")
    report.check((folder / "witness_n5_vertices.txt").read_text() == (DATA / "w5_vertices.txt").read_text(),
                 "W_5: the 58 vertices written by the search program equal data/w5_vertices.txt")
    (block,) = analyser_blocks(folder / "w5_first.txt").values()
    first = analyser_numbers(block)
    report.check(first["poly"] == W5_POLY and first["counts"] == W5_COUNTS and "vertices: 58" in block,
                 f"W_5, facet program: 58 vertices, L(0..6) = {first['counts']}")
    report.check(first["facets"] == 102 and first["heights"] == [1, 3, 4, 5, 6, 7, 8, 9, 10, 12, 17] and first["interior"] == (1, 243),
                 "W_5, facet program: 102 facets at lattice distances 1, 3-10, 12, 17; interior points of W_5, 2W_5: 1, 243")
    nz = normaliz(folder / "w5.out")
    report.check(nz["poly"] == W5_POLY and nz["points"] == 125 and nz["hyperplanes"] == 102,
                 "W_5, Normaliz: the same polynomial, G = 125, 102 facets")
    report.check(latte(folder / "latte_w5.txt") == W5_POLY, "W_5, LattE integrale 1.7.6: the same polynomial")


def check_deletions(report, folder):
    text = (folder / "deletions_first.txt").read_text()
    rows = re.findall(r"^\| (\d+) \| (\([^)]*\)) \| yes \| (\d+) \| (\S+) \| 1 \| True \|$", text, re.M)
    first = {int(num): (pair, int(verts), g1) for num, pair, verts, g1 in rows}
    report.check(sorted(first) == list(range(25)) and all(v == 48 for _, v, _ in first.values()),
                 "deletions, first program: all 25 deletions are in W^5 and have 48 vertices")
    values = [fr(g1) for _, _, g1 in first.values()]
    report.check(max(values) == 10 and values.count(10) == 2 and min(values) == Fraction(43, 6),
                 "deletions, first program: max g_1 = 10 (exactly twice), min g_1 = 43/6")
    agree = True
    for num in range(25):
        nz = normaliz(folder / f"d{num:02d}.out")
        out = (folder / f"d{num:02d}.out").read_text()
        agree &= nz["poly"][1] == first[num][2] and re.search(r"^48 extreme rays", out, re.M) is not None
    report.check(agree, "deletions, Normaliz: the same 25 values of g_1, 48 vertices each")


CHECKS = {"test": check_tests, "theorem-1.3": check_w, "computation-1": check_case1, "computation-2": check_index,
          "computation-3": check_case2, "computation-4": check_frames, "computation-5": check_case3, "section-7": check_section7,
          "computation-6": check_rank_cuts, "computation-7": check_boxes, "computation-8": check_box_walks,
          "computation-9": check_x_maximal, "w5": check_w5, "deletions": check_deletions}


def main_check(claim, folder):
    report = Report()
    if claim not in CHECKS:
        sys.exit(f"no checks for claim {claim!r}; claims: {', '.join(CHECKS)}")
    CHECKS[claim](report, Path(folder))
    report.print_and_exit(claim)


def run_tests():
    line = ("RESULT #38 D=18 H=[[1]] |Stab|=48 box=417: nodes 193; leaves (classes, G >= 31) 1 per G {33: 1}; max g_1 8; "
            "max g_2 4; g_1 >= 8: [(33, ['1', '8', '4', '8', '12'])]; vol 16: []; Case IV G >= 49: []; hulls 192; "
            "rank M histogram {0: 1}; rank_prune True")
    match = SANDWICH.match(line)
    assert match and match.group(3) == "1" and ast.literal_eval(match.group(7))[0][0] == 33
    assert str((4 * 118 + 24 * Fraction(386, 15) - Fraction(1029)) / 6) == "101/10"
    print("check_claims.py --test PASS")


def main():
    if sys.argv[1:] == ["--test"]:
        run_tests()
    elif len(sys.argv) == 3:
        main_check(sys.argv[1], sys.argv[2])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
