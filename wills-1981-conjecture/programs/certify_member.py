#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# certify_member.py - certify that a lattice polytope lies in W_n and compare its Ehrhart coefficients with the cube
## version 0.10 - 20261102 - the version used for the runs reported in the paper
# W_n = lattice polytopes P = -P in R^n whose only interior lattice point is the origin.
# Checks (all exact): (a) the point set is symmetric; (b) the origin is interior (no facet passes through it);
# (c) #int(P) = 1; (d) which input points are vertices; (e) Ehrhart coefficients vs. Wills' bounds 2^i C(n,i).
# Usage: certify_member.py FILE   (one point per line, integers separated by spaces; or a JSON list)
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ehrhart_count as ehr  # noqa: E402


def read_points(path):
    text = Path(path).read_text().strip()
    if text.startswith("["):
        return [tuple(int(xx) for xx in vv) for vv in json.loads(text)]
    return [tuple(int(xx) for xx in line.split()) for line in text.splitlines() if line.strip()]


def is_vertex(point, facets):
    """A point of P is a vertex iff the facets tight at it have normals of full rank n."""
    tight = [list(normal) for normal, height in facets if sum(aa * bb for aa, bb in zip(normal, point)) == height]
    return bool(tight) and ehr.rank_of(tight) == len(point)


def wills_bounds(nn):
    return [Fraction(2 ** ii * math.comb(nn, ii)) for ii in range(nn + 1)]


def main_certify(points, extra=2):
    """Return a dict of exact certificate facts for conv(points)."""
    nn = len(points[0])
    symmetric = set(points) == set(tuple(-xx for xx in pp) for pp in points)
    coeffs, facets, values, checked = ehr.main_ehrhart(points, extra=extra)
    origin_interior = all(height > 0 for _normal, height in facets)
    n_interior = ehr.count_points(facets, points, 1, strict=True)
    n_vertices = sum(1 for pp in points if is_vertex(pp, facets))
    bounds = wills_bounds(nn)
    violations = [(ii, coeffs[ii], bounds[ii]) for ii in range(nn + 1) if coeffs[ii] > bounds[ii]]
    return {"n": nn, "points": len(points), "vertices": n_vertices, "facets": len(facets),
            "symmetric": symmetric, "origin_interior": origin_interior, "interior_lattice_points": n_interior,
            "in_W_n": symmetric and origin_interior and n_interior == 1, "G": values[1],
            "coeffs": coeffs, "checked_k": checked, "violations": violations,
            "facet_heights": sorted(set(height for _n, height in facets))}


def format_certificate(cert):
    lines = [f"n = {cert['n']}; input points {cert['points']}, of which vertices {cert['vertices']}; facets {cert['facets']}",
             f"symmetric P = -P: {cert['symmetric']}; origin interior: {cert['origin_interior']}; "
             f"#int(P) cap Z^n = {cert['interior_lattice_points']}  =>  in W_n: {cert['in_W_n']}",
             f"G = L(1) = {cert['G']}; facet heights (u primitive): {cert['facet_heights']}",
             f"extra k values consistency-checked: {cert['checked_k']}"]
    lines += [f"g_{ii} = {cc}  (= {float(cc):.6f}; cube bound {2 ** ii * math.comb(cert['n'], ii)})"
              for ii, cc in enumerate(cert["coeffs"])]
    lines.append("VIOLATIONS of Wills' bounds: " + (", ".join(f"g_{ii} = {cc} > {bb}" for ii, cc, bb in cert["violations"])
                                                    if cert["violations"] else "none"))
    return "\n".join(lines)


def main():
    if len(sys.argv) != 2:
        sys.exit("usage: certify_member.py FILE")
    print(format_certificate(main_certify(read_points(sys.argv[1]))))


if __name__ == "__main__":
    main()
