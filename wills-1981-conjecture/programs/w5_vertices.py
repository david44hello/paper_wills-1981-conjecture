#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# w5_vertices.py - the 58 vertices of W_5, the polytope found by search_layered.py (seed 2)
## version 0.10 - 20261102 - the version used for the runs reported in the paper
from ehrhart_exact import ehrhart, cube_coeffs
A_PAIRS = [(0, 0, 1, 0), (0, 1, -1, -1), (0, 1, -1, 0), (0, 1, 0, -1), (0, 1, 0, 0), (0, 1, 0, 1), (0, 1, 1, -1), (0, 1, 1, 1),
           (1, -1, -1, -1), (1, -1, 0, -1), (1, -1, 0, 1), (1, 0, -1, 1), (1, 0, 1, -1), (1, 1, -1, -1), (1, 1, -1, 1),
           (1, 1, 0, 1), (1, 1, 1, -1), (1, 1, 1, 1)]
B_POINTS = [(-1, -1, 1, 1), (-1, 0, -1, 0), (-1, 0, 0, 0), (-1, 0, 1, -1), (-1, 0, 1, 0), (-1, 1, -1, 0), (0, -1, -1, 1),
            (0, -1, 0, -1), (0, -1, 0, 0), (0, 0, -1, -1), (0, 0, -1, 0), (0, 0, -1, 1), (0, 0, 0, -1), (0, 0, 0, 0),
            (0, 0, 0, 1), (0, 1, -1, 0), (0, 1, 0, 1), (1, -1, 0, 1), (1, 0, -1, 1), (1, 0, 0, -1), (1, 0, 0, 0),
            (1, 0, 0, 1), (1, 0, 1, -1), (1, 0, 1, 0), (1, 1, 1, -1)]


def witness_points():
    rows = set()
    for v in A_PAIRS:
        rows.add(tuple(v) + (0,))
        rows.add(tuple(-c for c in v) + (0,))
    for v in B_POINTS:
        rows.add(tuple(v) + (1,))
        rows.add(tuple(-c for c in v) + (-1,))
    return sorted(rows)


if __name__ == "__main__":
    import numpy as np
    from scipy.spatial import ConvexHull
    pts = witness_points()
    assert all(tuple(-c for c in p) in set(pts) for p in pts), "not centrally symmetric"
    hull = ConvexHull(np.array(pts, dtype=float))
    verts = sorted({pts[i] for i in hull.vertices})
    coeffs, inner = ehrhart(verts)
    print("points:", len(pts), " hull vertices:", len(verts), " facets(simplices):", len(hull.simplices))
    print("interior lattice points of P:", inner)
    print("g =", [str(c) for c in coeffs], " cube:", [str(c) for c in cube_coeffs(5)])
    print("float volume (qhull):", hull.volume, " g_5 =", float(coeffs[5]))
    print("L(1) =", sum(coeffs))
    with open("witness_n5_vertices.txt", "w") as out:
        for v in verts:
            out.write(" ".join(str(c) for c in v) + "\n")
    print("vertices written: witness_n5_vertices.txt")
