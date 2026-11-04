#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# set_guard.py - the exact per-set guard of the first-program walks: saturation, one interior point, exact vertices
## version 0.10 - 20261102 - the version used for the runs reported in the paper
import sys

import numpy as np

GUARD_EXIT = 3


def guard_fail(name, mask, why):
    print(f"GUARD FAIL {name}: {why}; points {np.flatnonzero(mask).tolist()}", flush=True)
    sys.exit(GUARD_EXIT)


def exact_guard(points, mask, qhull_verts, normals, rhs, name):
    """Exact integer checks of one set S = points[mask], where points = ALL lattice points of the ambient polytope (box or
    cube) and (normals, rhs) = integer facet inequalities a.x <= b of conv S. Exits 3 on any failure.
    (1) every inequality holds on S (so conv S lies inside the polyhedron of the inequalities);
    (2) the ambient points inside that polyhedron are exactly S - all lattice points of conv S are ambient points, so S is
        saturated; (3) exactly one ambient point, the origin, is strictly inside every inequality (one interior point);
    (4) exact vertices = points p of S such that no other q in S is tight on every inequality tight at p. A point in the
        relative interior of a face of dim >= 1 is covered by a vertex of that face, so these are true vertices; they must
        equal qhull's list (a non-vertex in qhull's list would make an unsaturated child)."""
    values = points @ normals.T
    inside, strict = np.all(values <= rhs, axis=1), np.all(values < rhs, axis=1)
    if not np.all(inside[mask]):
        guard_fail(name, mask, "an integer facet inequality fails on S")
    if not np.array_equal(inside, mask):
        guard_fail(name, mask, f"NOT SATURATED: {int(inside.sum())} lattice points in conv S, {int(mask.sum())} in S")
    if strict.sum() != 1 or np.any(points[strict]):
        guard_fail(name, mask, f"{int(strict.sum())} interior lattice points (must be the origin only)")
    idx = np.flatnonzero(mask)
    tight = (values[idx] == rhs).astype(np.int64)
    shared, own = tight @ tight.T, tight.sum(axis=1)
    covered = (shared == own[:, None]).sum(axis=1) > 1  # another q is tight wherever p is
    exact_verts = set(idx[~covered].tolist())
    if exact_verts != {int(v) for v in qhull_verts}:
        guard_fail(name, mask, f"qhull vertices {sorted(int(v) for v in qhull_verts)} != exact {sorted(exact_verts)}")


def must_fire(points, mask, verts, normals, rhs, label):
    try:
        exact_guard(points, mask, verts, normals, rhs, label)
    except SystemExit as exc:
        assert exc.code == GUARD_EXIT
        return
    raise AssertionError(f"guard did not fire: {label}")


def main_test():
    """On the cube {-1,0,1}^4: the full cube passes; an unsaturated set (non-vertex pair removed), an added non-vertex and
    a dropped vertex each fire."""
    import itertools
    from case3_reverse_search import fast_facets
    points = np.array(list(itertools.product((-1, 0, 1), repeat=4)), dtype=np.int64)
    full = np.ones(len(points), dtype=bool)
    corners = np.flatnonzero(np.all(np.abs(points) == 1, axis=1))
    normals, rhs, _ = fast_facets(points)
    exact_guard(points, full, corners, normals, rhs, "cube (must pass)")
    lookup = {tuple(p): i for i, p in enumerate(points)}
    edge_mid, minus_mid = lookup[(1, 1, 1, 0)], lookup[(-1, -1, -1, 0)]
    holed = full.copy()
    holed[[edge_mid, minus_mid]] = False
    must_fire(points, holed, corners, *fast_facets(points[holed])[:2], "negative: unsaturated")
    must_fire(points, full, np.append(corners, edge_mid), normals, rhs, "negative: added non-vertex")
    must_fire(points, full, corners[1:], normals, rhs, "negative: dropped vertex")
    print("set_guard TEST PASS (cube passes; unsaturated, added non-vertex, dropped vertex all fire)")


if __name__ == "__main__":
    if sys.argv[1:] != ["--test"]:
        sys.exit("usage: set_guard.py --test")
    main_test()
