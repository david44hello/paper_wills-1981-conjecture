#!/usr/bin/env python3
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# x_maximal_check.py - enlargements of X, second program: X cannot be enlarged inside its frame V[-1,1]^4
## version 0.10 - 20261102 - the version used for the runs reported in the paper
"""X = conv{+-v_1..+-v_4}, v = (1,0,0,0), (0,1,0,0), (1,1,3,0), (2,4,3,6), |det| = 18.
If P contains X and its max |det| of 4 lattice points is 18, then (Cramer) every lattice point of P lies in the frame
V[-1,1]^4. This program lists the frame's lattice points, and for every frame point x outside X it tests whether
conv(X u {+-x}) still has 0 as its only interior lattice point. Expected: 417 frame points, 33 in X,
192 outside pairs, and every one of them creates an extra interior lattice point."""
import argparse
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from ehrhart_probe import exact_facets  # noqa: E402

FRAME = np.array([[1, 0, 0, 0], [0, 1, 0, 0], [1, 1, 3, 0], [2, 4, 3, 6]], dtype=np.int64)  # rows = v_i


def integer_adjugate(matrix):
    """Exact integer adjugate and determinant of a small integer matrix (cofactor expansion via numpy rounding check)."""
    det = int(round(np.linalg.det(matrix.astype(float))))
    adj = np.rint(np.linalg.inv(matrix.astype(float)) * det).astype(np.int64)
    if not np.array_equal(matrix @ adj, det * np.eye(len(matrix), dtype=np.int64)):
        raise RuntimeError("adjugate not exact")
    return adj, det


def box_around(rows):
    """All integer points of the axis box that contains V[-1,1]^4 (half-widths = column sums of |v_i|)."""
    half = np.abs(rows).sum(axis=0)
    axes = [np.arange(-hh, hh + 1, dtype=np.int64) for hh in half]
    grid = np.stack(np.meshgrid(*axes, indexing="ij"), axis=-1)
    return grid.reshape(-1, len(half))


def frame_coordinates(points, rows):
    """c-coordinates times |det|: x = sum c_i v_i  <=>  c = x V^{-1}; returns integer det*c and |det|."""
    adj, det = integer_adjugate(rows)   # rows @ adj = det I  =>  V^{-1} (rows form) = adj / det
    scaled = points @ adj
    if det < 0:
        scaled, det = -scaled, -det
    return scaled, det


def interior_count(vertices, grid):
    """Number of grid points strictly inside conv(vertices)."""
    normals, offsets = exact_facets(vertices)
    return int(np.all(grid @ normals.T < offsets, axis=1).sum())


def main_check():
    grid = box_around(FRAME)
    scaled, det = frame_coordinates(grid, FRAME)
    in_frame = np.all(np.abs(scaled) <= det, axis=1)
    in_x = np.abs(scaled).sum(axis=1) <= det
    frame_pts, x_pts = grid[in_frame], grid[in_x]
    xverts = np.vstack([FRAME, -FRAME])
    print("det", det, "| frame points", len(frame_pts), "| X points", len(x_pts),
          "| X interior", interior_count(np.vstack([xverts, [[0, 0, 0, 0]]]), grid))
    outside = [pt for pt, inx in zip(frame_pts, in_x[in_frame]) if not inx]
    pairs = [pt for pt in outside if tuple(pt) > tuple(-pt)]
    bad = []
    for pt in pairs:
        count = interior_count(np.vstack([xverts, [pt], [-pt]]), grid)
        if count <= 1:
            bad.append(pt.tolist())
    print("outside pairs", len(pairs), "| pairs keeping W_4 (should be 0):", len(bad), bad[:5])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    main_check()


if __name__ == "__main__":
    main()
