# Wills' (1981) conjecture is fully resolved — Lean 4 proof

The paper: https://doi.org/10.5281/zenodo.23956181

This folder is the Lean folder of the computation repository of the paper "Wills' (1981) conjecture is fully
resolved" (Dave Goel). It proves in Lean 4 Theorems 1.2, 1.3 and 7.1 and Corollary 1.4, and most other claims of the
paper; AUDIT.md gives the status of every claim.

## Directions to Reproduce

The full build needs about 32 GB of memory (RAM plus swap): `Wills/Proofs/Sec7Counts.lean` and
`Wills/Proofs/CountW2.lean` need about 13 GB each, Mathlib's files about 6 GB more, and `lake build` may build the two
files at the same time.

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone --branch v1.90 --single-branch https://github.com/david44hello/paper_wills-1981-conjecture.git
cd paper_wills-1981-conjecture/lean
./check.sh
```

Its last lines look like:

```
FINAL GATE PASS: placeholders only as whole bodies of the 0 listed OPEN rows; every other row PROVED or PROVED GIVEN; per-printed-claim table present.
PASS (final): project builds; source policy passes; the only gaps are the listed OPEN rows.
```

The proof takes as given 7 published facts that Lean's library lacks (Ehrhart theory, the facet formula,
triangulations of spheres, the tile theorem, Wills' theorem for n = 3) and 6 computer checks (vol(W) = 386/15 and
Computations 1-5, run by `./reproduce.sh` in the repository folder `wills-1981-conjecture/`); [AUDIT.md](AUDIT.md)
names them, claim by claim, and [AUDIT_NOTES.md](AUDIT_NOTES.md) explains the modelling.

Copyright (C) Dave Goel 2026--now. All rights reserved.
