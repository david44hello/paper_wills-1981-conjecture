# Wills' (1981) conjecture is fully resolved — Lean 4 formalization

This folder is the Lean folder of the computation repository of the paper "Wills' (1981) conjecture is fully
resolved" (Dave Goel). It formalizes in Lean 4 the deduction of Theorems 1.2, 1.3 and 7.1 and Corollary 1.4 from the
paper's computations and the cited theorems; it also formalizes most other claims of the paper, and AUDIT.md gives the
status of every claim.

## Directions to Reproduce

Memory in individual one-thread runs: the largest sampled resident size was about 7 GiB
(`Wills/Proofs/Slices/XInt2B.lean`). About 5 GiB was file-backed compiled code; the largest sampled working
memory was about 2 GiB per file. File-backed pages can be shared among processes. `lake build` may compile
several independent files at the same time, adding working memory for each process.

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone --branch v3.20 --single-branch https://github.com/david44hello/paper_wills-1981-conjecture.git
cd paper_wills-1981-conjecture/lean
./check.sh
```

Its last lines look like:

```
FINAL GATE PASS: placeholders only as whole bodies of the 0 listed OPEN rows; every other row PROVED or PROVED GIVEN; per-printed-claim table present.
PASS (final): project builds; source policy passes; the only gaps are the listed OPEN rows.
```

The proof takes as given 6 published facts that Lean's library lacks (Ehrhart theory, the facet formula,
triangulations of spheres, the tile theorem) and 5 computer checks (vol(W) = 386/15 and the results of Computations
1, 3, 4 and 5, run by `./reproduce.sh` in the repository folder `wills-1981-conjecture/`; the result of Computation 2
is proved in Lean); [AUDIT.md](AUDIT.md)
names them, claim by claim, and [AUDIT_NOTES.md](AUDIT_NOTES.md) explains the modelling.

Copyright (C) Dave Goel 2026--now. All rights reserved.
