#!/usr/bin/env bash
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# reproduce.sh - rerun the computations of the paper, one claim at a time, and check every number it states
# Usage: ./reproduce.sh <claim>   with <claim> one of the names printed by ./reproduce.sh (no argument)
# Each claim writes its outputs to out/<claim>/ and ends with the lines of programs/check_claims.py.
set -euo pipefail
cd "$(dirname "$0")"
HERE="$PWD"
P="$HERE/programs"
D="$HERE/data"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
LATTICES=$(seq 0 38)

CLAIMS="test theorem-1.3 computation-1 computation-2 computation-3 computation-4 computation-5 section-7
computation-6 computation-7 computation-8 computation-9 w5 deletions all"

say() { echo "== $*"; }

enter() {   # enter <claim>: a fresh, empty output folder
    if [ -e "out/$1" ]; then echo "out/$1 exists: move it away first (outputs are never overwritten)"; exit 2; fi
    mkdir -p "out/$1"
    cd "out/$1"
}

normaliz_run() {   # normaliz_run <input name in data/normaliz, without .in>
    command -v normaliz > /dev/null || { echo "normaliz not found (Normaliz 3.10.2 is needed)"; exit 2; }
    cp "$D/normaliz/$1.in" "$1.in"
    normaliz -x=1 -c "$1" > /dev/null
}

latte_run() {   # latte_run <input name in data/latte, without .vrep>: LattE integrale 1.7.6 on that vertex file
    command -v latte-count > /dev/null || { echo "latte-count not found (LattE integrale 1.7.6 is needed)"; exit 2; }
    cp "$D/latte/$1.vrep" "$1.vrep"
    latte-count --ehrhart-polynomial --vrep "$1.vrep" > "latte_$1.txt" 2>&1
}

sandwich_all() {   # sandwich_all <output file> <extra flags...>: the second Case III program on all 39 lattices
    local out="$1" idx
    shift
    : > "$out"
    for idx in $LATTICES; do
        python3 -u "$P/case3_sandwich.py" --sandwich --rank-prune "$@" --only-index "$idx" > "sandwich_idx$idx.log" 2>&1
        grep "^RESULT #$idx " "sandwich_idx$idx.log" >> "$out"
    done
}

TESTS="ehrhart_exact ehrhart_count ehrhart_probe set_guard generic_walk case1_walk case1_compare case2_walk walk_second
index_bound_second case3_frame_search boxes_list_first boxes_list_second boxes_walk_first boxes_walk_second boxes_compare
w_ehrhart_check w_deletions"

run_test() {   # every program's own test, with its exit code; case1_walk's test takes the number of random sets to check
    local prog rc
    for prog in $TESTS; do
        say "$prog --test"
        rc=0
        if [ "$prog" = case1_walk ]; then
            python3 "$P/$prog.py" --test 50 > "$prog.test.txt" 2>&1 || rc=$?
        else
            python3 "$P/$prog.py" --test > "$prog.test.txt" 2>&1 || rc=$?
        fi
        echo "$prog $rc" >> test_exit_codes.txt
        tail -1 "$prog.test.txt"
    done
}

run_theorem-1.3() {
    say "W: facets from all 5-subsets of vertices, direct counts of kW"
    cp "$D/w_pairs.txt" w_pairs.txt
    python3 "$P/w_ehrhart_check.py" --points w_pairs.txt --symmetrize > w_first.txt
    say "W: Normaliz"
    normaliz_run w
    say "W: LattE"
    latte_run w
    say "W: greedy reduction of W_5 with the exact counter of the search"
    cp "$D/w5_vertices.txt" witness_n5_vertices.txt
    python3 "$P/w5_reduction.py" > w_reduction.txt
}

run_computation-1() {
    say "Case I, first program (about 5 hours)"
    python3 "$P/case1_walk.py" --enumerate --min-g 31 --seconds 86400 --out case1_first_records.txt > case1_first.log
    say "Case I, second program (about 12 hours; checkpoints in case1_second/)"
    python3 "$P/walk_second.py" --start cube --group b4 --gmin 31 --ckpt case1_second > case1_second.txt
    python3 "$P/case1_compare.py" --first case1_first.log --second case1_second/rows.jsonl > case1_compare.txt
}

run_computation-2() {
    python3 "$P/index_bound_first.py" > index_first.txt
    python3 "$P/index_bound_second.py" > index_second.txt
}

run_computation-3() {
    python3 "$P/case2_walk.py" --min-g 31 > case2_first.txt
    local mm
    for mm in 2 3 4; do
        python3 "$P/walk_second.py" --start "gamma$mm" --group b4stab --gmin 31 --ckpt "case2_second_m$mm" > "case2_second_m$mm.txt"
    done
}

run_computation-4() {
    python3 "$P/frame_lattices_first.py" 24 > frames_first.txt
    python3 "$P/frame_lattices_second.py" --dmin 1 --dmax 23 --out frames_second.json > frames_second.txt
    python3 "$P/frame_lattices_orbits.py" > frames_orbits.txt
}

run_computation-5() {
    say "Case III, first program (hours)"
    python3 "$P/case3_run_all.py" --dmin 1 --dmax 23 --out case3_first_rank3.jsonl > case3_first.txt
    say "Case III, second program (hours)"
    sandwich_all case3_second_rank3.txt
    python3 "$P/case3_compare.py" --mode rank3 > case3_compare.txt
}

run_section-7() {
    python3 "$P/case3_frame_search.py" --only $LATTICES --max-rank 0 --min-g 31 --check-l6 200 --out case3_first_rank0.jsonl > /dev/null
    sandwich_all case3_second_rank0.txt --rank-cut 1
    python3 "$P/w_ehrhart_check.py" --all > tx_first.txt
    normaliz_run t
    normaliz_run x
}

run_computation-6() {
    local rho
    for rho in 0 1 2; do
        python3 "$P/case3_frame_search.py" --only $LATTICES --max-rank "$rho" --min-g 31 --check-l6 200 \
            --out "case3_first_rank$rho.jsonl" > /dev/null
    done
    sandwich_all case3_second_rank0.txt --rank-cut 1
    sandwich_all case3_second_rank1.txt --rank-cut 2
    sandwich_all case3_second_rank2.txt --rank-cut 3 --branch-rule hybrid
    say "the sets R_41 and R_39 (lattice #35): their points, one JSON line each"
    python3 -u "$P/case3_sandwich.py" --sandwich --rank-prune --rank-cut 2 --only-index 35 \
        --dump-leaves r41_r39_points.jsonl > sandwich_idx35_dump.log 2>&1
}

run_computation-7() {
    python3 "$P/boxes_list_first.py" --out boxes.jsonl > boxes_first.txt
    python3 "$P/boxes_list_second.py" --max-index 6 > boxes_second.txt
}

run_computation-8() {
    local box
    for box in 0 1 2 3; do
        say "box $box (the first program takes up to 3 hours per box)"
        python3 "$P/boxes_walk_first.py" --box "$box" --out "box${box}_first.log" > "box${box}_first_console.txt" 2>&1
        python3 "$P/boxes_walk_second.py" --box "$box" --min-g 31 > "box${box}_second.log" 2>&1
        python3 "$P/boxes_compare.py" --p1 "box${box}_first.log" --p2 "box${box}_second.log" > "box${box}_compare.txt"
    done
    for box in 4 5; do
        python3 "$P/boxes_walk_second.py" --box "$box" --min-g 31 > "box${box}_second.log" 2>&1
        python3 "$P/boxes_walk_second.py" --box "$box" --min-g 31 --no-cut > "box${box}_second_nocut.log" 2>&1
    done
    python3 "$P/boxes_small_third.py" > boxes_small_third.txt
}

run_computation-9() {
    cp "$D/x_points.txt" x_points.txt
    python3 "$P/x_growth.py" --start x_points.txt --runs 60 --seed 1 --frame > x_first.txt
    python3 "$P/x_maximal_check.py" > x_second.txt
}

run_w5() {
    python3 "$P/w5_vertices.py" > w5_search_counter.txt
    cp "$D/w5_vertices.txt" w5_vertices.txt
    python3 "$P/w_ehrhart_check.py" --points w5_vertices.txt > w5_first.txt
    normaliz_run w5
    latte_run w5
}

run_deletions() {
    python3 "$P/w_deletions.py" --run > deletions_first.txt
    local num
    for num in $(seq -w 0 24); do
        cp "$D/normaliz/deletions/d$num.in" "d$num.in"
        normaliz -x=1 -c "d$num" > /dev/null
    done
}

run_all() {
    local claim
    for claim in $CLAIMS; do
        [ "$claim" = all ] || (cd "$HERE" && "$HERE/reproduce.sh" "$claim")
    done
}

main() {
    local claim="${1:-}"
    if [ -z "$claim" ] || ! grep -qw -- "$claim" <<< "$CLAIMS"; then
        echo "usage: ./reproduce.sh <claim>   claims:" $CLAIMS
        exit 2
    fi
    if [ "$claim" = all ]; then run_all; return; fi
    enter "$claim"
    "run_$claim"
    cd "$HERE"
    python3 "$P/check_claims.py" "$claim" "out/$claim"
}
main "$@"
