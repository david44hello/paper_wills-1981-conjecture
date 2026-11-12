#!/usr/bin/env python3
"""audit.py — the claim audit of the Wills project: Lean's own `#print axioms` and declared signatures, row by row and
per printed claim.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Usage: python3 scripts/audit.py          checks that the build is current (`lake build --no-build Wills.Paper.Statements`,
                                         which builds nothing), then runs `lake env lean` (one Lean thread) on the
                                         generated probe
       python3 scripts/audit.py --test   self-test, no Lean
Paths are relative to the folder above scripts/ (found from this file's own location).
Reads:  Wills/Paper/Statements.lean, the Wills sources (axiom scan), CLAIM_MAP.tsv (loud warning if missing).
Writes: AUDIT.md, CLAIMS.json (the same bytes on every run of the same tree), logs/audit_{probe.lean,probe.log,built.log}
        (logs/ is outside Wills/, whose every module the lakefile builds; Git ignores it).
Row status, from Lean's output only:
  PROVED                  axioms within propext, Classical.choice, Quot.sound, and no fact or check binder
  PROVED GIVEN <names>    PROVED, with facts (Wills/Facts) and computer checks (Wills/Checks) as explicit hypotheses,
                          recognised by the binder's TYPE (FACTS, CHECKS below); <names> = their short names, facts first,
                          then checks, in the fixed order of those tables
  OPEN                    depends on sorryAx (and nothing non-standard besides)
  VIOLATION               any other axiom: the audit FAILS (after writing the reports)
  Binder guards (the audit FAILS): a fact/check binder carries its own name (hE1 : EhrhartLeading, hC2 : Comp2, ...),
  or that name with Lean's unused mark "_" (_hE3); a reserved name (hEHR ... hC5, with or without "_") carries its
  own type; a binder typed by a constant declared in a Wills.Facts or
  Wills.Checks module is a known fact or check.
Printed claims (CLAIM_MAP: EXACTLY 5 TAB-separated fields id, description, REQUIRED, SUPPORT, KIND; "-" = an empty
  field; '#' lines are comments; the map's own header explains the columns):
  KIND "-": REQUIRED = alternatives separated by '|'; one alternative = comma-listed rows that must ALL hold, so its
    status is its worst row (OPEN if any row is OPEN, else PROVED GIVEN the union of the rows' hypotheses, else PROVED).
    Claim status = the best alternative (PROVED > PROVED GIVEN, fewer hypotheses first > OPEN). REQUIRED = PENDING
    (rows not stated yet) counts as OPEN. An empty REQUIRED FAILS.
  KIND "FACT <Prop>", "CHECK <P1>,<P2>", "NOT-FORMALIZED faces": a fixed status text (kind_status); a non-empty
    REQUIRED, or an unknown kind, fact or check, FAILS.
  SUPPORT rows are listed only. VIOLATION in any row the claim names = VIOLATION.
  A map row that is not a Statements theorem FAILS the audit; a theorem named by no claim is a WARNING.
"""
import json
from pathlib import Path
import re
import subprocess
import sys

PROJECT = Path(__file__).resolve().parent.parent
LIB = "Wills"
NAMESPACE = LIB
STATEMENTS_REL = LIB + "/Paper/Statements.lean"
STATEMENTS = PROJECT / STATEMENTS_REL
STATEMENTS_MODULE = LIB + ".Paper.Statements"
CLAIM_MAP_REL = "CLAIM_MAP.tsv"
CLAIM_MAP = PROJECT / CLAIM_MAP_REL
LOGS = PROJECT / "logs"
# The two Lean processes run with one Lean thread.
LEAN_ENV = ["env", "LEAN_NUM_THREADS=1"]
LEAN_OPTIONS = ["-j1", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false"]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
OPEN_AXIOM = "sorryAx"
VERSION = "0.71"
PAPER = "Wills' (1981) conjecture is fully resolved"
TEXT_LINE = ("Paper text: the paper's TeX source, version 3.20 (md5 47e41917); the pointers l.N in the rows "
             "are its lines.")
# Facts the paper uses from areas Lean's library lacks: binder type -> (short name, binder name, area).
FACTS = {
    "Wills.EhrhartThm": ("EHR", "hEHR", "Ehrhart theory"),
    "Wills.EhrhartLeading": ("E1", "hE1", "Ehrhart theory"),
    "Wills.EhrhartReciprocity": ("E2", "hE2", "Ehrhart theory"),
    "Wills.FacetFormula": ("E3", "hE3", "facets of polytopes"),
    "Wills.BoundaryTriangulation": ("TRI", "hTRI", "triangulations of spheres, f-vectors and facets of polytopes"),
    "Wills.CrossPolytopeNoTiling": ("TILE", "hTILE", "tilings and facets of polytopes"),
}
# Computer checks (checked by computer, NOT proved in Lean): binder type -> (short name, binder name).
CHECKS = {"Wills.VolW": ("VolW", "hVolW"), **{f"Wills.Comp{n}": (f"Comp{n}", f"hC{n}") for n in range(1, 6)}}
HYPOTHESES = {type_name: entry[:2] for type_name, entry in (FACTS | CHECKS).items()}
ORDER = [short for short, _ in HYPOTHESES.values()]                       # facts first, then checks
RESERVED = {binder: type_name for type_name, (_, binder) in HYPOTHESES.items()}
HYPOTHESIS_MODULES = (LIB + ".Facts", LIB + ".Checks")
# The claim map's CHECK names -> the keys of ./reproduce.sh that rerun them.
REPRODUCE_KEYS = {"VolW": "theorem-1.3", "Comp1Max": "computation-1",
                  **{f"Comp{n}{suffix}": f"computation-{n}" for n in range(1, 6) for suffix in ("", "Count")}}
NOT_FORMALIZED = {"faces": "NOT FORMALIZED (no faces of polytopes in Lean's library)"}
WORDS = ("PROVED", "PROVED GIVEN", "OPEN", "VIOLATION", "CHECKED BY COMPUTER", "NOT FORMALIZED")  # totals order
CLAIM_ONLY = {"CHECKED BY COMPUTER", "NOT FORMALIZED"}                     # shown in a totals line only when nonzero
RANK = {"PROVED": 0, "PROVED GIVEN": 1, "OPEN": 2}                         # best first


def fail(message):
    raise SystemExit("AUDIT FAILED: " + message)


def warn(message):
    print("AUDIT WARNING: " + message, file=sys.stderr)


def mask_comments(text):
    """Preserve offsets/newlines while removing nested Lean comments and strings."""
    chars = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                chars[i:i+2] = "  "; depth += 1; i += 2
            elif text.startswith("-/", i):
                chars[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if text[i] != "\n": chars[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                chars[i:i+2] = "  "; i += 2
            else:
                if text[i] != "\n": chars[i] = " "
                if text[i] == '"': string = False
                i += 1
        elif text.startswith("/-", i):
            chars[i:i+2] = "  "; depth = 1; i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0: end = len(text)
            chars[i:end] = " " * (end-i); i = end
        elif text[i] == '"':
            chars[i] = " "; string = True; i += 1
        else:
            i += 1
    if depth or string:
        fail("unterminated comment/string")
    return "".join(chars)


def doc_first_line(text, offset):
    """First non-empty line of the docstring that directly precedes offset ('' if there is none)."""
    before = text[:offset].rstrip()
    start = before.rfind("/--")
    if not before.endswith("-/") or start < 0 or "-/" in before[start + 3:-2]:
        return ""
    lines = [line.strip() for line in before[start + 3:-2].splitlines() if line.strip()]
    return lines[0] if lines else ""


def parse_statements(text):
    """Plain, line-start theorem declarations, as required by the Statements contract."""
    clean = mask_comments(text)
    heads = list(re.finditer(r"^theorem\s+([A-Za-z_][\w']*)(?=\s)", clean, re.M))
    if len(heads) != len(re.findall(r"\btheorem\b", clean)):
        fail("unsupported theorem syntax; use plain line-start theorem declarations")
    if re.search(r"\b(?:lemma|example|axiom|opaque|def|abbrev|constant)\b", clean):
        fail("Statements may contain only theorem rows, imports, namespaces and comments")
    items = [{"name": head.group(1), "line": text.count("\n", 0, head.start()) + 1,
              "claim": doc_first_line(text, head.start())} for head in heads]
    names = [item["name"] for item in items]
    if not names or len(names) != len(set(names)):
        fail("empty or duplicate theorem inventory")
    return items


def is_backup(relative):
    return "versions" in Path(relative).parts


def lean_sources(tree):
    """{relative path: text} of the library's Lean sources; backups in any versions/ folder are not sources."""
    paths = [tree / (LIB + ".lean"), *sorted((tree / LIB).rglob("*.lean"))]
    return {str(path.relative_to(tree)): path.read_text(encoding="utf-8")
            for path in paths if not is_backup(path.relative_to(tree))}


def axiom_declarations(sources):
    """'file:line' of every `axiom` keyword outside comments and strings. This project declares no axioms at all."""
    return [f"{name}:{text.count(chr(10), 0, match.start()) + 1}" for name, text in sources.items()
            for match in re.finditer(r"\baxiom\b", mask_comments(text))]


def row_list(field):
    return [row.strip().removeprefix(NAMESPACE + ".") for row in field.split(",") if row.strip()]


def field_value(field):
    """A claim-map field; "-" marks an empty field (editors strip trailing TABs)."""
    field = field.strip()
    return "" if field == "-" else field


def fact_status(number, prop):
    entry = FACTS.get(NAMESPACE + "." + prop)
    if not entry: fail(f"claim map line {number}: unknown fact {prop!r} (known: {', '.join(FACTS)})")
    return f"NOT FORMALIZED (fact {prop}: no {entry[2]} in Lean's library)"


def check_status(number, field):
    checks = [name.strip() for name in field.split(",")]
    unknown = [name for name in checks if name not in REPRODUCE_KEYS]
    if unknown: fail(f"claim map line {number}: unknown check(s) {unknown} (known: {', '.join(REPRODUCE_KEYS)})")
    keys = " ".join(dict.fromkeys(REPRODUCE_KEYS[name] for name in checks))
    return f"CHECKED BY COMPUTER ({', '.join(checks)}), NOT proved in Lean: ./reproduce.sh {keys}"


def kind_status(number, kind):
    """The fixed status text of a KIND other than "-"."""
    word, _, rest = kind.partition(" ")
    rest = rest.strip()
    if word == "FACT": return fact_status(number, rest)
    if word == "CHECK": return check_status(number, rest)
    if word == "NOT-FORMALIZED" and rest in NOT_FORMALIZED: return NOT_FORMALIZED[rest]
    fail(f"claim map line {number}: unknown KIND {kind!r} (FACT <Prop>, CHECK <P1>,<P2>, NOT-FORMALIZED faces, or -)")


def parse_claim_line(number, line):
    fields = line.split("\t")
    if len(fields) != 5:
        fail(f"claim map line {number}: need 5 tab-separated fields (id, description, REQUIRED, SUPPORT, KIND; "
             f'"-" = empty), got {len(fields)}')
    claim_id, description, required, support, kind = (field_value(field) for field in fields)
    if kind and required: fail(f"claim map line {number}: KIND {kind!r} needs an empty REQUIRED, got {required!r}")
    if not kind and not required: fail(f"claim map line {number}: no REQUIRED rows and no KIND")
    pending = required == "PENDING"   # rows not yet stated: the claim counts as OPEN
    alternatives = [] if pending or not required else [row_list(alternative) for alternative in required.split("|")]
    if any(not alternative for alternative in alternatives): fail(f"claim map line {number}: empty REQUIRED alternative")
    return {"id": claim_id, "description": description, "required": alternatives, "pending": pending,
            "support": row_list(support), "kind": kind or None,
            "kind_status": kind_status(number, kind) if kind else None, "line": number}


def named_rows(claim):
    return [row for alternative in claim["required"] for row in alternative] + claim["support"]


def parse_claim_map(text, names):
    """The claim lines (see the module docstring). Returns (claims, Statements theorems named by no claim)."""
    claims = [parse_claim_line(number, line) for number, line in enumerate(text.splitlines(), 1)
              if line.strip() and not line.lstrip().startswith("#")]
    ids = [claim["id"] for claim in claims]
    if not claims or "" in ids or len(ids) != len(set(ids)): fail("claim map: empty, blank or duplicate claim ids")
    named = {row for claim in claims for row in named_rows(claim)}
    unknown = sorted(named - set(names))
    if unknown: fail("claim map rows that are not Statements theorems: " + ", ".join(unknown))
    return claims, [name for name in names if name not in named]


def probe_text(names):
    lines = ["-- Generated by scripts/audit.py; do not edit. Compiled with `lake env lean`.",
             f"import {STATEMENTS_MODULE}", "import Lean", "open Lean Elab Command", "",
             "/-- The module that declares a constant (`_` if none). -/",
             "def willsAuditModule (env : Environment) (c : Name) : String :=",
             "  match (env.getModuleIdxFor? c).bind (fun idx => env.header.moduleNames[idx.toNat]?) with",
             "  | some m => m.toString",
             '  | none => "_"', "",
             "/-- `name:Type:Module` of one binder: `Type` = the binder type's constant name and `Module` = its module,",
             "both `_` when the binder type is not a constant (definitions are NOT unfolded). -/",
             "def willsAuditEntry (env : Environment) (name : Name) (type : Expr) : String :=",
             "  match type.consumeMData with",
             '  | .const c _ => s!"{name.eraseMacroScopes}:{c}:{willsAuditModule env c}"',
             '  | _ => s!"{name.eraseMacroScopes}:_:_"', "",
             "/-- The binders of the Pi spine of a declared type, outermost first. -/",
             "partial def willsAuditPiBinders (env : Environment) : Expr → List String",
             "  | .forallE name type body _ => willsAuditEntry env name type :: willsAuditPiBinders env body",
             "  | .mdata _ inner => willsAuditPiBinders env inner",
             "  | _ => []", "",
             "/-- Prints `WILLSBINDERS|<row>|<name:Type:Module, comma-separated>|END`. -/",
             "def willsAuditBinders (decl : Name) (row : String) : CommandElabM Unit := do",
             "  let env ← getEnv",
             "  let info ← getConstInfo decl",
             '  logInfo m!"WILLSBINDERS|{row}|{",".intercalate (willsAuditPiBinders env info.type)}|END"', ""]
    for name in names:
        lines += [f"#print axioms {NAMESPACE}.{name}", f'run_cmd willsAuditBinders ``{NAMESPACE}.{name} "{name}"']
    return "\n".join(lines) + "\n"


def run_logged(command, log):
    """Runs command in the project folder; its whole output goes to log. Returns (exit status, output)."""
    proc = subprocess.run(LEAN_ENV + command, cwd=PROJECT, capture_output=True, text=True)
    output = proc.stdout + proc.stderr
    log.write_text(output, encoding="utf-8")
    return proc.returncode, output


def check_built(log):
    """Lake's own hash-based check (builds nothing): the oleans the probe imports must match the current sources."""
    status, _ = run_logged(["lake", "build", "--no-build", STATEMENTS_MODULE], log)
    if status:
        fail(f"{STATEMENTS_MODULE} is not built from the current sources (lake build --no-build rc {status}; "
             f"see {log.relative_to(PROJECT)}). Build it first: lake build {LIB}")


def run_probe(names):
    probe, log = LOGS / "audit_probe.lean", LOGS / "audit_probe.log"
    probe.write_text(probe_text(names), encoding="utf-8")
    status, output = run_logged(["lake", "env", "lean", *LEAN_OPTIONS, str(probe.relative_to(PROJECT))], log)
    if status: fail(f"Lean failed on the probe (rc {status}); see {log.relative_to(PROJECT)}\n" + output[-3000:])
    return output


def parse_axioms(output, names):
    result = {}
    for match in re.finditer(r"'([\w.']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", output, re.S):
        if not match.group(1).startswith(NAMESPACE + "."): continue
        name = match.group(1).removeprefix(NAMESPACE + ".")
        if name in result: fail("duplicate axiom output for " + name)
        result[name] = {a.strip() for a in (match.group(2) or "").split(",") if a.strip()}
    if set(names) != set(result): fail("missing/unexpected axiom rows: " + str(set(names) ^ set(result)))
    return result


def parse_binders(output, names):
    """{row: [(binder name, type constant or '_', module or '_')]}, in signature order, from the WILLSBINDERS lines."""
    result = {}
    for match in re.finditer(r"WILLSBINDERS\|([^|\n]+)\|([^|\n]*)\|END", output):
        name, field = match.groups()
        if name in result: fail("duplicate binder inspection for " + name)
        entries = [entry.split(":") for entry in field.split(",") if entry]
        if any(len(entry) != 3 for entry in entries): fail(f"malformed binder inspection for {name}: {field}")
        result[name] = [tuple(entry) for entry in entries]
    if set(names) != set(result): fail("missing/unexpected binder inspections: " + str(set(names) ^ set(result)))
    return result


def in_hypothesis_module(module):
    return any(module == prefix or module.startswith(prefix + ".") for prefix in HYPOTHESIS_MODULES)


def hypotheses_of(row, binders):
    """Short names of the row's fact/check binders, facts first, in ORDER; FAILS on a mislabelled binder."""
    found = set()
    for binder, type_name, module in binders:
        if type_name in HYPOTHESES:
            short, expected = HYPOTHESES[type_name]
            if binder not in (expected, "_" + expected):           # "_": Lean's mark of an unused hypothesis
                fail(f"row {row}: binder {binder} : {type_name} must be named {expected} (or _{expected})")
            found.add(short)
        elif binder.removeprefix("_") in RESERVED:
            fail(f"row {row}: binder {binder} has type {type_name}, not {RESERVED[binder.removeprefix('_')]}")
        elif in_hypothesis_module(module):
            fail(f"row {row}: binder {binder} : {type_name} (declared in {module}) is no known fact or check; "
                 "add it to FACTS or CHECKS of scripts/audit.py")
    return [short for short in ORDER if short in found]


def classify(axioms, hypotheses):
    if axioms - STANDARD - {OPEN_AXIOM}: return "VIOLATION"
    if OPEN_AXIOM in axioms: return "OPEN"
    return "PROVED GIVEN " + ", ".join(hypotheses) if hypotheses else "PROVED"


def status_word(status):
    """The totals word of a status ('PROVED GIVEN E1, Comp2' -> 'PROVED GIVEN', 'NOT FORMALIZED (...)' -> ...)."""
    for word in sorted(WORDS, key=len, reverse=True):
        if status == word or status.startswith(word + " "): return word
    fail("unknown status " + status)


def alternative_status(rows):
    """All rows of one REQUIRED alternative must hold: (status, hypotheses) of its worst row, hypotheses united."""
    if any(row["status"] == "OPEN" for row in rows): return "OPEN", []
    found = {name for row in rows for name in row["hypotheses"]}
    hypotheses = [short for short in ORDER if short in found]
    return ("PROVED GIVEN " + ", ".join(hypotheses) if hypotheses else "PROVED"), hypotheses


def claim_status(claim, rows_by_name):
    """(status, best REQUIRED alternative) of one printed claim."""
    if any(rows_by_name[name]["status"] == "VIOLATION" for name in named_rows(claim)): return "VIOLATION", []
    if claim.get("kind_status"): return claim["kind_status"], []
    if claim.get("pending"): return "OPEN", []
    options = [(alternative_status([rows_by_name[name] for name in alternative]), alternative)
               for alternative in claim["required"]]
    (status, _), best = min(options, key=lambda option: (RANK[status_word(option[0][0])], len(option[0][1])))
    return status, best


def count_words(statuses):
    counts = {word: 0 for word in WORDS}
    for status in statuses: counts[status_word(status)] += 1
    return counts


def totals_line(label, counts):
    shown = [f"{word} {counts[word]}" for word in WORDS if counts[word] or word not in CLAIM_ONLY]
    return f"{label}: {sum(counts.values())} — " + ", ".join(shown) + "."


def cell(value):
    return str(value).replace("|", "\\|").replace("\n", " ")


def render_rows(rows):
    table = ["| # | Lean name | Paper claim | Status |", "|---|---|---|---|"]
    table += [f'| {i} | `{row["name"]}` | {cell(row["claim"] or "(NO DOCSTRING)")} | {cell(row["status"])} |'
              for i, row in enumerate(rows, 1)]
    return table


def render_printed(printed, uncovered):
    table = ["| Claim | Description | Status | Best alternative | REQUIRED (alternatives) | SUPPORT |",
             "|---|---|---|---|---|---|"]
    table += [f'| {cell(claim["id"])} | {cell(claim["description"])} | {cell(claim["status"])} | '
              f'{cell(", ".join(claim["best_alternative"]) or "—")} | '
              f'{cell(" | ".join(", ".join(alternative) for alternative in claim["required"]) or "—")} | '
              f'{cell(", ".join(claim["support"]) or "—")} |' for claim in printed]
    if uncovered:
        table += ["", f"WARNING: {len(uncovered)} Statements theorem(s) in no printed claim: "
                  + ", ".join(f"`{name}`" for name in uncovered)]
    return table


def legend():
    facts = ", ".join(f"{short} ({type_name.removeprefix(NAMESPACE + '.')})"
                      for type_name, (short, _, _) in FACTS.items())
    checks = ", ".join(short for short, _ in CHECKS.values())
    return ("PROVED = only propext, Classical.choice, Quot.sound, and no fact or check among the hypotheses. "
            "PROVED GIVEN <names> = PROVED, with the named facts and computer checks entered as explicit hypotheses "
            f"(recognised by their types). Facts, from areas Lean's library lacks (Wills/Facts): {facts}. Computer "
            f"checks, NOT proved in Lean (Wills/Checks): {checks}. OPEN = depends on sorryAx. VIOLATION = any other "
            "axiom (the audit fails). Semantic fidelity to the paper is NOT checked here.")


def render(rows, printed, uncovered):
    text = [f"# Claim audit of {STATEMENTS_REL}", "",
            f"Generated by scripts/audit.py (version {VERSION}) from Lean's `#print axioms` output and the declared "
            f"signatures of `{STATEMENTS_REL}`.", "", TEXT_LINE, "",
            totals_line("Rows", count_words(row["status"] for row in rows)), "", legend(), "",
            "## Rows (Statements theorems)", "", *render_rows(rows), "", "## Per printed claim", ""]
    if printed is None:
        text += [f"NOT PRODUCED: no claim map at `{CLAIM_MAP_REL}`.", ""]
    else:
        text += [totals_line("Printed claims", count_words(claim["status"] for claim in printed)), "",
                 f"From `{CLAIM_MAP_REL}`. KIND \"-\": status = the best REQUIRED alternative; an alternative is as good "
                 "as its worst row (hypotheses of its rows united). KIND FACT, CHECK or NOT-FORMALIZED: the fixed "
                 "status text of that kind. SUPPORT rows do not change the status.", "",
                 *render_printed(printed, uncovered), ""]
    return "\n".join(text) + "\n"


def read_claim_map(names):
    if not CLAIM_MAP.exists():
        warn(f"no claim map at {CLAIM_MAP_REL}: the per-printed-claim table is NOT produced")
        return None, None
    return parse_claim_map(CLAIM_MAP.read_text(encoding="utf-8"), names)


def build_rows(items, axioms, binders):
    rows = []
    for item in items:
        name = item["name"]
        hypotheses = hypotheses_of(name, binders[name])
        rows.append(dict(item, qualified_name=NAMESPACE + "." + name, axioms=sorted(axioms[name]),
                         hypotheses=hypotheses, binders=[f"{binder} : {type_name}" for binder, type_name, _ in binders[name]],
                         status=classify(axioms[name], hypotheses)))
    return rows


def build_printed(claims, rows):
    if claims is None: return None
    rows_by_name = {row["name"]: row for row in rows}
    printed = []
    for claim in claims:
        status, best = claim_status(claim, rows_by_name)
        printed.append(dict(claim, status=status, best_alternative=best))
    return printed


def write_reports(rows, printed, uncovered):
    (PROJECT / "AUDIT.md").write_text(render(rows, printed, uncovered), encoding="utf-8")
    data = {"version": VERSION, "paper": PAPER, "namespace": NAMESPACE, "statements": STATEMENTS_REL,
            "counts": count_words(row["status"] for row in rows), "claims": rows,
            "claim_map": CLAIM_MAP_REL if printed is not None else None,
            "printed_claim_counts": count_words(c["status"] for c in printed) if printed is not None else None,
            "printed_claims": printed, "rows_in_no_claim": uncovered}
    (PROJECT / "CLAIMS.json").write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def report_to_stdout(rows, printed, uncovered):
    print(totals_line("AUDIT rows", count_words(row["status"] for row in rows)))
    for row in rows:
        if not row["claim"]: warn(f"row {row['name']} (Statements l.{row['line']}) has no docstring")
    if printed is not None:
        print(totals_line("AUDIT printed claims", count_words(claim["status"] for claim in printed)))
        print("\n".join(render_printed(printed, [])))
    if uncovered: warn(f"{len(uncovered)} Statements theorem(s) in no printed claim: " + ", ".join(uncovered))
    print("wrote AUDIT.md and CLAIMS.json")


def main_audit():
    text = STATEMENTS.read_text(encoding="utf-8")
    items = parse_statements(text)
    names = [item["name"] for item in items]
    declared = axiom_declarations(lean_sources(PROJECT))
    if declared: fail("axiom declarations in the Wills sources (this project allows none): " + ", ".join(declared))
    claims, uncovered = read_claim_map(names)
    LOGS.mkdir(exist_ok=True)
    check_built(LOGS / "audit_built.log")
    output = run_probe(names)
    if STATEMENTS.read_text(encoding="utf-8") != text:
        fail(f"{STATEMENTS_REL} changed during the audit (rows and docstrings may not match the probed oleans); rerun")
    rows = build_rows(items, parse_axioms(output, names), parse_binders(output, names))
    printed = build_printed(claims, rows)
    write_reports(rows, printed, uncovered)
    report_to_stdout(rows, printed, uncovered)
    bad = [row["name"] for row in rows if row["status"] == "VIOLATION"]
    if bad: fail("VIOLATION rows (non-standard axioms): " + ", ".join(bad))


def expect_fail(function, *args):
    try: function(*args)
    except SystemExit: return
    raise AssertionError(f"{function.__name__} accepted bad input {args!r}")


def test_statements():
    sample = ("/-- Row 1 — Lemma 2.2 | first line.\nsecond line. -/\ntheorem foo' (hE1 : True) : True := by trivial\n"
              "/-- Row 2 — one line -/\ntheorem bar : True := by\n  sorry\n/-! section -/\ntheorem nodoc : True := trivial\n"
              "end Wills\n")
    rows = parse_statements(sample)
    assert [r["name"] for r in rows] == ["foo'", "bar", "nodoc"] and rows[1]["line"] == 5
    assert [r["claim"] for r in rows] == ["Row 1 — Lemma 2.2 | first line.", "Row 2 — one line", ""]
    for bad in ["theorem a : True := trivial\n theorem hidden : True := trivial", "lemma hidden : True := trivial",
                "theorem a : True := trivial\naxiom b : True", "theorem a : True := trivial\ntheorem a : True := trivial"]:
        expect_fail(parse_statements, bad)
    assert "theorem" not in mask_comments('/- outer /- theorem -/ more -/ "theorem"')
    return rows


def test_sources():
    assert is_backup("Wills/Paper/versions/Statements_version_0.71.lean") and is_backup("versions/a.lean")
    assert not is_backup("Wills/Paper/Statements.lean")
    sources = {"Wills/A.lean": "-- an axiom here is a comment\n/-- axiom -/\ntheorem t : True := trivial\n",
               "Wills/B.lean": 'def s := "axiom"\n\nprivate axiom evil : False\n'}
    assert axiom_declarations(sources) == ["Wills/B.lean:3"]


SAMPLE_OUTPUT = ("'Wills.foo'' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
                 "'Wills.bar' depends on axioms: [propext, sorryAx]\n'Wills.nodoc' does not depend on any axioms\n"
                 "'Other.lemma' depends on axioms: [propext]\n"
                 "x.lean:9:0: info:WILLSBINDERS|foo'|hC2:Wills.Comp2:Wills.Checks.Computations,n:Nat:Init.Prelude,"
                 "hE1:Wills.EhrhartLeading:Wills.Facts.Basic,P:_:_,hP:_:_|END\n"
                 "WILLSBINDERS|bar|hE3:Wills.FacetFormula:Wills.Facts.Basic|END\nWILLSBINDERS|nodoc||END\n")


def test_lean_output(names):
    axioms, binders = parse_axioms(SAMPLE_OUTPUT, names), parse_binders(SAMPLE_OUTPUT, names)
    hyps = {name: hypotheses_of(name, binders[name]) for name in names}
    assert hyps == {"foo'": ["E1", "Comp2"], "bar": ["E3"], "nodoc": []}            # facts first, then checks
    statuses = [classify(axioms[n], hyps[n]) for n in names]
    assert statuses == ["PROVED GIVEN E1, Comp2", "OPEN", "PROVED"]
    for bad in ({"evil"}, {"evil", "sorryAx"}, {"Lean.ofReduceBool", "propext"}):
        assert classify(bad, []) == "VIOLATION"
    expect_fail(parse_axioms, SAMPLE_OUTPUT.replace("'Wills.bar'", "'Wills.other'"), names)
    expect_fail(parse_axioms, SAMPLE_OUTPUT + "'Wills.Rows1.extra' depends on axioms: [propext]\n", names)
    expect_fail(parse_binders, SAMPLE_OUTPUT + "WILLSBINDERS|bar||END\n", names)
    expect_fail(parse_binders, SAMPLE_OUTPUT.replace("hE3:Wills.FacetFormula:Wills.Facts.Basic", "hE3:Wills"), names)
    for mislabelled in [("h", "Wills.EhrhartLeading", "Wills.Facts.Basic"),      # fact binder with a wrong name
                        ("hC1", "Wills.Comp2", "Wills.Checks.Computations"),     # check binder with another's name
                        ("hE1", "Nat", "Init.Prelude"), ("hVolW", "_", "_"),     # reserved name, wrong type
                        ("_hE1", "Nat", "Init.Prelude"),                         # unused reserved name, wrong type
                        ("_hE1", "Wills.FacetFormula", "Wills.Facts.Basic"),     # unused fact binder, wrong name
                        ("hC1c", "Wills.Comp1Count", "Wills.Checks.Computations")]:  # unmapped Prop of Wills/Checks
        expect_fail(hypotheses_of, "row", [mislabelled])
    assert hypotheses_of("row", [("h", "Wills.Pt", "Wills.Defs.Basic"), ("hX", "Wills.FactsExtra", "Wills.FactsX")]) == []
    assert hypotheses_of("row", [("_hE3", "Wills.FacetFormula", "Wills.Facts.Basic")]) == ["E3"]  # unused, still named
    return axioms, binders


def test_claim_map(names):
    tsv = ("# id\tdescription\tREQUIRED\tSUPPORT\tKIND\n\nLem 2.2\tfourth power\tfoo', Wills.bar | foo'\t-\t-\n"
           "Thm 3.1\tcount\tbar\tfoo'\t-\nI1\tEhrhart\t-\t-\tFACT EhrhartThm\nC1b\tclasses\t-\t-\tCHECK Comp1,Comp1Count\n"
           "TW2\tfacets\t-\t-\tNOT-FORMALIZED faces\nW3v\tvolume\t-\tfoo'\tCHECK VolW\nPend\tlater\tPENDING\t-\t-\n")
    claims, uncovered = parse_claim_map(tsv, names)
    assert [c["required"] for c in claims] == [[["foo'", "bar"], ["foo'"]], [["bar"]], [], [], [], [], []]
    assert [c["support"] for c in claims] == [[], ["foo'"], [], [], [], ["foo'"], []] and uncovered == ["nodoc"]
    assert [c["pending"] for c in claims] == [False] * 6 + [True]
    assert claims[2]["kind_status"] == "NOT FORMALIZED (fact EhrhartThm: no Ehrhart theory in Lean's library)"
    assert claims[3]["kind_status"] == ("CHECKED BY COMPUTER (Comp1, Comp1Count), NOT proved in Lean: "
                                        "./reproduce.sh computation-1")
    assert kind_status(1, "CHECK VolW,Comp2") == ("CHECKED BY COMPUTER (VolW, Comp2), NOT proved in Lean: "
                                                  "./reproduce.sh theorem-1.3 computation-2")
    assert kind_status(1, "FACT BoundaryTriangulation") == ("NOT FORMALIZED (fact BoundaryTriangulation: no "
                                                            "triangulations of spheres, f-vectors and facets of polytopes in Lean's library)")
    assert claims[4]["kind_status"] == "NOT FORMALIZED (no faces of polytopes in Lean's library)"
    for bad in ["X\tdesc\tnot_a_row\t-\t-\n", "X\tdesc\tbar\t-\n", "X\tdesc\tbar\t-\t-\t-\n", "X\tdesc\tbar\t\n",
                "X\td\tbar\t-\t-\nX\td\tfoo'\t-\t-\n", "# only comments\n", "X\td\tbar |\t-\t-\n", "X\td\tbar\tghost\t-\n",
                "X\td\t-\t-\t-\n", "X\td\tbar\t-\tFACT EhrhartThm\n", "X\td\tPENDING\t-\tCHECK VolW\n",
                "X\td\t-\t-\tFACT Ehrhart\n", "X\td\t-\t-\tFACT\n", "X\td\t-\t-\tCHECK Comp6\n", "X\td\t-\t-\tCHECK Comp1,\n",
                "X\td\t-\t-\tCHECK\n", "X\td\t-\t-\tNOT-FORMALIZED edges\n", "X\td\t-\t-\tLEMMA x\n",
                "X\td\t-\tghost\tFACT EhrhartThm\n", "-\td\tbar\t-\t-\n"]:
        expect_fail(parse_claim_map, bad, names)
    return claims


def test_best_status():
    def row(name, status, hyps=()): return {"name": name, "status": status, "hypotheses": list(hyps)}
    def claim(required, support=(), kind=None): return {"required": required, "support": list(support), "kind_status": kind}
    rows = {r["name"]: r for r in [row("a", "PROVED GIVEN E1, E2", ["E1", "E2"]), row("b", "PROVED GIVEN Comp1", ["Comp1"]),
                                   row("e", "PROVED GIVEN E1", ["E1"]), row("c", "OPEN", ["E3"]), row("d", "PROVED"),
                                   row("v", "VIOLATION")]}
    assert claim_status(claim([["a"], ["b"], ["c"]]), rows) == ("PROVED GIVEN Comp1", ["b"])   # fewer hypotheses first
    assert claim_status(claim([["c"], ["a"], ["d"]]), rows) == ("PROVED", ["d"])
    assert claim_status(claim([["c"]]), rows) == ("OPEN", ["c"])
    assert claim_status(claim([["d", "c"]]), rows) == ("OPEN", ["d", "c"])                      # worst row of an alternative
    assert claim_status(claim([["b", "e"]]), rows) == ("PROVED GIVEN E1, Comp1", ["b", "e"])    # united, facts first
    assert claim_status(claim([["d", "b"], ["a"]]), rows) == ("PROVED GIVEN Comp1", ["d", "b"])
    assert claim_status(claim([["d"]], ["v"]), rows) == ("VIOLATION", [])                      # even in SUPPORT
    assert claim_status(claim([], ["v"], "CHECKED BY COMPUTER (VolW), x"), rows) == ("VIOLATION", [])
    assert claim_status(claim([], ["d"], "NOT FORMALIZED (x)"), rows) == ("NOT FORMALIZED (x)", [])
    assert [status_word(s) for s in ("PROVED", "PROVED GIVEN E1", "CHECKED BY COMPUTER (VolW), x", "NOT FORMALIZED (x)",
                                     "OPEN", "VIOLATION")] == ["PROVED", "PROVED GIVEN", "CHECKED BY COMPUTER",
                                                               "NOT FORMALIZED", "OPEN", "VIOLATION"]
    expect_fail(status_word, "PROVEDX")


def test_render_and_probe(items, axioms, binders, claims):
    rows = build_rows(items, axioms, binders)
    assert rows[0]["binders"][:2] == ["hC2 : Wills.Comp2", "n : Nat"]
    printed = build_printed(claims, rows)
    assert [c["status"] for c in printed] == [
        "PROVED GIVEN E1, Comp2", "OPEN", "NOT FORMALIZED (fact EhrhartThm: no Ehrhart theory in Lean's library)",
        "CHECKED BY COMPUTER (Comp1, Comp1Count), NOT proved in Lean: ./reproduce.sh computation-1",
        "NOT FORMALIZED (no faces of polytopes in Lean's library)",
        "CHECKED BY COMPUTER (VolW), NOT proved in Lean: ./reproduce.sh theorem-1.3", "OPEN"]
    report = render(rows, printed, ["nodoc"])
    assert "Lemma 2.2 \\| first line." in report and "(NO DOCSTRING)" in report and "`nodoc`" in report
    assert "foo', bar \\| foo'" in report
    assert "Rows: 3 — PROVED 1, PROVED GIVEN 1, OPEN 1, VIOLATION 0." in report
    assert ("Printed claims: 7 — PROVED 0, PROVED GIVEN 1, OPEN 2, VIOLATION 0, CHECKED BY COMPUTER 2, "
            "NOT FORMALIZED 2.") in report
    assert "NOT PRODUCED" in render(rows, build_printed(None, rows), None)
    # the public report: paths relative to the folder, no time stamp, the same bytes on every run
    assert str(PROJECT) not in report and not re.search(r"[0-9]{8}__|\b[0-2][0-9]:[0-5][0-9]\b", report)
    assert report == render(rows, printed, ["nodoc"])
    probe = probe_text([item["name"] for item in items])
    assert "gated" not in probe
    assert f"import {STATEMENTS_MODULE}" in probe and "#print axioms Wills.foo'" in probe
    assert 'run_cmd willsAuditBinders ``Wills.nodoc "nodoc"' in probe
    # check.sh scans every .lean file of the tree for these words; the probe must never trip it
    assert not re.search(r"\b(?:sorry|admit|sorryAx|axiom|native_decide|implemented_by|extern|unsafe|csimp)\b", probe)


def main_test():
    items = test_statements()
    names = [item["name"] for item in items]
    test_sources()
    axioms, binders = test_lean_output(names)
    claims = test_claim_map(names)
    test_best_status()
    test_render_and_probe(items, axioms, binders, claims)
    print("PASS: audit.py --test (statements, axiom scan, Lean output, binder guards, statuses, claim map and kinds, "
          "best status, Markdown, probe)")


def main():
    if sys.argv[1:] == ["--test"]: main_test()
    elif not sys.argv[1:]: main_audit()
    else: fail("usage: scripts/audit.py [--test]")


if __name__ == "__main__":
    main()
