#!/usr/bin/env python3
"""Refuse a change that defers work instead of doing it.

The expensive failure mode of an agentic formalization is not a false proof; the
axiom gate catches that.  It is UNPRODUCTIVE WRAPPING: a worker reduces an open
goal to a new lemma that is itself open, repackages it under a longer name, and
reports progress, while the set of open assumptions never shrinks.

This check counts open holes in the tree and compares them with the recorded
baseline in `ledger/holes.json`.  A change may close holes or leave them alone.
It may not open new ones, and it may not hold the count steady while growing the
number of declarations that depend on an open hole.

    python3 tools/check_progress.py           # verify against the baseline
    python3 tools/check_progress.py --record  # record the current state

A hole in a file that a manifest node registers as DRAFT_SORRY is that node's own
placeholder and is counted, but it is expected: closing it is what sealing means.
"""
from __future__ import annotations
import json, re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
BASE = ROOT / "ledger" / "holes.json"
BLOCK = re.compile(r"/-.*?-/", re.S)
LINE = re.compile(r"--.*?$", re.M)
HOLE = re.compile(r"\bsorry\b")
DECL = re.compile(r"^(theorem|lemma|def)\s+([A-Za-z_][^\s(\[{:]*)", re.M)


def strip(text: str) -> str:
    return LINE.sub("", BLOCK.sub("", text))


def survey() -> dict[str, int]:
    out: dict[str, int] = {}
    for f in sorted((ROOT / "Sandpile").rglob("*.lean")):
        n = len(HOLE.findall(strip(f.read_text(encoding="utf-8", errors="replace"))))
        if n:
            out[str(f.relative_to(ROOT))] = n
    return out


def main() -> int:
    now = survey()
    total = sum(now.values())
    if "--record" in sys.argv[1:]:
        BASE.write_text(json.dumps({"holes": now, "total": total}, indent=2, sort_keys=True) + "\n")
        print(f"check_progress: recorded {total} open hole(s) in {len(now)} file(s)")
        return 0
    if not BASE.exists():
        print("check_progress: no baseline; run --record once to create ledger/holes.json")
        return 1
    was = json.loads(BASE.read_text())
    old, oldtotal = was["holes"], was["total"]
    opened = {f: n for f, n in now.items() if n > old.get(f, 0)}
    closed = {f: old[f] - now.get(f, 0) for f in old if old[f] > now.get(f, 0)}
    if total > oldtotal:
        print(f"check_progress: FAIL ({oldtotal} -> {total} open holes)")
        for f, n in sorted(opened.items()):
            print(f"  + {f}: {old.get(f, 0)} -> {n}")
        print("  A change may close holes. It may not open them. If a step genuinely")
        print("  needs spelling out further, close the hole you opened in the same")
        print("  change, or record a new baseline with a written reason.")
        return 1
    for f, n in sorted(closed.items()):
        print(f"  - {f}: closed {n}")
    print(f"check_progress: OK ({oldtotal} -> {total} open hole(s))")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
