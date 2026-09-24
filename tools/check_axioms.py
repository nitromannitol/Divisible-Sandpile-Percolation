#!/usr/bin/env python3
"""Check every frozen export's elaborated axiom closure against the manifest.

Only DRAFT_SORRY and CONDITIONAL theorem nodes may depend on sorryAx. Every export must be
resolved, and all other axioms must belong to the standard logical foundation.
Use --strict to require that the whole manifest is free of sorryAx. This check
never changes node states; register a completed proof with freeze.py.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

import yaml


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"
FOUNDATION = {"propext", "Classical.choice", "Quot.sound"}
AXIOMS = re.compile(r"['`]([^'`]+)['`] depends on axioms:\s*\[([^\]]*)\]")


def audit_closures(nodes: list[dict], output: str, returncode: int,
                   strict: bool = False) -> tuple[list[str], list[str]]:
    """Validate actual elaborator output, including absent or duplicate exports."""
    closures: dict[str, list[set[str]]] = {}
    for name, axioms in AXIOMS.findall(output):
        closures.setdefault(name, []).append({a.strip() for a in axioms.split(",") if a.strip()})
    reports, errors = [], []
    if returncode:
        errors.append(f"elaboration failed with exit code {returncode}")
    clean = draft = 0
    for node in nodes:
        nid, export = node["id"], node["export"]
        matches = closures.get(export, [])
        if len(matches) != 1:
            errors.append(f"{nid}: expected one axiom report for {export}, found {len(matches)}")
            continue
        axioms = matches[0]
        extra = axioms - FOUNDATION - {"sorryAx"}
        if extra:
            errors.append(f"{nid}: unexpected axioms {', '.join(sorted(extra))}")
        authorized = node["state"] in ("DRAFT_SORRY", "CONDITIONAL") and node["kind"] == "theorem"
        if "sorryAx" in axioms:
            draft += 1
            reports.append(f"  sorryAx {nid} (registered draft)" if authorized
                           else f"  sorryAx {nid} (NOT authorized)")
            if not authorized or strict:
                errors.append(f"{nid}: sorryAx in the axiom closure")
        else:
            clean += 1
            reports.append(f"  clean   {nid}")
            if node["state"] in ("DRAFT_SORRY", "CONDITIONAL"):
                errors.append(f"{nid}: proof is clean but state is {node['state']}; register its seal")
    reports.append(f"\n{clean} clean, {draft} depend on sorryAx, "
                   f"{len(nodes) - clean - draft} unresolved")
    return reports, errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--strict", action="store_true", help="reject all remaining proof debt")
    args = parser.parse_args()
    nodes = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))["nodes"]
    modules = sorted({n["file"][:-5].replace("/", ".") for n in nodes})
    source = "".join(f"import {m}\n" for m in modules)
    source += "".join(f"#print axioms {n['export']}\n" for n in nodes)
    scratch = ROOT / "scratch"
    scratch.mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=scratch,
                                     encoding="utf-8", delete=False) as probe:
        probe.write(source)
        path = Path(probe.name)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True,
            text=True, encoding="utf-8", timeout=3600,
            env={**os.environ, "PATH": str(Path.home() / ".elan" / "bin")
                 + ":" + os.environ.get("PATH", "")})
    finally:
        path.unlink()
    reports, errors = audit_closures(nodes, result.stdout, result.returncode, args.strict)
    print("\n".join(reports))
    if errors:
        if result.returncode:
            print(result.stdout)
            print(result.stderr)
        print("check_axioms: FAIL")
        for error in errors:
            print(f"  {error}")
        return 1
    print("check_axioms: OK (all closures match their registered states)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
