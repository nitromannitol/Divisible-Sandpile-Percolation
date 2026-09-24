"""Check that every theorem-like statement in the paper has a manifest entry.

The manifest says which paper statement each Lean node transcribes.  This asks
the complementary question, which no other checker asks: is there a statement in
the paper that no node claims?  A formalization can be entirely axiom-clean and
still be silently incomplete, so the gap is worth a gate of its own.

Open problems (the `problem` environment of Section 9) are excluded: they are
questions, not claims.

    python3 tools/check_coverage.py
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_coverage.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"
def _paper_path() -> Path:
    """The paper: the copy pinned in this repository, or `$SANDPILE_PAPER`."""
    env = os.environ.get("SANDPILE_PAPER")
    return Path(env) if env else ROOT / "paper" / "sandpile.tex"


PAPER = _paper_path()

STATEMENT_ENVS = ("theorem", "lemma", "proposition", "corollary")
STATEMENT = re.compile(
    r"\\begin\{(" + "|".join(STATEMENT_ENVS) + r")\}(.*?)\\end\{\1\}", re.DOTALL)
LABEL = re.compile(r"\\label\{((?:thm|lem|prop|cor)[:-][A-Za-z0-9:_-]+)\}")
LABEL_TOKEN = re.compile(r"\b((?:thm|lem|prop|cor)[:-][A-Za-z0-9:_-]+)")


def canonical_label(label: str) -> str:
    """Manifest source anchors use a hyphen where the paper uses a colon."""
    return re.sub(r"^(thm|lem|prop|cor)-", r"\1:", label)


def main() -> int:
    if not PAPER.exists():
        print(f"check_coverage: paper not found at {PAPER}", file=sys.stderr)
        return 2
    # Preserve line numbers while ignoring commented-out statements and labels.
    text = re.sub(r"(?<!\\)%[^\n]*", "", PAPER.read_text(encoding="utf-8"))
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))

    claimed: set[str] = set()
    for node in manifest.get("nodes") or []:
        claimed.update(canonical_label(label) for label in LABEL_TOKEN.findall(node["source"]))

    statements = []
    seen = set()
    for m in STATEMENT.finditer(text):
        label = LABEL.search(m.group(2))
        line = text[:m.start()].count("\n") + 1
        if label is None:
            print(f"check_coverage: unlabeled {m.group(1)} at sandpile.tex:{line}",
                  file=sys.stderr)
            return 2
        lab = canonical_label(label.group(1))
        if lab not in seen:
            seen.add(lab)
            statements.append((m.group(1), lab, line))

    uncovered = [(k, lab, ln) for k, lab, ln in statements if lab not in claimed]

    print(f"check_coverage: {len(statements)} statements in the paper, "
          f"{len(statements) - len(uncovered)} represented in the manifest")
    if uncovered:
        print("\nNot claimed by any manifest node:")
        for kind, lab, ln in uncovered:
            print(f"  sandpile.tex:{ln}  {kind} {lab}")
        print("\ncheck_coverage: the formalization does not cover the whole paper",
              file=sys.stderr)
        return 1
    print("every theorem, lemma, proposition and corollary has a manifest entry")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
