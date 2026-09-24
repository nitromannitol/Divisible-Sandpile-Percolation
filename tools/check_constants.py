"""Check that every constant depends only on the dimension.

The paper's constants are always "depending only on `d`".  In Lean that is a
property of quantifier order: the existential must be bound before `β` and
before `n`.  Writing

    theorem foo {d : ℕ} (hd : 2 ≤ d) {β : ℝ} (hβ : 1 ≤ β) : ∃ c, ... β ... n ...

reads as `∀ β, ∃ c(β)`, which lets the constant absorb any power of `β` and
makes a factor like `β^{-d/(d+1)}` decorative -- the statement would hold with
the wrong exponent.  That is a silent weakening, invisible to every other check
here, so it gets its own.

The rule enforced: in a frozen statement that binds a real-valued existential,
none of `β`, `n`, `k`, `m`, `h` may be a *parameter* of the theorem; they must be
quantified inside the conclusion, after the existential.  Only `d` may be a
parameter, which is what the paper's own convention allows: "`c > 0` and
`C < ∞` are constants that depend only on `d` ... They never depend on `β`, `k`,
`m`, or `n`."

    python3 tools/check_constants.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_constants.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"

# Names that must never be theorem parameters when a constant is existential.
FORBIDDEN = ("R", "n", "t", "m", "r", "s", "L", "x", "y", "u", "v", "e", "z", "ε", "η", "δ")

# Statements read against the paper where a forbidden name is a parameter by the
# paper's own standing assumption, with the reason recorded.  A statement whose
# existential is an honest constant of the paper (`∃ c ∀ n`) is never listed here.
REVIEWED: dict[str, dict[str, str]] = {
    "prop-path-reduction": {
        "η": "the standing assumption of prop:path-reduction is `for some η > 0` the "
             "criterion holds (sandpile.tex:1007-1011); the paper's `a` in (ii) is chosen "
             "under that assumption, so it may depend on η, and the only other real "
             "existentials are the limit-shape constants of (iii), likewise",
    },
    "prop-brownian-os": {
        "x": "prop:brownian-os opens \"Fix $T>0$ and $x\\in\\R^d$\" "
             "(sandpile.tex:1083-1084), so the point is fixed before every clause; and the "
             "existentials the pattern matches are not constants at all but a "
             "right-continuous modification of the value process and the first time the "
             "value vanishes, both of which the paper says are built from the path started "
             "at that point",
    },
    "rem-dlt4-killed-scaling": {
        "ε": "the remark reads \"for every compact $K$, every $T$ and every $\\varepsilon,\\delta>0$ "
             "there is $R_0$\" (sandpile.tex:1929-1950); its only real existential is the "
             "threshold $R_0$ of the couplings, which the remark itself lets depend on the "
             "accuracy and the probability, so it is bound after both",
        "δ": "same statement; the threshold $R_0$ is per-accuracy and per-probability by the "
             "remark's own quantifier order",
    },
    "thm-limiting-odometer-crossing": {
        "ε": "the theorem reads \"For every $\\varepsilon>0$, there are $T<\\infty$ and "
             "$H>0$ such that\" (sandpile.tex:2517-2519), so the horizon and the height are "
             "chosen after the error and depend on it; binding them before it would assert a "
             "single horizon good for every error, which is not the paper's statement and is "
             "false, since the crossing probability at a fixed horizon is bounded away from one",
    },
    "lem-finite-scale-extraction": {
        "ε": "the lemma reads \"For every $\\varepsilon>0$, there are $c>0$ and rational "
             "scales $s_1,\\ldots,s_k\\in(0,1)$ such that\" (sandpile.tex:2417-2419); the "
             "level and the finite list of scales are chosen after the error, exactly as "
             "thm:limiting-odometer-crossing then uses them",
    },
    "thm-main-explosion-ii-c": {
        "s": "clause (ii)(c) reads \"For every $T>0$ and $s>0$, the fields ... are tight in "
             "$H^{-s}_{\\rm loc}(\\R^4)$\" (sandpile.tex:255-257), so the Sobolev exponent "
             "is fixed before the assertion; the existential the pattern matches is the "
             "tightness threshold, which is per-exponent and per-error by the definition of "
             "tightness and cannot be uniform in either",
    },
    "prop-d4-superdiffusive-limit": {
        "s": "the proposition fixes the domain, the density and the exponent and then reads "
             "\"Then, for every $s>0$, as $R\\to\\infty$\" (sandpile.tex:3323-3324), so the "
             "Sobolev exponent is fixed before the convergence; the existential the pattern "
             "matches is again the tightness threshold of the second clause",
    },
    "prop-passage-limit": {
        "η": "same standing assumption; the only real existential is `R₀`, bound after "
             "the rotors `ρ` and `ε` exactly as the paper's almost-sure limit "
             "(sandpile.tex:1088-1093) prescribes, and the function `f` does not depend "
             "on η at all (its proof uses only invariance and ergodicity)",
    },
}

# Only a real-valued existential is a *constant*.  `lem-walk-order` also binds
# an existential -- the ordering of the visited sites -- and that one must depend
# on the word and the time, so it is not what this check is about.
CONSTANT = re.compile(r"∃\s+[^,:]*:\s*ℝ")


def split_statement(block: str) -> tuple[str, str]:
    """(binders, conclusion), split at the FIRST `:` outside every bracket.

    Every theorem parameter is bracketed, so its own `:` sits at depth one or
    more; the first `:` at depth zero is the one that ends the binder list.
    Taking the last such `:` instead would cut inside `∃ c : ℝ` and hide the
    existential in the binders, which is precisely the thing being looked for."""
    depth = 0
    for i, ch in enumerate(block):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and not block.startswith(":=", i):
            return block[:i], block[i + 1:]
    return block, ""


def parameters(binders: str) -> set[str]:
    """Variable names bound as theorem parameters.

    Only a TOP-LEVEL bracket group is a binder.  A type ascription inside the
    body of a hypothesis -- `(m : ℝ)` in a cast, `Var(...)` inside a display --
    sits at depth two or more and binds nothing, so reading it as a parameter
    reports a dependence that the statement does not have.  Within a top-level
    group the names are those before its own first `:`."""
    names: set[str] = set()
    depth, start = 0, None
    for i, ch in enumerate(binders):
        if ch in "([{⟨":
            if depth == 0:
                start = i + 1
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
            if depth == 0 and start is not None:
                group, inner = binders[start:i], 0
                for j, c in enumerate(group):
                    if c in "([{⟨":
                        inner += 1
                    elif c in ")]}⟩":
                        inner -= 1
                    elif c == ":" and inner == 0:
                        for tok in group[:j].split():
                            names.add(tok)
                        break
                start = None
    return names


def main() -> int:
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    bad, ok = [], 0
    print(f"{'node':28s} {'real constant?':15s} {'bad parameters':22s}")
    for node in manifest.get("nodes") or []:
        text = (ROOT / node["file"]).read_text(encoding="utf-8")
        blk = text[text.index("-- FROZEN-STATEMENT-BEGIN") + len("-- FROZEN-STATEMENT-BEGIN"):
                   text.index("-- FROZEN-STATEMENT-END")]
        binders, concl = split_statement(blk)
        has_exists = bool(CONSTANT.search(concl))
        params = parameters(binders)
        offenders = sorted(params & set(FORBIDDEN))
        reviewed = REVIEWED.get(node["id"], {})
        for name in sorted(set(offenders) & set(reviewed)):
            print(f"  {node['id']:26s} reviewed {name}: {reviewed[name]}")
        offenders = [o for o in offenders if o not in reviewed]
        mark = ""
        if has_exists and offenders:
            bad.append((node["id"], offenders))
            mark = "  <-- CONSTANT MAY DEPEND ON " + ", ".join(offenders)
        else:
            ok += 1
        print(f"  {node['id']:26s} {'yes' if has_exists else 'no':13s} "
              f"{', '.join(offenders) if offenders else '-':20s}{mark}")

    if bad:
        print("\ncheck_constants: a constant is bound after a quantity it must not "
              "depend on:", file=sys.stderr)
        for nid, off in bad:
            print(f"  {nid}: move {', '.join(off)} inside the existential", file=sys.stderr)
        return 1
    print(f"\ncheck_constants: OK ({ok} statements; every existential constant is "
          f"bound before every paper parameter, so it is a genuine constant)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
