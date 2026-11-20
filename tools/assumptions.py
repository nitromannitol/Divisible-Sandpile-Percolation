#!/usr/bin/env python3
"""Write ASSUMPTIONS.md: every result this development assumes, with its statement.

A reader who is told that something is assumed should be able to see exactly
what.  This lists each node whose state is `FROZEN`, with where the paper cites
it and the verbatim Lean proposition that is assumed.

    python3 tools/assumptions.py            # write ASSUMPTIONS.md
    python3 tools/assumptions.py --check    # fail if the file on disk is stale
"""
import pathlib, re, sys

try:
    import yaml
except ImportError:
    sys.exit("assumptions.py: PyYAML is required")

ROOT = pathlib.Path(__file__).resolve().parent.parent
BEGIN, END = "-- FROZEN-STATEMENT-BEGIN", "-- FROZEN-STATEMENT-END"
# An optional explicit universe instantiation, as in `ContinuumStoppingStability.{u}`.
UNIVERSES = r"(?:\.\{[^}]*\})?"


def frozen_block(path):
    t = (ROOT / path).read_text(encoding="utf-8")
    return t[t.index(BEGIN) + len(BEGIN):t.index(END)].strip("\n")


def companions(nodes):
    """Assumed propositions for which this repository also supplies a proof.

    The proof lives beside the proposition in a `*Proved.lean` companion; some
    prove it outright and some under hypotheses the paper's setting satisfies.
    """
    out = {}
    for n in nodes:
        if n.get("state") in ("SEALED", "PROVED") and n["file"].endswith("Proved.lean"):
            out[pathlib.Path(n["file"]).name[: -len("Proved.lean")]] = n
    return out


def bridge_proof(n):
    """Find an unconditional companion or bridge proving the exact proposition.

    A companion may be a nonfrozen theorem beside the proposition; other bridge theorems
    live outside `External/` and `Frozen/`.
    """
    export = n["export"]
    namespace, short = export.rsplit(".", 1)
    source = pathlib.Path(n["file"])
    companion = source.with_name(source.stem + "Proved.lean")
    if not (ROOT / companion).is_file():
        companion = source.with_name(short + "Proved.lean")
    if (ROOT / companion).is_file():
        text = (ROOT / companion).read_text(encoding="utf-8")
        top_level = re.search(r"^theorem\s+(" + re.escape(namespace) + r"\.\w+)\s*:\s*"
                              + re.escape(export) + UNIVERSES + r"\s*:=", text, re.M)
        if top_level and not re.search(r"^\s*(?:variable|variables|section|namespace)\b",
                                       text[:top_level.start()], re.M):
            return {"id": top_level.group(1), "file": str(companion),
                    "unconditional_bridge": True}
        opening = re.search(r"^namespace\s+" + re.escape(namespace) + r"\s*$", text, re.M)
        if opening:
            block = text[opening.end():].split("\nend " + namespace, 1)[0]
            target = r"(?:" + re.escape(export) + "|" + re.escape(short) + r")"
            match = re.search(r"^theorem\s+(\w+)\s*:\s*" + target + UNIVERSES + r"\s*:=",
                              block, re.M)
            prefix = text[:opening.end()] + block[:match.start()] if match else ""
            if (match and len(re.findall(r"^\s*namespace\b", prefix, re.M)) == 1
                    and not re.search(r"^\s*(?:variable|variables|section)\b", prefix, re.M)):
                return {"id": namespace + "." + match.group(1), "file": str(companion),
                        "unconditional_bridge": True}
    names = {re.escape(export), r"External\." + re.escape(short)}
    pat = re.compile(r"^theorem\s+(\S+)\s*:\s*(?:" + "|".join(names) + r")" + UNIVERSES
                     + r"\s*:=", re.M)
    pkg = pathlib.Path(n["file"]).parts[0]
    for f in sorted((ROOT / pkg).rglob("*.lean")):
        rel = f.relative_to(ROOT)
        if "External" in rel.parts or "Frozen" in rel.parts:
            continue
        m = pat.search(f.read_text(encoding="utf-8"))
        if m:
            return {"id": m.group(1), "file": str(rel)}
    return None


def conditional(c):
    """The frozen statement of a companion node, when it carries hypotheses; else None.

    A companion `theorem NAME : PROP` proves the assumed proposition outright.  One with
    binders proves it only under them (for example only on transient graphs), and the reader
    must see which, so its statement is shown beside the assumed one.
    """
    if c.get("unconditional_bridge") or "file" not in c or not c["file"].endswith("Proved.lean"):
        return None
    block = frozen_block(c["file"])
    body = re.sub(r"(?s)^\s*/--.*?-/\s*", "", block)
    if re.fullmatch(r"(?s)theorem\s+\S+\s*:\s*\S+\s*", body):
        return None
    return block


def render():
    man = yaml.safe_load((ROOT / "ledger" / "manifest.yaml").read_text(encoding="utf-8"))
    assumed = [n for n in man["nodes"] if n.get("state") == "FROZEN"]
    comp = companions(man["nodes"])
    out = ["# What this development assumes", ""]
    if not assumed:
        out += ["Nothing.  Every registered statement in this repository is proved here,",
                "from Mathlib and the libraries named in the README; no result is carried",
                "as an assumed hypothesis.", ""]
        return "\n".join(out)
    out += [
        "The results below are quoted by the paper from the literature and recorded as",
        "frozen propositions.  Some are carried as explicit hypotheses; others have",
        "proofs in this repository, as noted with their statements.",
        "",
        f"There are {len(assumed)} of them.  Each entry gives the node id, where the paper",
        "cites the result, and the verbatim Lean proposition.",
        "",
        "This file is generated by `python3 tools/assumptions.py` from",
        "`ledger/manifest.yaml` and the Lean sources; do not edit it by hand.",
        "",
    ]
    for n in assumed:
        stem = pathlib.Path(n["file"]).stem
        if stem not in comp:
            b = bridge_proof(n)
            if b:
                comp[stem] = b
    withproof = [n for n in assumed if pathlib.Path(n["file"]).stem in comp]
    if withproof:
        out += [(f"Of these, **{len(withproof)} are also proved in this repository** and so need not "
                 "be taken on trust; each is marked below with the theorem that proves it. "
                 if len(withproof) > 1 else
                 "Of these, **one is also proved in this repository** and so need not "
                 "be taken on trust; it is marked below with the theorem that proves it. ") +
                (f"The remaining **{len(assumed) - len(withproof)}** are assumed outright."
                 if len(assumed) - len(withproof) != 1 else
                 "The remaining **one** is assumed outright."), ""]
        ncond = sum(1 for n in withproof if conditional(comp[pathlib.Path(n["file"]).stem]))
        if ncond:
            out[-2] += (f" Of the {len(withproof)} proofs, **{ncond}** hold only under hypotheses "
                        "of their own, shown with them; where those fail, the result is still assumed.")
    for n in sorted(assumed, key=lambda x: x["id"]):
        c = comp.get(pathlib.Path(n["file"]).stem)
        cond = conditional(c) if c else None
        name = (c.get("export") or c["id"]) if c else None
        if cond:
            line = (f"* **Also proved here, under hypotheses**, by `{name}` in `{c['file']}`, "
                    "whose statement is shown after the assumed one; where those hypotheses "
                    "hold, this hypothesis can be discharged, and elsewhere it is assumed")
        elif c:
            line = (f"* **Also proved here** by `{name}` in `{c['file']}`, so this hypothesis "
                    "can be discharged rather than assumed")
        else:
            line = "* **Not proved here**: this one is assumed outright"
        out += [f"## `{n['id']}`", "",
                f"* **Lean name** `{n['export']}`",
                f"* **File** `{n['file']}`",
                f"* **Cited at** {n['source']}",
                line,
                ""]
        if n["id"] == "ext-continuum-optimal-stopping":
            out += ["**Defect and deviation.** The frozen proposition permits exceptional paths of",
                    "Brownian motion while requiring a pointwise least contact for a right-continuous",
                    "modification and a raw natural-filtration stopping time. A pathological null",
                    "path can force that stop to be zero almost surely even when stopping at the",
                    "horizon has strictly greater reward. An earlier continuous-path replacement",
                    "also omitted ambient measurability of Brownian time slices; a null copy of",
                    "Wiener space with the trivial sigma algebra gives a contradiction. The amended",
                    "`Sandpile.External.ContinuumOptimalStoppingOfContinuous` assumes continuous",
                    "paths and strongly measurable time slices and is proved by",
                    "`Sandpile.External.continuumOptimalStoppingOfContinuous_holds`. The Brownian",
                    "representation `Sandpile.Support.brownian_optimal_stopping_of_continuous`",
                    "uses this proved result. See `CORRESPONDENCE.md` for details.", ""]
        out += ["```lean", frozen_block(n["file"]), "```", ""]
        if cond:
            out += [f"The proof `{name}`:", "", "```lean", cond, "```", ""]
    return "\n".join(out)


text = render()
target = ROOT / "ASSUMPTIONS.md"
if "--check" in sys.argv[1:]:
    cur = target.read_text(encoding="utf-8") if target.exists() else ""
    if cur != text:
        sys.exit("assumptions: ASSUMPTIONS.md is stale; rerun tools/assumptions.py")
    print("assumptions: OK (ASSUMPTIONS.md is current)")
else:
    target.write_text(text, encoding="utf-8")
    n = text.count("\n## `")
    print(f"assumptions: wrote ASSUMPTIONS.md ({n} frozen result(s))")
