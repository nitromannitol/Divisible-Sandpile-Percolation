"""Compare every exponent in a paper statement with those in its Lean statement.

The exponents `2/3`, `1/3`, `-2/3`, `-1/3` and the `e^{-cR}` tails carry the
content of this paper, and `2/3` versus `1/3` is a transposition that no type
error would catch.  So they are compared directly:
every exponent is extracted from the paper's statement and from the frozen Lean
statement and the two multisets are matched.

Three kinds of difference are expected and are recorded per node rather than
silently ignored:

  notation   the paper writes `\\gamma`, Lean writes `γ`
  general    the paper writes the `d = 2` case as `2/3` and `1/3`; Lean carries
             the general `d/(d+1)` and `1/(d+1)`, which agree at `d = 2`
  split      `thm:return` is one theorem in the paper and three nodes here, so
             each node sees the whole theorem's line range but carries only its
             own display

    python3 tools/check_exponents.py
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_exponents.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"


def paper_path() -> Path:
    env = os.environ.get("SANDPILE_PAPER")
    return Path(env) if env else ROOT / "paper" / "sandpile.tex"


# Superscripts that are not exponents of a quantity: set names like `ℤ^d`, the
# inverse in `Δ^{-1}`, the summation limits, and the `θ`-expressions of lem:exp,
# which Lean writes with `Real.exp` rather than with `^`.
NOISE = {"2", "+", "-1", "\Z", "\R", "\infty", "\ast", "\star", "j", "n", "m", "k", "i"}

# A superscript that decorates a symbol instead of raising it to a power: the
# paper's rescaling label `f^{(R)}`, the density label `\sigma^{(\rho)}`, the
# roman decorations `g^{\rm BM}` and `\P^{\rm tr}`, and the transpose star.
DECORATION = re.compile(
    r"^(\\(rm|mathrm|mathbf|mathcal|text|operatorname).*"
    r"|\((\\rho|\\rho\'|R|T|\\varepsilon)\)"
    r"|\*|\\ast|\\star|\\top|\\dagger|\\prime|\'|\\|)$")

# Bases whose superscript is a dimension or a set name, never a power of a
# quantity: `\Z^d`, `\R^d`, `\N^d`, `\T^d`.
SET_BASE = re.compile(r"(\\(Z|R|N|T|mathbb\{[A-Za-z]\})|\bC_{\\rm loc}|\bH)\s*$")

# Per node: exponents present in the paper's line range but legitimately absent
# from this node's Lean statement, with the reason.
EXPECTED_ABSENT: dict[str, dict[str, str]] = {
    "ext-gaussian-lipschitz-concentration": {
        "-(d-4)/2": "context: the concentration proxy bound C k_n^{-(d-4)/2} is the paper's application of the inequality to Theta_n, not part of the abstract Borell/TIS statement this node asserts",
        "k_n+1": "context: the iterate P^{k_n+1} defining Theta_n belongs to the paper's argument, not to the abstract concentration inequality",
    },
    "cor-mean-localization": {
        "-cA^2/T": "notation: the paper's e^{-cA^2/T} is Lean's Real.exp (-(c * A ^ 2 / T)) in the second conjunct.",
        "Q(x,AR)": "definition: the superscript Q(x,AR) of u_t^{Q(x,AR)} is the first argument of Sandpile.localizedOdometer, instantiated as Sandpile.supBox x (A * R); I read supBox (defined in Sandpile/Frozen/MeanLocalization.lean above the statement, {y | for all i, |y i - x i| <= floor L}, the floor being harmless for integer coordinates) and localizedOdometer (Sandpile/Walk.lean), and they match Q(x,L) of tex 680 and eq:localized-odometer.",
    },
    "ext-continuum-besov-tightness": {
        "-s,{\\rmloc}": "definition: the superscript of the Besov space B^{-s,loc}_{2,2} is not written in Lean; the conclusion names Sandpile.Continuum.TightInNegSobolev d s (Continuum/Membrane.lean:69), which I read together with negSobolevNorm and sobolevNormSq (Continuum/Sobolev.lean): for every bounded open nonempty D and eps>0 there is a finite M with P{M < negSobolevNorm d s D (F R omega)} <= eps for all R>=1, and negSobolevNorm d s D is the sup of |F(phi)| over phi in C_c^infty(D) with Fourier H^s norm <= 1, so the -s is the s of negSobolevNorm and the 'loc' is the for-every-D quantification, matching the paper's own definition of tightness in H^{-s}_loc at sandpile.tex:721-722; the identification B^{-s,loc}_{2,2} = H^{-s}_loc that the paper asserts in the same sentence is built into the assumed conclusion rather than stated as a separate clause",
    },
    "ext-paired-local-clt-four": {
        "-d": "split: R^{-d} occurs only in the display eq:lclt-parity (2R^{-d} p^BM, sandpile.tex:1145-1161) which is formalized by the separate node Sandpile.External.LocalCLT (read, External/LocalCLT.lean), not by this node",
        "d": "split: R^d occurs only in the display eq:lclt-parity (lim R^d sup ..., sandpile.tex:1145-1161) which is formalized by the separate node Sandpile.External.LocalCLT (read, External/LocalCLT.lean), not by this node",
        "t-1": "split: the superscript t-1 is the upper limit of sum_{a,b=0}^{t-1} in the statement of lem:d4-double-heat-kernel (1163-1168), formalized by the separate node lem-d4-double-heat-kernel (Finset.range t twice)",
    },
    "ext-rellich-kondrachov-negsobolev": {
        "(d-4)/2": "split: the line range 5610-5655 is Lemma lem:dgt4-linearization-from-survival, formalized as the node lem-dgt4-linearization-from-survival, where R^{(d-4)/2} and the threshold s > (d-4)/2 appear (as R ^ (((d:R) - 4)/2) and ((d:R) - 4)/2 < s); the Rellich-Kondrachov Prop has only the abstract orders s0 < s and no such exponent.",
        "-2": "split: R^{-2} is the prefactor of the survival hypothesis in Lemma lem:dgt4-linearization-from-survival, spelled (R ^ 2)^{-1} in hsurvival of the sibling node lem-dgt4-linearization-from-survival; it is not part of the Rellich-Kondrachov external.",
        "n_R-1": "split: the upper limit n_R - 1 of sum_{j=0}^{n_R-1} belongs to the survival hypothesis and the linear field of Lemma lem:dgt4-linearization-from-survival, formalized in the sibling node lem-dgt4-linearization-from-survival as Finset.range floor(R^2*T)_+; the Rellich-Kondrachov external has no sum.",
    },
    "lem-brownian-ball-localization": {
        "-cA^2/T": "notation: the paper's e^{-c A^2/T} is Real.exp (-(c * A ^ 2 / T)) in the Lean inequality, with the same c, A and T (c bound by exists C c, A by forall A >= 1, T by forall T > 0).",
    },
    "lem-convex-linear-bound": {
        "N": "notation: N is only the upper limit of the sums sum_{i=1}^N and of the index range 1 <= i <= N, not an exponent; Lean writes the same range as the type Fin N of coordinates (N : Nat is the theorem's natural-number argument, coordinates Fin N -> Real, sums over the whole type, 0-indexed).",
    },
    "lem-d4-difference-tail": {
        "-2": "notation: the paper's C (t+2)^{-2} is Lean's ENNReal.ofReal (C / ((t : R) + 2) ^ 2) with R the reals, a negative power written as division by the square with the same constant C and base t+2",
    },
    "lem-d4-double-heat-kernel": {
        "t-1": "notation: the upper limit t-1 of sum_{a,b=0}^{t-1} is Lean's Finset.range t in both nested sums, so a and b run over 0..t-1",
    },
    "lem-dgt4-blocking-to-crossing": {
        "c": "notation: the c is the superscript of the complement O^c in 'O^c cap Q(x, 2*64^n)', not an exponent; Lean writes the complement as `O\u1d9c` in `T subset O\u1d9c inter boxAt x (2 * 64^n)`, same content spelled differently",
    },
    "lem-dgt4-linearization-from-survival": {
        "-2": "notation: the paper's R^{-2} in R^{-2} sum_{j} E_0 |P(S=1|X) - q_{R,j}| is the inverse of (R ^ 2), written with Lean's postfix inverse, multiplying (sum ...) in the hypothesis hsurvival of the Lean statement.",
        "n_R-1": "notation: the upper index n_R - 1 of sum_{j=0}^{n_R-1} (in the survival hypothesis and in the linear field sum q_{R,j} P^j zeta) is Finset.range floor(R ^ 2 * T)_+ with n_R = floor(R^2 T), i.e. j = 0, ..., n_R - 1, in hsurvival and in both conclusions; the same range is the constraint j < floor(R ^ 2 * T)_+ in hq.",
    },
    "lem-dgt4-path-survival": {
        "-2": "notation: the superscript in R^{-2} of eq:dgt4-averaged-positive-path-limit is written in the Lean conclusion as the inverse of R ^ 2 (Lean's postfix inverse applied to R ^ 2, multiplying the sum), same content spelled as a reciprocal.",
        "n_R-1": "notation: n_R-1 is the upper limit of sum_{j=0}^{n_R-1} in eq:dgt4-averaged-positive-path-limit, not an exponent; Lean writes the same index set as Finset.range (Nat.floor (R ^ 2 * T)) = {0,...,n_R-1}.",
    },
    "lem-dgt4-stretched-green-scenery-tail": {
        "\\min\\{\u03b3,d/2\\}": "notation: the exponent min{gamma, d/2} of s in the conclusion is Lean's `s ^ min \u03b3 ((d : Real) / 2)` inside Real.exp (-(c * ...)), a real power with min taken on reals with d cast to Real.",
    },
    "lem-finite-scale-extraction": {
        "N": "notation: the upper index of the intersection over j = 1..N of H_{R_j}(4c; max X_{s_i}) is Lean's N : N with hN : 1 <= N, the family indexed by Fin N, and the intersection is the universally quantified conjunction forall j : Fin N inside the event {omega | forall j : Fin N, Crosses (a j) (b j) (dir j) ...}.",
    },
    "lem-localization-killing": {
        "D": "definition: the superscript D of u_t^D is the argument D of Sandpile.localizedOdometer D zeta t (Sandpile/Walk.lean); I read the definition and it is eq:localized-odometer, sup over walk stopping times <= t of E_x sum_{k < tau ^ tau_D} zeta(X_k) via the indicator of {j | for all i <= j, X i in D}, and 0 off D; the paper's tau_D is Sandpile.exitTime D, which the statement also names.",
    },
    "lem-odometer-derivative": {
        "n-1": "notation: the upper limit n-1 of sum_{j=0}^{n-1} is Lean's Finset.range n, so j runs over 0..n-1",
    },
    "lem-weighted-exp-conc": {
        "N": "notation: N is the number of coordinates and the upper limit of the paper's sums and max over 1 <= i <= N; in Lean N : N is bound in each of the four parts and the coordinates are indexed by Fin N (0-based), with sums written as sum over i of Finset.univ and the norms Sandpile.lTwoNorm and Sandpile.lInfNorm (read in Sandpile/Support/Norms.lean) taken over Fin N, so the content is the same and only the indexing is spelled differently.",
    },
    "prop-dgt4-height-lower-stretched": {
        "-As^\u03b3": "notation: the exponent -A s^gamma of e^{-A s^gamma} in the lower-tail hypothesis is Lean's `-(A * s ^ \u03b3)` inside Real.exp in `ENNReal.ofReal (a * Real.exp (-(A * s ^ \u03b3))) <= \u03bd (Set.Iic (-s))`, with s ^ \u03b3 a real power.",
        "1/\\min\\{\u03b3,d/2\\}": "notation: the exponent 1/min{gamma, d/2} of log t in the conclusion is Lean's `(Real.log t) ^ (1 / min \u03b3 ((d : Real) / 2))`, a real power with d cast to Real.",
    },
    "prop-dgt4-linearization": {
        "n_R-1": "notation: n_R-1 is the upper summation limit of sum_{j=0}^{n_R-1} P^j zeta, not an exponent; Lean writes the same index set {0,...,n_R-1} as Finset.range (Nat.floor (R^2 * T)) with n_R = floor(R^2 T) inlined, and I read the sum over avg^[j] (scenery d sigma) in the statement.",
    },
    "prop-finite-time-concentration-scale": {
        "1/2": "notation: the power 1/2 in (sum_z g_t(x,z)^2)^{1/2} is Lean's Real.sqrt (tsum z, Sandpile.greenTime d t x z ^ 2), and the ||zeta - eta||_{l2} it multiplies is Real.sqrt (tsum z, (\u03b6 z - \u03b7 z) ^ 2), so the right side of the Lipschitz bound is a product of two Real.sqrt.",
    },
    "prop-weighted-membrane-limit": {
        "T": "definition: T is the upper limit of the time integral in the limit field integral_0^T q(r) e^{r Delta/(2d)} W dr; the Lean statement names Sandpile.Frozen.WeightedMembraneLimit.generalWeightedMembraneCov d (variance id nu) T q, whose body has integral r in (0:R)..T and integral r' in (0:R)..T; I read the definition (WeightedMembraneLimit.lean) and it matches the covariance of the paper's limit field with q(r)q(r') in place of the weights; T also occurs literally in the statement through floor(R^2*T)_+ and ContinuousOn q (Icc 0 T)",
        "\\lfloorR^2T\\rfloor-1": "notation: the paper's upper summation limit floor(R^2T)-1 in sum_{j=0}^{floor(R^2T)-1} is Lean's Finset.range floor(R^2*T)_+, which enumerates j = 0,...,floor(R^2*T)_+ - 1",
    },
    "rem-dlt4-killed-scaling": {
        "Q(\\lfloorRu\\rfloor,R)": "notation: the paper's superscript on u (the lattice box Q(floor(Ru),R) in u^{Q(floor(Ru),R)}) is the first (domain) argument of Sandpile.localizedOdometer, supplied in the Lean statement as Sandpile.supBox (fun i => floor(R * u i)) R; I read Sandpile.supBox (Sandpile/Frozen/MeanLocalization.lean:41, {y | forall i, |y i - x i| <= floor(L)}, the paper's Q(x,L) of sandpile.tex:680 with integer coordinates, so radius R real is equivalent to floor(R)) and Sandpile.localizedOdometer (Sandpile/Walk.lean:109, the paper's u_t^D(x) of eq:localized-odometer with tau_D as the first exit, zero off D); both match.",
    },
    "thm-dgt4-height-upper-tail": {
        "1/\\min\\{\u03b3,d/2\\}": "notation: the paper's (log t)^{1/min{gamma,d/2}} is Lean's (Real.log t) ^ (1 / min gamma ((d : R) / 2)), where gamma is the Lean variable and R the reals; the exponent is the same, with min{gamma,d/2} spelled `min gamma ((d:R)/2)` (d cast to the reals) and 1/(.) as `1 / (.)`, in the frozen conclusion `Sandpile.meanOdometer ... t <= C * (Real.log t) ^ (...)`",
    },
    "thm-dgt4-many-limits": {
        "R_{k_\\ell}": "definition: the superscript ^{(R_{k_ell})} is the paper's piecewise-constant rescaling f^{(R)}(z) = f(floor(Rz)); in Lean it is the argument R = Rseq (kl (floor L)) of `Sandpile.Continuum.latticePairing` (Sandpile/Continuum/Sobolev.lean), which I read: latticePairing R f phi = integral of `embed R f z * phi z`, with `embed R f z = f (fun i => floor (R * z i))`, i.e. the pairing of f^{(R)} with phi, matching the paper; the companion occurrences R_{k_ell}^{(d-4)/2} and floor(T R_{k_ell}^2) appear literally in the statement as `Rseq (kl (floor L)) ^ (((d:R) - 4)/2)` and `Rseq (kl (floor L)) ^ 2`.",
    },
    "thm-dgt4-nontriviality": {
        "-b\\Eu_t(0)": "notation: the exponent -b E u_t(0) in the bound 1 - C e^{-b E u_t(0)} is Lean's `Real.exp (-(b * Sandpile.Frozen.DGT4Nontriviality.meanOdometerOf d nu t))` in the second conjunct; I read meanOdometerOf, which is the integral of `Sandpile.odometerOf zeta t 0` under `LatticeProb.iidLaw d nu`, i.e. E u_t(0), so the factor is the same and only spelled through a named definition",
    },
    "thm-main-explosion-ii-a": {
        "-(2-d/2)": "split: the exponent R^{-(2-d/2)} is in the display of part (i)(b) of thm:main-explosion (sandpile.tex:230 and 236, dimensions one to three), formalized as the separate node thm-main-explosion-i-b; the Lean statement of this node is part (ii)(a), dimension four, whose conclusion has only log t.",
        "-(4-d)/4": "split: the exponent t^{-(4-d)/4} is in part (i)(a) of thm:main-explosion (sandpile.tex:214, dimensions one to three), formalized as the separate node thm-main-explosion-i-a; the Lean statement of this node is part (ii)(a), dimension four, whose conclusion has only log t.",
    },
    "thm-main-explosion-iii-b": {
        "1/\\min\\{\u03b3,d/2\\}": "notation: the paper's (log t)^{1/min{gamma,d/2}} is Lean's (Real.log t) ^ (1 / min gamma ((d : R) / 2)), where gamma is the Lean variable and R the reals, written in both the lower and the upper bound of the conclusion; the exponent is identical, with min{gamma,d/2} spelled `min gamma ((d:R)/2)`",
    },
    "thm-main-explosion-iii-d": {
        "(d-4)/2": "definition: the normalisation R^{(d-4)/2} is inside `Sandpile.Continuum.diffusiveFluctuation` (Sandpile/Support/ExplFluctuation.lean, lines 18-22), which I read: it is `R ^ (((d:R) - 4)/2) * latticePairing R (fun x => odometer sigma floor(T*R^2) x - meanOdometer P floor(T*R^2)) phi`, matching the paper's R^{(d-4)/2}(u_{floor(TR^2)} - E u_{floor(TR^2)}(0))^{(R)}; the other occurrence, the threshold s>(d-4)/2, appears in the Lean statement literally as `((d:R) - 4)/2 < s` (not written with a caret, so the gate does not see it as an exponent).",
    },
}


GREEK = {"\\alpha": "α", "\\beta": "β", "\\gamma": "γ", "\\delta": "δ",
         "\\theta": "θ", "\\kappa": "κ", "\\lambda": "λ", "\\rho": "ρ",
         "\\sigma": "σ", "\\tau": "τ", "\\varepsilon": "ε", "\\eta": "η"}


def top_level_sum(e: str) -> bool:
    """True when `e` has a `+` or `-` outside every bracket, so that dropping a
    wrapping parenthesis after a minus sign would change what it means."""
    depth = 0
    for j, ch in enumerate(e):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch in "+-" and depth == 0 and j > 0:
            return True
    return False


def canon(e: str) -> str:
    """One spelling for an exponent, applied to the paper and to Lean alike.

    `-(2 - d/2)` and `-2 - d/2` are different numbers, so the parenthesis after
    a minus sign is kept whenever the operand is itself a sum; it is dropped
    only when it is redundant, which is what makes the two sides comparable.
    """
    for k, v in GREEK.items():
        e = e.replace(k, v)
    e = re.sub(r"\\(cdot|times|,|!|;|\s)", "", e)
    e = re.sub(r"[\s*]", "", e)
    for _ in range(3):
        e = re.sub(r":ℝ$", "", e)
        m = re.fullmatch(r"\((.*)\)", e)
        if m and not top_level_sum(m.group(1)):
            e = m.group(1)
        if e.startswith("-(") and e.endswith(")") and not top_level_sum(e[2:-1]):
            e = "-" + e[2:-1]
        e = re.sub(r":ℝ$", "", e)
    return e


def balanced(s: str, i: int, op: str, cl: str) -> str | None:
    depth = 0
    for j in range(i, len(s)):
        if s[j] == op:
            depth += 1
        elif s[j] == cl:
            depth -= 1
            if depth == 0:
                return s[i + 1:j]
    return None


DECL_START = re.compile(
    r"^(noncomputable\s+)?(private\s+|protected\s+)?"
    r"(def|abbrev|theorem|lemma|instance|structure|inductive|class|namespace|end|open|variable|@\[|/-)")


def definition_bodies() -> dict[str, str]:
    """Every `def` in `Sandpile/`, by fully qualified name, with its body.

    An exponent of a paper statement often sits in a definition the statement
    names -- `h(t)` of Theorem 1.2 is `Sandpile.criticalScale` -- so the text a
    statement is compared against is the frozen block together with the bodies
    of the definitions it mentions.
    """
    bodies: dict[str, str] = {}
    for path in sorted((ROOT / "Sandpile").rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        i = 0
        while i < len(lines):
            m = re.match(r"^(noncomputable\s+)?def\s+([A-Za-z_][A-Za-z0-9_.']*)", lines[i])
            if not m:
                i += 1
                continue
            name = m.group(2)
            j = i + 1
            while j < len(lines) and not DECL_START.match(lines[j]):
                j += 1
            bodies[name] = "\n".join(lines[i:j])
            bodies[name.split(".")[-1]] = bodies[name]
            i = j
    return bodies


def with_definitions(blk: str, bodies: dict[str, str]) -> str:
    """The frozen block plus the body of each definition it names."""
    out = [blk]
    for name in sorted(set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", blk))):
        # a statement writes the qualified `Parking.nearRate`; the declaration
        # inside `namespace Parking` writes the short name
        body = bodies.get(name) or bodies.get(name.split(".")[-1])
        if body is not None and body not in out:
            out.append(body)
    return "\n".join(out)


def paper_exponents(seg: str) -> tuple[set[str], bool]:
    """The exponents of the segment, and whether it contains an exponential.

    A superscript is not an exponent when its base is a set name (`\\Z^d` is a
    lattice, not a power) and when it decorates rather than raises (`f^{(R)}`).
    A superscript on `e` is an exponential: Lean writes it `Real.exp`, not `^`,
    so it is reported separately and checked by name instead of by text.
    """
    out, exponential = [], False
    for m in re.finditer(r"\^", seg):
        i = m.end()
        if i >= len(seg):
            continue
        if seg[i] == "{":
            g = balanced(seg, i, "{", "}")
            if g is None:
                continue
        else:
            g = seg[i]
        base = seg[:m.start()]
        if SET_BASE.search(base):
            continue
        if re.search(r"(^|[^A-Za-z\\])e\s*$", base):
            exponential = True
            continue
        out.append(g)
    cleaned = set()
    for e in out:
        e = re.sub(r"\s|\\,|\\!|\\bigl|\\bigr", "", e)
        # `^{}_{\rm loc}` and friends leave a brace-wrapped decoration behind
        while e.startswith("{") and e.endswith("}"):
            e = e[1:-1]
        if e and not DECORATION.match(e):
            cleaned.add(canon(e))
    return cleaned - NOISE, exponential


def lean_exponents(blk: str) -> set[str]:
    out = []
    for m in re.finditer(r"\^\s*", blk):
        i = m.end()
        if i >= len(blk):
            continue
        if blk[i] == "(":
            g = balanced(blk, i, "(", ")")
            if g is not None:
                out.append(g)
        else:
            g = re.match(r"[A-Za-zγβ0-9]+", blk[i:])
            if g:
                out.append(g.group(0))
    cleaned = set()
    for e in out:
        e = re.sub(r"\(\s*([a-zA-Zβγ])\s*:\s*ℝ\s*\)", r"\1", e)
        e = re.sub(r"\(\s*(\d+)\s*:\s*ℝ\s*\)", r"\1", e)
        cleaned.add(canon(e))
    return cleaned - {"2"}


def main() -> int:
    lines = paper_path().read_text(encoding="utf-8").splitlines()
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    unexplained: list[tuple[str, list[str]]] = []
    compared = 0
    bodies = definition_bodies()

    for node in manifest.get("nodes") or []:
        rng = re.search(re.escape(paper_path().name) + r":(\d+)-(\d+)", node["source"])
        if not rng:
            continue
        a, b = int(rng.group(1)), int(rng.group(2))
        seg = "\n".join(lines[a - 1:b])
        text = (ROOT / node["file"]).read_text(encoding="utf-8")
        blk = text[text.index("-- FROZEN-STATEMENT-BEGIN"):
                   text.index("-- FROZEN-STATEMENT-END")]
        pe, pexp = paper_exponents(seg)
        le = lean_exponents(with_definitions(blk, bodies))
        if pexp and not re.search(r"Real\.exp|rexp|Real\.log",
                                  with_definitions(blk, bodies)):
            unexplained.append((node["id"], ["e^{...}: the paper's statement has an "
                                            "exponential and the Lean statement has no `Real.exp`"]))
        compared += 1
        allowed = EXPECTED_ABSENT.get(node["id"], {})
        missing = [e for e in sorted(pe) if e not in le and e not in allowed]
        print(f"  {node['id']:24s} paper {sorted(pe)}")
        print(f"  {'':24s} lean  {sorted(le)}")
        for e in sorted(pe):
            if e in allowed:
                print(f"  {'':24s}   {e}: {allowed[e]}")
        if missing:
            unexplained.append((node["id"], missing))

    if unexplained:
        print("\ncheck_exponents: a paper exponent has no counterpart in Lean:",
              file=sys.stderr)
        for nid, ms in unexplained:
            print(f"  {nid}: {', '.join(ms)}", file=sys.stderr)
        return 1
    print(f"\ncheck_exponents: OK ({compared} statements; every paper exponent "
          f"appears in its Lean statement or is explained above)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
