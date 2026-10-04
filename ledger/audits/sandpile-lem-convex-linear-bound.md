# Audit report — `lem-convex-linear-bound`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `lem-convex-linear-bound` |
| export | `Sandpile.Frozen.convex_linear_bound` |
| file | `Sandpile/Frozen/ConvexLinearBound.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | sandpile.tex:1548-1570 (label `lem-convex-linear-bound`) |
| provider | `Sandpile.Frozen.convex_linear_bound` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.Frozen.convex_linear_bound` starting
`∃ C > 0, ∀ N ν, …`, concluding
`∫ (F ξ - E F - Σ (E D i) ξ i)² ∂(π) ≤ C L² Σ Var(D i) + C η(L) Σ b i²`,
with `η(L) = Sandpile.truncatedGap ν L`. This is the paper's display term by term:
coordinatewise convexity, `0 ≤ ∂_i⁺F ≤ b_i` a.s., `b_i` deterministic, `C` universal
(bound before `N`, the law, `F`, `D`, `b`, `L`), and the right partial derivative
modelled by a supplied `D` with `HasDerivWithinAt` rather than `derivWithin` (so no junk
derivative at non-differentiability). `truncatedGap` is the paper's iterated integral
with the strict `L < |y-z|`; the quantifier order matches `sandpile.tex:1548-1570`.

## 2. Proof and axiom closure

The proof invokes the registered provider `LatticeProb.exists_efron_stein_L2` and
reduces the goal to that provider's conclusion after centring `F` by its mean and the
linear term. It compiles; `clean lem-convex-linear-bound`.

## 3. Non-vacuity / junk

Hypotheses are satisfiable: `N = 1`, `F(x) = x²`, `D x = 2x`, `b = 1` on a compactly
supported law, `ν = gaussianReal 0 1`, `L = 1` satisfy every binder. **Junk-guard
observed:** the proof splits on integrability of the squared centred integrand; in the
non-integrable branch `integral_undef` makes the integral `0` and only non-negativity of
the right-hand side is used. Under the hypotheses the integrand is in fact integrable
(convexity plus `0 ≤ ∂_i⁺F ≤ b_i` gives linear growth against a finite second moment), so
this branch is unreachable on the paper's instances and the conclusion is non-vacuous.

## 4. Citations

The node carries no `External` hypothesis; the provider is a library theorem. The
paper anchor and the universal constant are as stated. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean lem-convex-linear-bound`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.Frozen.convex_linear_bound` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.Frozen.convex_linear_bound`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
