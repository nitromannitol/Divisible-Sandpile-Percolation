# Design decisions

Owner rulings that govern the formalization.  They are statement-level
constraints, not implementation suggestions.

## 2026-09-27

### D-001

`ext-brownian-exit-step` is repaired (owner ruling 2026-09-27, "Yes approve the
repair").  Version 2 of the frozen Prop quantified over every field `h` that is
continuous on `[0, T] × ℝ^d`, with no growth condition, and bounded the reward
after the exit by the supremum of the values at the full horizon `T`.  It is
false in two independent ways.

1. Integrability.  For `d = 1`, `K = {0}`, `u = 0`, `A = T = 1`, `τ ≡ T` and
   `h(t, x) = -exp(x²)`: on `{τ_{0,1} < 1}` the exit term is the constant `-e`
   (the exit time is the infimum of a closed set, so `|B_σ| = 1`), while
   `E[exp(B_1²)] = ∞` because `Var B_1 = 1 ≥ 1/2`; the integrand is not
   integrable and the Bochner integral is `0` by convention
   (`MeasureTheory.integral_undef`).  Constant stopping times `τ ≡ t` with
   `t ↑ 1/2` show that the payoff set of every motion is unbounded above, so each
   discount is `0` by convention (`Real.sSup_of_not_bddAbove`) and each value is
   `-exp(z²)`; the supremum over `|z| ≤ 1` is `-1`.  The inequality reads
   `0 ≤ -P(τ_{0,1} < 1)`, which is false.  A Brownian family with every path
   continuous and every time slice measurable exists
   (`LatticeProb.exists_isBrownianSpace_cont`), so the hypotheses are
   satisfiable and the counterexample is genuine; it was checked against the
   repository definitions on 2026-09-27.
2. Horizon.  For `h(t, x) = sin(π t / T)` (bounded, so every envelope condition
   holds) and `τ ≡ T`: the left side is `E[sin(π (T - σ) / T); σ < T] > 0`, while
   every value at horizon `T` is `0`, so the right side is `0`.

Consequence: `lem-brownian-ball-localization`, SEALED with `hExit :
BrownianExitStep` as a hypothesis, was vacuous.

Ruling.  Version 3 of `ext-brownian-exit-step` (a cited input, the strong
Markov property of Brownian motion at the exit time of the ball; Mörters and
Peres, *Brownian Motion*, Theorem 2.16) adds an integrable envelope of `h` along
the motions started within `A` of `K`, with expectations bounded uniformly, and
takes the supremum of the values over every remaining horizon `s ∈ [0, T]`.  The
monotonicity of the value of the Gaussian heat potential in the horizon, which
turns that supremum into the value at `T`, is a paper-internal obligation, the
new node `lem-brownian-value-mono-horizon`, not a cited input.
`lem-brownian-ball-localization` keeps its statement and is re-established on
version 3 and on that node.  The paper copy is corrected to give the proof
(`paper/CHANGES_FROM_ARXIV.md`, item 9).
