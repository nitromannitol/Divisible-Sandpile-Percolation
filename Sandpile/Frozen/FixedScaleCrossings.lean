/-
Proposition of Section 4 of sandpile.tex, frozen.  `sandpile.tex:2157-2164`
(label `prop:fixed-scale-crossings`):

  "For every $\theta>0$ there is $p>0$ such that, for every $L\geq0$,
   \[
     \liminf_{R\to\infty}
     \P\bigl(H_{[-\theta R,\theta R]\times[0,2R]}(L/R)\bigr)
     \geq p\, ."

The objects are those of `ssec:admissible` and `ssec:fixed-scale-crossings`.

`sandpile.tex:2074-2088`: "Fix $d=2$ or $d=3$.  For $u\in\R^2$ and $0<s\leq1$,
let
\[
  \mathcal X_s(u)\coloneqq
  \begin{cases}
  \int_{\R^2}\frac1{2\pi}\log\frac{s}{|u-z|}\mathbf 1_{\{|u-z|<s\}}\mathcal W(dz),& d=2\, ,\\
  \int_{\R^3}\frac1{4\pi}\left(\frac1{|(u,0)-z|}-\frac1s\right)\mathbf 1_{\{|(u,0)-z|<s\}}\mathcal W(dz),& d=3\, .
  \end{cases}
\]"
That is `ballField` below, the white noise tested against `ballKernel`.

`sandpile.tex:2112-2118`: "For a rectangle $\mathcal R$ in the plane, write
$H_{\mathcal R}(\ell)$ for the event that $\{\mathcal X_1\geq\ell\}\cap\mathcal R$
contains a compact connected left-right crossing of $\mathcal R$.  Bottom-top
crossings are defined analogously.  For open sets, ``crosses'' means that the
set contains a compact connected subset joining the two opposite sides."
That is `Crosses` below, applied to the level set of `ballField d W 1` at level
`ℓ = L/R` and to the rectangle `[-θR,θR]×[0,2R]` in its left-right direction,
which is the coordinate direction `0`.

Modelling choices.

`\mathcal X_1` is a fixed field, so its crossing probabilities do not depend on
the space carrying the white noise; `p` is therefore bound before that space,
after `d` and `θ` and before `L`, exactly as the paper orders `θ`, `p`, `L`.
Mathlib 4.32 constructs no white noise, so the space carrying it is quantified
over, and taken in `Type` so that it can be bound inside the existential.

`\mathcal X_s` is a white-noise integral against a kernel that is not square
integrable in every dimension, but it is for `d ∈ {2,3}` and `s ≤ 1`, which the
statement fixes; the definition itself needs no such hypothesis.  The kernel is
written as one formula with the paper's two cases selected by `d`, and the
identification of `u\in\R^2` with `(u,0)` for `d=3` is `planePoint`.

The paper's `\liminf_{R\to\infty}` is `Filter.liminf … atTop` computed in
`ℝ≥0∞`, where the probability of the possibly non-measurable crossing event is
its outer measure; keeping the comparison in `ℝ≥0∞` avoids the junk of
`ENNReal.toReal` and makes `p` a genuine lower bound.

The paper writes the rectangle as `[-θR,θR]×[0,2R]`; the corner vectors are
`![-(θ*R), 0]` and `![θ*R, 2*R]`, and the crossing direction is `0`.  For small
`R` the rectangle can be degenerate, but only the behaviour as `R → ∞` is
asserted.
-/
import Sandpile.Continuum.WhiteNoise
import Sandpile.External.ContinuumRSW
import Sandpile.External.PittGaussianFKG
import Sandpile.Support.CrossExploreExists

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Frozen.FixedScaleCrossings

end Sandpile.Frozen.FixedScaleCrossings

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.fixed_scale_crossings
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (θ : ℝ) (hθ : 0 < θ) :
    ∃ p : ℝ, 0 < p ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P,
          Continuous (fun u : Sandpile.Continuum.Space 2 =>
            Sandpile.Frozen.FixedScaleCrossings.ballField d W s u ω)) →
      ∀ L : ℝ, 0 ≤ L →
        ENNReal.ofReal p ≤ liminf (fun R : ℝ => P {ω |
          Sandpile.Frozen.FixedScaleCrossings.Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
            {u : Sandpile.Continuum.Space 2 |
              L / R ≤ Sandpile.Frozen.FixedScaleCrossings.ballField d W 1 u ω}}) atTop
-- FROZEN-STATEMENT-END
:=
  Sandpile.Support.fixed_scale_crossings_proved hRSWc hPitt d hd θ hθ
