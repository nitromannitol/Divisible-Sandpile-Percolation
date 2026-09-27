/-
Proposition of sandpile.tex, frozen.  `sandpile.tex:4894-4896`
(label `prop:dgt4-contact-asymptotics`):

  "As $n \to \infty$, we have $\P(u_n(0)=0)\sim\frac{G(0,0)\kappa}{n}$."

The standing hypotheses are those of `sandpile.tex:4641-4643`: "Throughout the
remainder of this subsection, we assume the hypotheses of
Theorem~\ref{thm:dgt4-diffusive-membrane}, and $\kappa$ denotes the exponent
defined there."  They are therefore transcribed here in full, exactly as in
`Sandpile/Frozen/DGT4DiffusiveMembrane.lean`: `d ≥ 5`, the scenery i.i.d.,
atomless, centred, of finite positive variance, and either Gaussian, in which
case `κ = 1`, or bounded above with a lower tail regularly varying of index
`-α` for some `α > 2`, in which case `κ = 1 - 1/α`.  The disjunction pins `κ`
in each branch; the proposition is proved case by case at
`sandpile.tex:4969` and `sandpile.tex:5306`.

Modelling decisions.

The scenery is written in the mass normalization: the integration variable is
`σ` with law `Sandpile.centeredMassLaw d ν`, so `ζ = (σ-1)/(2d)` has one-site
law `ν` and `u_n(0)` is `Sandpile.odometer σ n 0`.

`f ∼ g` is `Tendsto (f / g) atTop (𝓝 1)`.  The probability is the `toReal` of
the measure of the event `{σ | u_n(0) = 0}`; the event is measurable, since
`u_n(0)` depends on finitely many coordinates.  The quotient is by
`G(0,0)κ/n`, which vanishes at `n = 0`; the junk value `x/0 = 0` there is
invisible to the `atTop` filter, and `G(0,0)κ > 0` for every `n ≥ 1` because
`d ≥ 5` makes `G(0,0)` finite and positive and each branch of `hcase` makes
`κ > 0`.

Cited inputs (standing convention R1).  Step 4 of case (a) bounds the conditional
mean increment for `y \leq -1` by Gaussian concentration for the Lipschitz
functional `\Theta_n` (`sandpile.tex:5267-5271`); that inequality is Borell's and
Tsirelson-Ibragimov-Sudakov's, cited and not proved in the paper, and enters here
as `hGaussConc` at version 3.  `hGreenHigh` carries the `d \geq 5` Green estimates
of `ssec:green-estimates` the two cases use throughout.
-/
import Sandpile.Law
import Sandpile.Walk
import Sandpile.External.GreenBoundsHigh
import Sandpile.External.GaussianLipschitzConcentration
import Sandpile.Support.Dgt4AFinal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_contact_asymptotics
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (κ : ℝ)
    (hcase :
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧ κ = 1) ∨
      (∃ α : ℝ, 2 < α ∧ (∃ M : ℝ, ν (Set.Ioi M) = 0) ∧
        (∀ lam : ℝ, 0 < lam →
          Tendsto (fun r : ℝ => (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
            atTop (𝓝 (lam ^ (-α)))) ∧
        κ = 1 - 1 / α)) :
    Tendsto (fun n : ℕ =>
        ((Sandpile.centeredMassLaw d ν) {σ | Sandpile.odometer σ n 0 = 0}).toReal /
          (Sandpile.green d 0 0 * κ / n)) atTop (𝓝 1)
-- FROZEN-STATEMENT-END
:= by
  have hGreenHigh : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
  exact Sandpile.dgt4_contact_asymptotics_of_hcase hGreenHigh hGaussConc d hd ν hatom hmean hvar
    hvar' κ hcase
