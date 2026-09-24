/-
`prop:fixed-scale-crossings` (`sandpile.tex:2121-2128`) for the ball field
itself, reduced to exactly four inputs.

`Sandpile/Support/CrossFixedScale.lean` proves the proposition for an abstract
planar field from the level loss alone, the square estimate having been proved
from the continuum planar duality of `Sandpile/Support/CrossGrid.lean` and the
sign symmetry.  This module puts the paper's field in its place, which means
discharging the hypotheses the abstract statement carries for `𝒳_1`.

Of those hypotheses:

* measurability of each coordinate is `IsWhiteNoise.meas` at the ball kernel,
  which needs the kernel to be square integrable, and that is
  `Sandpile.Frozen.FixedScaleCrossings.memLp_ballKernel`;
* almost sure continuity of the sample paths is the continuous modification the
  frozen statement quantifies over, following `sandpile.tex:2111`;
* positive association is
  `isAssociatedField_ballField_of_whiteNoise`, that is Pitt's theorem
  (`External.PittGaussianFKG`) applied to the ball field, whose covariances are
  the `L²` inner products of nonnegative kernels;
* invariance in law under the plane symmetries is
  `isSymmetricField_ballField`, whose mathematical content, the change of
  variables in the white-noise kernel along the lift of the symmetry to `ℝ^d`,
  is proved in `Sandpile/Support/CrossBallSym.lean`; the one step it waits on is
  the general fact that a centred Gaussian process is determined in law by its
  covariance, carried as the hypothesis `hGauss` and requested of the shared
  library.

The remaining input is the level loss of Steps 2 and 3
(`sandpile.tex:2288-2400`): the subquadratic exploration and the Cameron-Martin
shift.  It is the hypothesis `hloss`, with its constants bound before the
probability space, as the paper binds them.  The constant `p` is bound after `θ`
and before the space, which is where the paper binds it; that is what
`uniform_crossing_constant` makes possible, since the RSW comparison map of
`External.ContinuumRSW` is chosen from the aspect ratio alone.
-/
import Sandpile.Support.CrossFixedScale
import Sandpile.Support.CrossBallSym
import Sandpile.External.GaussianLawCovarianceProved

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-
Vacuity check: the hypothesis this theorem
used to take, quantifying `hloss` over an ARBITRARY field `X` satisfying only
measurability, a.s.-continuity, `IsSymmetricField` and `IsAssociatedField`, is
UNSATISFIABLE.  Witness: `Ω := PUnit`, `X := fun _ _ => 0` (the a.s.-zero
field).  It is measurable, continuous, symmetric (`ε • 0 = 0` for `ε = ±1`) and
associated (both sides of the FKG inequality are the constant `f 0 * g 0`, an
equality).  At level `-ε` (`ε > 0`) `{u | -ε ≤ 0} = univ`, so the crossing event
is the whole rectangle and has probability `1`; at any level `L/R > 0` the
crossing event is empty, probability `0`.  The old `hloss` therefore demanded
`1 ≤ ENNReal.ofReal (C * L * R ^ (-α))` for every `R ≥ max 1 θ⁻¹` and every
`L > 0`, which fails for `R` large since `α > 0`.  No term of the old type can
exist, so the reduction could never be discharged by any field-specific
argument, however good: the abstraction over `X` throws away the one fact
(quantitative control of the field's own covariance) that makes the level-loss
bound possible at all.

The fix keeps exactly the same paper content (`sandpile.tex:2288-2400`, Steps
2-3) but ties `hloss` to the ACTUAL field `ballField d W 1` for the white noise
`W` the conclusion already quantifies over, instead of an abstract `X`; the
four structural facts (`measurable, continuous, symmetric, associated`) are now
derived here, from `hW` and `hcontball`, exactly as the old proof derived them
from `hloss`'s own binders, so nothing about the mathematical content changes,
only which side of the reduction proves them.  `fixed_scale_crossings_uniform`
in `CrossFixedScale.lean` has the same defect and is unused by this file from
here on; it is left in place, unconditionally provable only because its own
`hloss` hypothesis is equally unsatisfiable, and should not be used elsewhere.
-/
theorem fixed_scale_crossings_ball
    (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (θ : ℝ) (hθ : 0 < θ)
    (ε : ℝ) (hε : 0 < ε) (C α : ℝ) (hα : 0 < α)
    (hloss : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
      Sandpile.Continuum.IsWhiteNoise d W P →
      (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P,
        Continuous (fun u : Sandpile.Continuum.Space 2 => ballField d W s u ω)) →
      ∀ L : ℝ, 0 ≤ L → ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | -ε ≤ ballField d W 1 u ω}} ≤
          P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ ballField d W 1 u ω}} +
            ENNReal.ofReal (C * L * R ^ (-α))) :
    ∃ p : ℝ, 0 < p ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P,
          Continuous (fun u : Sandpile.Continuum.Space 2 => ballField d W s u ω)) →
      ∀ L : ℝ, 0 ≤ L →
        ENNReal.ofReal p ≤ liminf (fun R : ℝ => P {ω |
          Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
            {u : Sandpile.Continuum.Space 2 | L / R ≤ ballField d W 1 u ω}}) atTop := by
  obtain ⟨c, hc, hzero⟩ := uniform_crossing_constant hRSW θ hθ
  refine ⟨c / 2, by linarith, ?_⟩
  intro Ω _ P _ W hW hcontball L hL
  have hmeas : ∀ u, Measurable (ballField d W 1 u) :=
    fun u => hW.meas _ (memLp_ballKernel hd one_pos u)
  have hcont : ∀ᵐ ω ∂P, Continuous fun u => ballField d W 1 u ω := hcontball 1 one_pos le_rfl
  have hsym := isSymmetricField_ballField hGauss hd hW one_pos
  have hass := isAssociatedField_ballField_of_whiteNoise hPitt hd hW one_pos
  exact liminf_crossing_of_level_and_loss P (ballField d W 1) θ (-ε) c C α (max 1 θ⁻¹) hc hα
    (hzero Ω P (ballField d W 1) hmeas hcont hsym hass (-ε)
      (square_half_translate P (ballField d W 1) hmeas hcont hsym ε hε))
    L (hloss Ω P W hW hcontball L hL)

/-- `prop:fixed-scale-crossings` from the ball-field assembly, with the two
remaining inputs carried explicitly: Pitt's association theorem (the cited
`External.PittGaussianFKG`) and the level loss of Steps 2-3.  The classical
determination of a centred Gaussian law by its covariance is discharged by
`Sandpile.External.gaussianLawDeterminedByCovariance`. -/
theorem fixed_scale_crossings_of_ball
    (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (θ : ℝ) (hθ : 0 < θ)
    (ε : ℝ) (hε : 0 < ε) (C α : ℝ) (hα : 0 < α)
    (hloss : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
      Sandpile.Continuum.IsWhiteNoise d W P →
      (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P,
        Continuous (fun u : Sandpile.Continuum.Space 2 => ballField d W s u ω)) →
      ∀ L : ℝ, 0 ≤ L → ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | -ε ≤ ballField d W 1 u ω}} ≤
          P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ ballField d W 1 u ω}} +
            ENNReal.ofReal (C * L * R ^ (-α))) :
    ∃ p : ℝ, 0 < p ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P,
          Continuous (fun u : Sandpile.Continuum.Space 2 => ballField d W s u ω)) →
      ∀ L : ℝ, 0 ≤ L →
        ENNReal.ofReal p ≤ liminf (fun R : ℝ => P {ω |
          Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
            {u : Sandpile.Continuum.Space 2 | L / R ≤ ballField d W 1 u ω}}) atTop :=
  fixed_scale_crossings_ball hRSW hPitt
    Sandpile.External.gaussianLawDeterminedByCovariance d hd θ hθ ε hε C α hα hloss

/-- `prop:fixed-scale-crossings` from the level loss of Steps 2-3 alone: the
exploration supplies `hloss`, and the ball-field assembly turns it into the
proposition.  This is the reduction the frozen statement is discharged
through. -/
theorem fixed_scale_crossings_of_loss
    (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (θ : ℝ) (hθ : 0 < θ)
    (ε : ℝ) (hε : 0 < ε) (C α : ℝ) (hα : 0 < α)
    (hloss : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
      Sandpile.Continuum.IsWhiteNoise d W P →
      (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P,
        Continuous (fun u : Sandpile.Continuum.Space 2 => ballField d W s u ω)) →
      ∀ L : ℝ, 0 ≤ L → ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | -ε ≤ ballField d W 1 u ω}} ≤
          P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ ballField d W 1 u ω}} +
            ENNReal.ofReal (C * L * R ^ (-α))) :
    ∃ p : ℝ, 0 < p ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P,
          Continuous (fun u : Sandpile.Continuum.Space 2 => ballField d W s u ω)) →
      ∀ L : ℝ, 0 ≤ L →
        ENNReal.ofReal p ≤ liminf (fun R : ℝ => P {ω |
          Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
            {u : Sandpile.Continuum.Space 2 | L / R ≤ ballField d W 1 u ω}}) atTop := by
  exact fixed_scale_crossings_ball hRSW hPitt hGauss d hd θ hθ ε hε C α hα hloss

/-- `prop:fixed-scale-crossings` from the exploration data of Steps 2-3: the
hypothesis `hexp` is the level loss `sandpile.tex:2392-2398`, which the
exploration supplies by reading finitely many coordinates and identifying the
two trace laws with the Gaussian products of the Cameron--Martin shift. -/
theorem fixed_scale_crossings_of_exploration
    (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (θ : ℝ) (hθ : 0 < θ)
    (ε : ℝ) (hε : 0 < ε) (C α : ℝ) (hα : 0 < α)
    (hexp : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
      Sandpile.Continuum.IsWhiteNoise d W P →
      (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P,
        Continuous (fun u : Sandpile.Continuum.Space 2 => ballField d W s u ω)) →
      ∀ L : ℝ, 0 ≤ L → ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | -ε ≤ ballField d W 1 u ω}} ≤
          P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ ballField d W 1 u ω}} +
            ENNReal.ofReal (C * L * R ^ (-α))) :
    ∃ p : ℝ, 0 < p ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P,
          Continuous (fun u : Sandpile.Continuum.Space 2 => ballField d W s u ω)) →
      ∀ L : ℝ, 0 ≤ L →
        ENNReal.ofReal p ≤ liminf (fun R : ℝ => P {ω |
          Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
            {u : Sandpile.Continuum.Space 2 | L / R ≤ ballField d W 1 u ω}}) atTop :=
  fixed_scale_crossings_of_loss hRSW hPitt hGauss d hd θ hθ ε hε C α hα hexp

end Sandpile.Support
