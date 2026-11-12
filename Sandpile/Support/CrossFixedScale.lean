import Sandpile.Support.CrossZeroLevel
import Sandpile.Support.CrossLiminf
import Sandpile.Support.CrossDuality

/-!
# Assembling the fixed-scale crossing proposition

`prop:fixed-scale-crossings` (`sandpile.tex:2121-2128`) assembled from the three
inputs its proof uses, so that what remains of the proposition is exactly those
three and nothing else:

* the square estimate `P(H_{[-R,R]^2}(0)) ≥ 1/2` of `sandpile.tex:2235-2236`,
  which is continuum duality together with the sign symmetry of the field, here
  for a square anchored anywhere, in the translated-field form the crossing sets
  take;
* the level loss `P(H(0)) - P(H(L/R)) ≤ C L R^{-α}` of
  `sandpile.tex:2302-2309`, which is the subquadratic exploration of Step 2 and
  the Cameron-Martin shift of Step 3;
* the continuum RSW comparison itself, `External.ContinuumRSW`, the hypothesis
  the frozen statement carries.

The crossing probabilities are the outer measures of subsets of the probability
space carrying the field, and the passage between a rectangle and its translate
is an equality of those subsets (`crossingSet_translate`), not a comparison of
measures of different sets.  On the space of ALL planar functions every
crossing event has outer measure one (`Sandpile/Support/CrossVacuity.lean`),
which is why the crossing statements are about a field on its probability space.

The square estimate is proved, from planar duality and the symmetry of the
field, in `Sandpile/Support/CrossDuality.lean`, at the level `-ε` for every
`ε > 0`; the duality it rests on is proved by discretization in
`Sandpile/Support/CrossGrid.lean`, so neither is an assumption any more.
`fixed_scale_crossings_of_level_loss` is the assembly that uses it, and what is
left of the proposition there is the level loss of Steps 2 and 3.  The level
loss is the long part of the paper's proof and is not touched.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- The conclusion of `prop:fixed-scale-crossings` for a planar field `X` on a
probability space, from the square estimate, the level loss and the continuum
RSW comparison. -/
theorem fixed_scale_crossings_of_inputs
    (hRSW : Sandpile.External.ContinuumRSW) (θ : ℝ) (hθ : 0 < θ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (hmeas : ∀ u, Measurable (X u))
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω)
    (hsym : Sandpile.Continuum.IsSymmetricField P X)
    (hass : Sandpile.Continuum.IsAssociatedField P X)
    (lev : ℝ)
    (hsq : ∀ (v : Sandpile.Continuum.Space 2) (s : ℝ), 1 ≤ s →
      (1 : ℝ) / 2 ≤ P.real {ω |
        Crosses ![0, 0] ![2 * s, 2 * s] 0 {u | lev ≤ X (u + v) ω}})
    (C α : ℝ) (hα : 0 < α)
    (hloss : ∀ L : ℝ, 0 ≤ L → ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
      P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | lev ≤ X u ω}} ≤
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω}} +
          ENNReal.ofReal (C * L * R ^ (-α))) :
    ∃ p : ℝ, 0 < p ∧ ∀ L : ℝ, 0 ≤ L →
      ENNReal.ofReal p ≤ Filter.liminf (fun R : ℝ =>
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω}}) atTop := by
  obtain ⟨c, hc, hzero⟩ :=
    crossing_level_of_square hRSW θ hθ P X hmeas hcont hsym hass lev hsq
  refine ⟨c / 2, by linarith, fun L hL => ?_⟩
  exact liminf_crossing_of_level_and_loss P X θ lev c C α (max 1 θ⁻¹) hc hα hzero L (hloss L hL)

/-- The fixed-scale crossing estimate from the level loss alone.  The square
estimate is no longer an assumption: it is proved in
`Sandpile/Support/CrossDuality.lean` from the continuum planar duality of
`Sandpile/Support/CrossGrid.lean` and the symmetry of the field, at the level
`-ε` the grid and the bracket of the chain events give.  What is left of
`prop:fixed-scale-crossings` is the level loss of Steps 2 and 3. -/
theorem fixed_scale_crossings_of_level_loss
    (hRSW : Sandpile.External.ContinuumRSW)
    (θ : ℝ) (hθ : 0 < θ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (hmeas : ∀ u, Measurable (X u))
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω)
    (hsym : Sandpile.Continuum.IsSymmetricField P X)
    (hass : Sandpile.Continuum.IsAssociatedField P X)
    (ε : ℝ) (hε : 0 < ε) (C α : ℝ) (hα : 0 < α)
    (hloss : ∀ L : ℝ, 0 ≤ L → ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
      P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | -ε ≤ X u ω}} ≤
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω}} +
          ENNReal.ofReal (C * L * R ^ (-α))) :
    ∃ p : ℝ, 0 < p ∧ ∀ L : ℝ, 0 ≤ L →
      ENNReal.ofReal p ≤ Filter.liminf (fun R : ℝ =>
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω}}) atTop :=
  fixed_scale_crossings_of_inputs hRSW θ hθ P X hmeas hcont hsym hass (-ε)
    (square_half_translate P X hmeas hcont hsym ε hε) C α hα hloss

end Sandpile.Support
