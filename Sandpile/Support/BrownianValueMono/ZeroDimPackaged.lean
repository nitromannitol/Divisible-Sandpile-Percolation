import Sandpile.Support.BrownianValueMono.HorizonFreeZeroDim
import Sandpile.Support.BrownianValueMono.Envelope
import Sandpile.Support.ExplBallGrowthZero

/-!
# The horizon-monotonicity hypotheses in dimension zero

The mirror of `Sandpile.Continuum.horizonFree_and_bddAbove_positive_dim` for the degenerate
dimension the family martingale theorem does not cover. Both hypotheses of
`Sandpile.Continuum.brownianValue_mono_horizon` come from the same growth-to-envelope route
(`Sandpile.Continuum.exists_envelope_of_samplewise_growth`, fed by
`Sandpile.Continuum.ballGrowthResidual_zero`) for boundedness, and from the direct affine
computation of `Sandpile.Support.BrownianValueMono.HorizonFreeZeroDim` for horizon-freeness.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum
open Sandpile.Support

/-- **In dimension zero, the horizon-freeness of the payoff and the boundedness of the
attainable stopping payoffs, jointly, for every base point and every horizon `s ≤ T`.** The
mirror of `horizonFree_and_bddAbove_positive_dim` for the degenerate dimension the family
theorem there does not cover: the space is a single point, the field is exactly affine in time,
and every admissible payoff has the same increment whichever horizon it is measured from. -/
theorem horizonFree_and_bddAbove_zero_dim
    {ΩW : Type} [MeasurableSpace ΩW] {PW : Measure ΩW} [IsProbabilityMeasure PW]
    {W : (Space 0 → ℝ) → ΩW → ℝ} (hW : IsWhiteNoise 0 W PW) (ν2 : ℝ) (hν2 : 0 ≤ ν2)
    (Z : ℝ → Space 0 → ΩW → ℝ)
    (hmod : ∀ (t : ℝ) (x : Space 0), Z t x =ᵐ[PW] gaussianPotential 0 ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space 0 => Z p.1 p.2 ω) (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    {ΩB : Type} [MeasurableSpace ΩB] {PB : Measure ΩB} [IsProbabilityMeasure PB]
    (B : Space 0 → ℝ≥0 → ΩB → Space 0) (hB : ∀ x, IsBrownian 0 x (B x) PB)
    (hBc : ∀ (x : Space 0) (b : ΩB), Continuous fun r => B x r b)
    (hBm : ∀ (x : Space 0) (t : ℝ≥0), StronglyMeasurable (B x t))
    (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂PW, ∀ x : Space 0, ∀ s : ℝ, 0 ≤ s → s ≤ T →
      HorizonFreeIncrement (B x) PB (fun t y => Z t y ω) s T x ∧
        BddAbove (stoppingPayoffs (B x) PB (fun t y => Z t y ω) T) := by
  have hgrow := ballGrowthResidual_zero ΩW PW W hW ν2 hν2 Z hmod hc T hT
  have haff := gaussianPotential_eq_affine_zero_dim hW ν2 Z hmod T hT (hc T hT)
  filter_upwards [hgrow, haff, hc T hT] with ω hgω haffω hcω
  intro x s hs0 hsT
  obtain ⟨C, hC, p, hgp⟩ := hgω
  obtain ⟨D, hD, hdom⟩ := exists_envelope_of_samplewise_growth (hB x)
    (fun t => (hBm x t).measurable) (hBc x) (fun t y => Z t y ω) T hT.le C hC p hgp
  have hbdd : BddAbove (stoppingPayoffs (B x) PB (fun t y => Z t y ω) T) :=
    bddAbove_stoppingPayoffs_of_envelope (hB x) (fun t y => Z t y ω) T hcω D hD hT.le hdom
  have hinc : HorizonFreeIncrement (B x) PB (fun t y => Z t y ω) s T x :=
    horizonFreeIncrement_zero_dim (z := x) (B := B x) (hBm x) (fun t y => Z t y ω)
      (Real.sqrt ν2 * W (fun _ : Space 0 => (1 : ℝ)) ω) s T hs0 hsT (fun s' hs' => haffω x s' hs')
  exact ⟨hinc, hbdd⟩

end Sandpile.Continuum
