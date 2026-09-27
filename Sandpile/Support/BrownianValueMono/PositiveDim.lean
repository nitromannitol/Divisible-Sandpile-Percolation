import Sandpile.Support.BrownianValueMono.Envelope
import Sandpile.Support.ExplGaussianFamily
import Sandpile.Support.BallGrowthExternal

/-!
# The horizon-monotonicity hypotheses in dimension `1 ≤ d ≤ 3`

`Sandpile.Continuum.brownianValue_mono_horizon` (`Sandpile/Support/ExplHorizon.lean`) needs, at
each base point `x` and each horizon `s ≤ T`, that the payoff of every admissible stopping time
does not depend on the horizon (`HorizonFreeIncrement`) and that the attainable stopping payoffs
at the top horizon are bounded above. This module supplies both, for `1 ≤ d ≤ 3`, from the
samplewise polynomial growth of the Gaussian heat potential
(`Sandpile.Continuum.ballGrowthResidual_of_external`) and the backward heat-increment martingale
along the motion
(`Sandpile.Support.gaussianPotential_horizonFreeIncrement_family_of_stopped_integrability`): the
growth bound gives an integrable envelope
(`Sandpile.Continuum.exists_envelope_of_samplewise_growth`) that discharges both the boundedness
itself and the stopped-integrability side condition the martingale identity needs.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum
open Sandpile.Support

/-- **In dimension `1 ≤ d ≤ 3`, the horizon-freeness of the payoff and the boundedness of the
attainable stopping payoffs, jointly, for every base point and every horizon `s ≤ T`.**
This packages the two hypotheses `Sandpile.Continuum.brownianValue_mono_horizon` needs, both
derived from the samplewise polynomial growth of the field (`ballGrowthResidual_of_external`)
and the backward heat-increment martingale
(`gaussianPotential_horizonFreeIncrement_family_of_stopped_integrability`). -/
theorem horizonFree_and_bddAbove_positive_dim {d : ℕ} (hd1 : 1 ≤ d) (hd3 : d ≤ 3)
    {ΩW : Type} [MeasurableSpace ΩW] {PW : Measure ΩW} [IsProbabilityMeasure PW]
    {W : (Space d → ℝ) → ΩW → ℝ} (hW : IsWhiteNoise d W PW) (ν2 : ℝ) (hν2 : 0 ≤ ν2)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hmod : ∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    {ΩB : Type} [MeasurableSpace ΩB] {PB : Measure ΩB} [IsProbabilityMeasure PB]
    (B : Space d → ℝ≥0 → ΩB → Space d) (hB : ∀ x, IsBrownian d x (B x) PB)
    (hBc : ∀ (x : Space d) (b : ΩB), Continuous fun r => B x r b)
    (hBm : ∀ (x : Space d) (t : ℝ≥0), StronglyMeasurable (B x t))
    (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂PW, ∀ x : Space d, ∀ s : ℝ, 0 ≤ s → s ≤ T →
      HorizonFreeIncrement (B x) PB (fun t y => Z t y ω) s T x ∧
        BddAbove (stoppingPayoffs (B x) PB (fun t y => Z t y ω) T) := by
  have hgrow := ballGrowthResidual_of_external d hd1 hd3 ΩW PW W hW ν2 hν2 Z hmod hc T hT
  have hfam := gaussianPotential_horizonFreeIncrement_family_of_stopped_integrability hd1 hd3 hW
    ν2 Z (fun t _ht x => hmod t x) hc B hB hBm hBc
  filter_upwards [hgrow, hfam, hc T hT] with ω hgω hfamω hcω
  intro x s hs0 hsT
  obtain ⟨C, hC, p, hgp⟩ := hgω
  obtain ⟨D, hD, hdom⟩ := exists_envelope_of_samplewise_growth (hB x)
    (fun t => (hBm x t).measurable) (hBc x) (fun t y => Z t y ω) T hT.le C hC p hgp
  have hbdd : BddAbove (stoppingPayoffs (B x) PB (fun t y => Z t y ω) T) :=
    bddAbove_stoppingPayoffs_of_envelope (hB x) (fun t y => Z t y ω) T hcω D hD hT.le hdom
  have hcs : ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc (0 : ℝ) s ×ˢ Set.univ) :=
    hcω.mono (Set.prod_mono (Set.Icc_subset_Icc_right hsT) (le_refl _))
  have hdoms : ∀ b : ΩB, ∀ r : ℝ≥0, (r : ℝ) ≤ s → ‖Z (s - r) (B x r b) ω‖ ≤ D b :=
    fun b r hr => hdom b s hs0 hsT r hr
  set t0 : ℝ≥0 := s.toNNReal with ht0
  set bigT0 : ℝ≥0 := T.toNNReal with hbigT0
  have hcast_s : (t0 : ℝ) = s := Real.coe_toNNReal s hs0
  have hcast_T : (bigT0 : ℝ) = T := Real.coe_toNNReal T hT.le
  have hle0 : t0 ≤ bigT0 := Real.toNNReal_le_toNNReal hsT
  have hI : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping (B x) τ → (∀ b, τ b ≤ t0) →
      Integrable (fun b => Z ((t0 : ℝ) - τ b) (B x (τ b) b) ω) PB := by
    intro τ hτ hτt
    rw [hcast_s]
    refine integrable_stopped_of_envelope (hB x) (fun t y => Z t y ω) s hcs D hD hdoms τ hτ ?_
    intro b
    exact hcast_s ▸ (NNReal.coe_le_coe.mpr (hτt b))
  have hinc0 := hfamω x t0 bigT0 hle0 hI
  rw [hcast_s, hcast_T] at hinc0
  exact ⟨hinc0, hbdd⟩

end Sandpile.Continuum
