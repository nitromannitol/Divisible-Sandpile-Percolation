import Sandpile.Support.ExplGreenFubini
import Sandpile.Support.ExplHorizonMartingale
import Sandpile.Support.StopMeasurable

/-!
# Natural stopping times in the continuous Fubini and horizon identities

Natural stopping times in the continuous heat-potential Fubini and horizon identities.

Strongly measurable motion coordinates make every natural Brownian stopping time measurable in
the ambient space. The stopped-field interchange therefore applies to every admissible bounded
stop. The backward-martingale criterion uses exactly the same stopping class, with its analytic
hypotheses retained.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Continuum

open Sandpile.Support

/-- **The backward-martingale horizon-free increment, restricted to natural stopping times.**
Specializes `horizonFreeIncrement_of_backward_martingale` to the natural filtration of `B`: every
`IsBrownianStopping B τ` is measurable there and is a stopping time for it
(`isBrownianStopping_iff_natFiltration`), so the martingale hypothesis need only be checked on
this one class. -/
theorem horizonFreeIncrement_of_natural_backward_martingale {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → Space d)
    (hBc : ∀ ω, Continuous fun r => B r ω) (hBm : ∀ r, StronglyMeasurable (B r))
    (h : ℝ → Space d → ℝ) (hc : Continuous fun p : ℝ≥0 × Space d => h p.1 p.2)
    (t T : ℝ≥0) (htT : t ≤ T) (z : Space d) (hstart : ∀ᵐ ω ∂P, B 0 ω = z)
    (hM : Martingale (fun r ω => h (T - min r t : ℝ≥0) (B (min r t) ω) -
      h (t - min r t : ℝ≥0) (B (min r t) ω)) (LatticeProb.natFiltration B hBm) P)
    (D : Ω → ℝ) (hD : Integrable D P)
    (hdom : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, r ≤ t →
      ‖h (T - r : ℝ≥0) (B r ω)‖ ≤ D ω ∧ ‖h (t - r : ℝ≥0) (B r ω)‖ ≤ D ω) :
    HorizonFreeIncrement B P h t T z := by
  exact horizonFreeIncrement_of_backward_martingale P B hBc hBm h hc t T htT z hstart
    (LatticeProb.natFiltration B hBm)
    (fun τ hτ => ⟨hτ.measurable hBm, (isBrownianStopping_iff_natFiltration B hBm τ).1 hτ⟩)
    hM D hD hdom

/-- **The pointwise stopped-field identity, for an `IsBrownianStopping` stop.** Restates
`gaussianPotential_stopped_integral_comm_pointwise` with the hypothesis `IsBrownianStopping B τ`
in place of bare measurability of `τ`, using that such a `τ` is measurable
(`IsBrownianStopping.measurable`). -/
theorem gaussianPotential_stopping_integral_comm_pointwise {ΩW ΩB : Type*}
    [MeasurableSpace ΩW] [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {PW : Measure ΩW} [IsProbabilityMeasure PW] {W : (Space d → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise d W PW) (ν2 : ℝ) (Z : ℝ → Space d → ΩW → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[PW] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (B : ℝ≥0 → ΩB → Space d)
    (hBc : ∀ ω, Continuous fun t => B t ω) (hBm : ∀ t, StronglyMeasurable (B t))
    (τ : ΩB → ℝ≥0) (hτ : IsBrownianStopping B τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    (∀ᵐ ω ∂PW, Integrable (fun b => Z ((T : ℝ) - τ b) (B (τ b) b) ω) PB) ∧
      W (fun y => ∫ b, Real.sqrt ν2 *
        greenTimeBM d ((T : ℝ) - τ b) (B (τ b) b) y ∂PB) =ᵐ[PW]
        fun ω => ∫ b, Z ((T : ℝ) - τ b) (B (τ b) b) ω ∂PB := by
  exact gaussianPotential_stopped_integral_comm_pointwise hd hd3 hW ν2 Z hmod hc PB B hBc hBm
    τ (hτ.measurable hBm) T hτT

end Sandpile.Continuum
