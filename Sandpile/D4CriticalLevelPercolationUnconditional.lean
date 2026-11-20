import Sandpile.External.PlanarRSWProved
import Sandpile.External.LSSDominationProved
import Sandpile.Frozen.D4CriticalLevelPercolation

/-!
# Critical-level percolation in dimension four

The critical level sets of the odometer in the coordinate plane percolate in
dimension four without cited hypotheses: the planar RSW input is supplied by
`Sandpile.External.planarRSW_holds` and the domination input by
`Sandpile.External.lssDomination`.
-/

open MeasureTheory ProbabilityTheory

/-- Critical-level percolation in the coordinate plane in dimension four. -/
-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.d4_critical_level_percolation
    (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.centeredMassLaw 4 ν),
          Sandpile.HasInfiniteComponent
            {z : Sandpile.Site 2 |
              c * Real.log t < Sandpile.odometer σ t (Sandpile.planeEmbed z)}
-- FROZEN-STATEMENT-END
:=
  Sandpile.Frozen.d4_critical_level_percolation Sandpile.External.planarRSW_holds
    Sandpile.External.lssDomination ν₀ θ₀ K₀ hν₀ hθ₀
