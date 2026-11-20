import Sandpile.External.PlanarRSWProved
import Sandpile.External.LSSDominationProved
import Sandpile.Frozen.D4BallGreenCrossing
import Sandpile.Frozen.D4CriticalLevelPercolation

/-!
# Dimension-four percolation consequences

The planar RSW and domination inputs yield the ball-killed Green crossing
estimate and critical-level percolation without external hypotheses.
-/

open MeasureTheory ProbabilityTheory

/-- The dimension-four ball-killed Green crossing estimate. -/
theorem Sandpile.d4_ball_green_crossing
    (ν₀ θ₀ K₀ ϑ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) (hϑ : 1 ≤ ϑ) :
    ∀ ε : ℝ, 0 < ε → ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∃ r₀ : ℕ,
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ r : ℕ, r₀ ≤ r → ∀ x : Sandpile.Site 4,
          LatticeProb.iidLaw 4 ν
              {ζ | Sandpile.HasStarTopBottomCrossing ϑ r x
                {z | Sandpile.ballGreenField r ζ z ≤ -(ε * Real.log r)}} ≤
            ENNReal.ofReal (C * (Real.log r) ^ 3 * (r : ℝ) ^ (-γ)) :=
  Sandpile.Frozen.d4_ball_green_crossing Sandpile.External.planarRSW_holds
    ν₀ θ₀ K₀ ϑ hν₀ hθ₀ hϑ

/-- Critical-level percolation in the coordinate plane in dimension four. -/
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
              c * Real.log t < Sandpile.odometer σ t (Sandpile.planeEmbed z)} :=
  Sandpile.Frozen.d4_critical_level_percolation Sandpile.External.planarRSW_holds
    Sandpile.External.lssDomination ν₀ θ₀ K₀ hν₀ hθ₀
