import Sandpile.External.PlanarRSWProved
import Sandpile.Frozen.D4BallGreenCrossing

/-!
# The dimension-four ball-killed Green crossing estimate

The crossing estimate for the ball-killed Green field in dimension four holds
without cited hypotheses: the planar RSW input is supplied by
`Sandpile.External.planarRSW_holds`.
-/

open MeasureTheory ProbabilityTheory

/-- The dimension-four ball-killed Green crossing estimate. -/
-- FROZEN-STATEMENT-BEGIN
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
            ENNReal.ofReal (C * (Real.log r) ^ 3 * (r : ℝ) ^ (-γ))
-- FROZEN-STATEMENT-END
:=
  Sandpile.Frozen.d4_ball_green_crossing Sandpile.External.planarRSW_holds
    ν₀ θ₀ K₀ ϑ hν₀ hθ₀ hϑ
