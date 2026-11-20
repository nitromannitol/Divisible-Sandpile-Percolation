import Sandpile.External.ContinuumStoppingStabilityProved
import Sandpile.Support.MeanWithoutOptimalStopping

/-!
# Mean odometer growth below dimension four

Theorem 1.3(i)(a) holds without cited hypotheses: the continuum stopping
stability input is supplied by `Sandpile.External.continuumStoppingStability_holds`,
and the optimal-stopping input is not used.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Mean odometer growth below dimension four. -/
-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.mean_growth_le_three_proved
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 L)
-- FROZEN-STATEMENT-END
:=
  Sandpile.mean_growth_le_three_from_stability Sandpile.External.continuumStoppingStability_holds
    d hd hd3 ν hprob hmean hvar hvar' θ₀ hθ₀ hexp
