import Sandpile.External.Stopping.CubeJointLawReward

/-!
# Cube-killed rewards of causal joint laws

Independent future increments imply that a joint path-clock law admits a
randomized stopping representation, and the cube constraint bounds its reward.
-/

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped NNReal ENNReal ProbabilityTheory

namespace Sandpile.External.Stopping

/-- A causal unit-clock joint law satisfying the cube constraint has reward at
most the Brownian cube-stopping value. -/
theorem integral_causal_joint_clock_reward_le_brownian_cube
    {d : ℕ} [NeZero d] {ι : Type*} [Countable ι]
    (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I)) [IsProbabilityMeasure ρ]
    (hB : Continuum.IsBrownian d 0 (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t) ρ.fst)
    (time : ι → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (hindep : ∀ i, Indep ((pathFutureSigma (d := d) (time i)).comap Prod.fst)
      (((pathPastSigma (d := d) (time i)).comap Prod.fst) ⊔
        MeasurableSpace.generateFrom {Prod.snd ⁻¹' Icc 0 (unitTime (time i))}) ρ)
    (hkill : ∀ᵐ p ∂ρ, (p.1, unitClock id p.2) ∈ cubeConstrainedPaths (d := d) 1)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    (∫ p, G (1 - (unitClock id p.2 : ℝ)) (p.1 (unitClock id p.2)) ∂ρ) ≤
      Continuum.brownianDiscountCube (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
        ρ.fst (fun s z => -G s z) 1 1 0 := by
  obtain ⟨τ, hτ, hτ1, hmap⟩ :=
    exists_path_stopping_version_of_independent_future ρ time hdense hindep
  exact integral_joint_clock_reward_le_brownian_cube ρ hB G hGc M hG τ hτ hτ1 hmap hkill

end Sandpile.External.Stopping
