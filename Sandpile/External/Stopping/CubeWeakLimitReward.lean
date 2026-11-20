import Sandpile.External.Stopping.CausalCubeJointLawReward
import Sandpile.External.Stopping.CubeWalkParameterizedClock

/-!
# Cube-killed rewards of weak walk-clock limits

A causal weak limit of killed walk-clock laws has reward bounded by the
Brownian cube-stopping value at unit horizon.
-/

open MeasureTheory ProbabilityTheory Set Filter unitInterval Topology
open scoped NNReal ENNReal ProbabilityTheory

namespace Sandpile.External.Stopping

/-- The reward of a causal weak limit of killed walk-clock laws is at most
the Brownian cube-stopping value. -/
theorem integral_causal_walk_clock_limit_le_brownian_cube
    {d : ℕ} [NeZero d] {ι : Type*} [Countable ι]
    (R : ℕ → ℝ) (q : ℕ → Site d) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (α : ℕ → (ℕ → Site d) → I) (hαm : ∀ n, Measurable (α n))
    (hkill : ∀ n, ∀ᵐ X ∂(walkLaw d (q n)), ∀ j : ℕ,
      (j : ℝ) < R n ^ 2 * (unitClock (α n) X : ℝ) → X j ∈ supBox (q n) (R n))
    (μn : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × I))
    (μ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × I))
    (hμn : ∀ n, (μn n : Measure _) = (walkLaw d (q n)).map
      (fun X => (centeredWalkPath (R n) (q n) X, α n X)))
    (hμ : Tendsto μn atTop (𝓝 μ))
    (hB : Continuum.IsBrownian d 0 (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
      (μ : Measure (C(ℝ≥0, Continuum.Space d) × I)).fst)
    (time : ι → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (hindep : ∀ i, Indep ((pathFutureSigma (d := d) (time i)).comap Prod.fst)
      (((pathPastSigma (d := d) (time i)).comap Prod.fst) ⊔
        MeasurableSpace.generateFrom {Prod.snd ⁻¹' Icc 0 (unitTime (time i))}) (μ : Measure (C(ℝ≥0, Continuum.Space d) × I)))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    (∫ p, G (1 - (unitClock id p.2 : ℝ)) (p.1 (unitClock id p.2)) ∂(μ : Measure (C(ℝ≥0, Continuum.Space d) × I))) ≤
      Continuum.brownianDiscountCube (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
        (μ : Measure (C(ℝ≥0, Continuum.Space d) × I)).fst (fun s z => -G s z) 1 1 0 := by
  have hunit : Continuous (unitClock (id : I → I)) := by
    change Continuous (fun u : I => (⟨(u : ℝ), u.2.1⟩ : ℝ≥0))
    exact continuous_subtype_val.subtype_mk _
  have hconstraint := ae_cube_constraint_of_parameterized_walk_clock_law_limit
    R q hRpos hR (unitClock (id : I → I)) hunit α hαm hkill μn μ hμn hμ
  exact integral_causal_joint_clock_reward_le_brownian_cube (μ : Measure (C(ℝ≥0, Continuum.Space d) × I)) hB time hdense
    hindep hconstraint G hGc M hG

end Sandpile.External.Stopping
