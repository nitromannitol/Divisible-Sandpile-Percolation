import Sandpile.External.Stopping.TranslatedCubeJointLawHorizon
import Sandpile.External.Stopping.TranslatedWalkClockLimit
import Sandpile.External.Stopping.WalkClockStoppingLimit

/-!
# Cube rewards of weak walk-clock limits

A weak limit of killed walk-clock laws admits a randomized stopping
representation and has reward bounded by the Brownian cube-stopping value.
-/

open MeasureTheory ProbabilityTheory Set Filter unitInterval Topology
open scoped NNReal ENNReal ProbabilityTheory

namespace Sandpile.External.Stopping

/-- A weak limit of killed lattice walk-clock laws with Brownian path marginal
and an almost-sure horizon bound has reward at most the cube-stopping value. -/
theorem integral_walk_clock_limit_le_translated_brownian_cube
    {d : ℕ} [NeZero d] {ι : Type*} [Countable ι]
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (q : ℕ → Site d) (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    (τ : ℕ → (ℕ → Site d) → ℕ) (hτ : ∀ n, IsWalkStopping (τ n))
    (hτm : ∀ n, Measurable (τ n))
    (hkill : ∀ n, ∀ᵐ X ∂(walkLaw d (q n)), ∀ j < τ n X, X j ∈ supBox (q n) (R n))
    (θ : ℕ → (ℕ → Site d) → I) (hθ : ∀ n, Measurable (θ n))
    (c : ℝ≥0) (hc : 0 < c)
    (hdecode : ∀ n X, c * unitClock id (θ n X) = diffusiveLatticeClock (R n) (τ n X))
    (μn : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × I))
    (μ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × I))
    (hμn : ∀ n, (μn n : Measure _) = (walkLaw d (q n)).map
      (fun X => (diffusiveWalkPath (R n) X, θ n X)))
    (hμ : Tendsto μn atTop (𝓝 μ)) (T : ℝ≥0)
    (hclockT : ∀ᵐ p ∂(μ : Measure (C(ℝ≥0, Continuum.Space d) × I)),
      c * unitClock id p.2 ≤ T)
    (hB : Continuum.IsBrownian d a (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
      (μ : Measure (C(ℝ≥0, Continuum.Space d) × I)).fst)
    (time : ι → ℝ≥0) (hdense : ∀ u v : ℝ≥0, u < v → ∃ i, u < time i ∧ time i < v)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    (∫ p, G ((T : ℝ) - ((c * unitClock id p.2 : ℝ≥0) : ℝ))
      (p.1 (c * unitClock id p.2)) ∂(μ : Measure (C(ℝ≥0, Continuum.Space d) × I))) ≤
      Continuum.brownianDiscountCube (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
        (μ : Measure (C(ℝ≥0, Continuum.Space d) × I)).fst (fun s z => -G s z) T 1 a := by
  let clock : I → ℝ≥0 := fun z => c * unitClock id z
  have hclock : Continuous clock := continuous_const.mul continuous_unitClock
  have hkill' : ∀ n, ∀ᵐ X ∂(walkLaw d (q n)), ∀ j : ℕ,
      (j : ℝ) < R n ^ 2 * (clock (θ n X) : ℝ) → X j ∈ supBox (q n) (R n) := by
    intro n
    filter_upwards [hkill n] with X hX
    intro j hj
    have heq : R n ^ 2 * (clock (θ n X) : ℝ) = (τ n X : ℝ) := by
      rw [show clock (θ n X) = diffusiveLatticeClock (R n) (τ n X) from hdecode n X]
      change R n ^ 2 * ((τ n X : ℝ) / R n ^ 2) = (τ n X : ℝ)
      exact mul_div_cancel₀ _ (pow_ne_zero 2 (hRpos n).ne')
    rw [heq] at hj
    exact hX j (by exact_mod_cast hj)
  have hconstraint := ae_translated_cube_constraint_of_walk_clock_law_limit R q hRpos hR a hstart
    clock hclock θ hθ hkill' μn μ hμn hμ
  obtain ⟨sigma, hsigma, _, hmap⟩ := exists_stopping_version_of_walk_clock_limit
    R hR q τ hτ hτm θ hθ c hc hdecode μn μ hμn hμ time hdense
  exact integral_joint_clock_reward_le_translated_brownian_cube_of_ae_le
    (μ : Measure (C(ℝ≥0, Continuum.Space d) × I)) a clock hclock.measurable T hB
    G hGc M hG sigma hsigma hmap hclockT hconstraint

end Sandpile.External.Stopping
