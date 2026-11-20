import Sandpile.External.Stopping.CubeInterpolationConstraint

/-!
# Cube constraints for weak limits of walk-clock laws

Joint weak limits of centered walk paths and killed step-walk stops retain the
closed unit-cube constraint before the limiting stop.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Joint weak limits of killed walk-clock laws satisfy the Brownian cube
constraint before the limiting clock. -/
theorem ae_cube_constraint_of_walk_clock_law_limit
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (θ : ℕ → (ℕ → Site d) → ℝ≥0) (hθm : ∀ n, Measurable (θ n))
    (hkill : ∀ n, ∀ᵐ X ∂(walkLaw d (q n)), ∀ j : ℕ,
      (j : ℝ) < R n ^ 2 * (θ n X : ℝ) → X j ∈ supBox (q n) (R n))
    (μn : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0))
    (μ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0))
    (hμn : ∀ n, (μn n : Measure _) = (walkLaw d (q n)).map
      (fun X => (centeredWalkPath (R n) (q n) X, θ n X)))
    (hμ : Tendsto μn atTop (𝓝 μ)) :
    ∀ᵐ p ∂(μ : Measure _), p ∈ cubeConstrainedPaths (d := d) 1 := by
  apply ae_cube_constraint_of_tendsto_probabilityMeasure μn μ hμ 1
  intro ε hε
  have hinv : Tendsto (fun n => 1 / R n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hR
  filter_upwards [hinv.eventually (Iio_mem_nhds hε)] with n hn
  rw [hμn n]
  change ∀ᵐ p ∂(walkLaw d (q n)).map (fun X => (centeredWalkPath (R n) (q n) X, θ n X)),
    ∀ t < p.2, ∀ i, |p.1 t i| ≤ 1 + ε
  rw [ae_map_iff
    (((measurable_centeredWalkPath (R n) (q n)).prodMk (hθm n)).aemeasurable)
    (isClosed_cubeConstrainedPaths (d := d) (1 + ε)).measurableSet]
  filter_upwards [ae_centeredWalkPath_cube_constraint (hRpos n) (q n) (θ n) (hkill n)] with X hX
  intro t ht i
  exact (hX t ht i).trans (by linarith)

end Sandpile.External.Stopping
