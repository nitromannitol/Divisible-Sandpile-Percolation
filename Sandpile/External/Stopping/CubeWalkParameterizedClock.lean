import Sandpile.External.Stopping.CubeWalkJointLawLimit

/-!
# Cube constraints for parameterized clock laws

A continuous parameterization of the clock preserves the cube constraint in
weak limits of killed walk-clock laws.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Weak limits of killed walk laws retain the cube constraint when the clock
is read through a continuous parameterization. -/
theorem ae_cube_constraint_of_parameterized_walk_clock_law_limit
    {d : ℕ} [NeZero d] {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (R : ℕ → ℝ) (q : ℕ → Site d) (hRpos : ∀ n, 0 < R n)
    (hR : Tendsto R atTop atTop) (θ : A → ℝ≥0) (hθ : Continuous θ)
    (α : ℕ → (ℕ → Site d) → A) (hαm : ∀ n, Measurable (α n))
    (hkill : ∀ n, ∀ᵐ X ∂(walkLaw d (q n)), ∀ j : ℕ,
      (j : ℝ) < R n ^ 2 * (θ (α n X) : ℝ) → X j ∈ supBox (q n) (R n))
    (μn : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × A))
    (μ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × A))
    (hμn : ∀ n, (μn n : Measure _) = (walkLaw d (q n)).map
      (fun X => (centeredWalkPath (R n) (q n) X, α n X)))
    (hμ : Tendsto μn atTop (𝓝 μ)) :
    ∀ᵐ p ∂(μ : Measure (C(ℝ≥0, Continuum.Space d) × A)), (p.1, θ p.2) ∈ cubeConstrainedPaths (d := d) 1 := by
  let F : C(ℝ≥0, Continuum.Space d) × A → C(ℝ≥0, Continuum.Space d) × ℝ≥0 :=
    fun p => (p.1, θ p.2)
  have hF : Continuous F := continuous_fst.prodMk (hθ.comp continuous_snd)
  let νn : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0) :=
    fun n => (μn n).map F
  let ν : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0) := μ.map F
  have hν : Tendsto νn atTop (𝓝 ν) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μn μ hμ hF
  have hνn (n : ℕ) : (νn n : Measure _) = (walkLaw d (q n)).map
      (fun X => (centeredWalkPath (R n) (q n) X, θ (α n X))) := by
    change (μn n : Measure _).map F = _
    rw [hμn n, Measure.map_map hF.measurable
      ((measurable_centeredWalkPath (R n) (q n)).prodMk (hαm n))]
    rfl
  have hbound := ae_cube_constraint_of_walk_clock_law_limit R q hRpos hR
    (fun n X => θ (α n X)) (fun n => hθ.measurable.comp (hαm n)) hkill νn ν hνn hν
  exact ae_of_ae_map hF.measurable.aemeasurable hbound

end Sandpile.External.Stopping
