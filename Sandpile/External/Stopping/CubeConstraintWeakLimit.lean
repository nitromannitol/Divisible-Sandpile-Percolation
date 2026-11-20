import Sandpile.External.Stopping.CubeStoppedPathLimit
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Cube constraints under weak convergence

The condition that a continuous path stays in a closed cube strictly before a
specified time is closed in path-time space. It therefore passes to weak limits,
even when the approximating cube widths approach the limiting width.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Continuous paths which stay in a cube strictly before the marked time. -/
def cubeConstrainedPaths {d : ℕ} (L : ℝ) : Set (C(ℝ≥0, Continuum.Space d) × ℝ≥0) :=
  {p | ∀ t < p.2, ∀ i, |p.1 t i| ≤ L}

/-- The pre-stop closed-cube constraint is closed in path-time space. -/
theorem isClosed_cubeConstrainedPaths {d : ℕ} (L : ℝ) :
    IsClosed (cubeConstrainedPaths (d := d) L) := by
  have heq : cubeConstrainedPaths (d := d) L =
      ⋂ t : ℝ≥0, ⋂ i : Fin d, {p : C(ℝ≥0, Continuum.Space d) × ℝ≥0 |
        p.2 ≤ t ∨ |p.1 t i| ≤ L} := by
    ext p
    simp only [cubeConstrainedPaths, mem_setOf_eq, mem_iInter]
    constructor
    · intro h t i
      by_cases ht : t < p.2
      · exact Or.inr (h t ht i)
      · exact Or.inl (le_of_not_gt ht)
    · intro h t ht i
      exact (h t i).resolve_left (not_le_of_gt ht)
  rw [heq]
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro i
  apply IsClosed.union
  · exact isClosed_le (NNReal.continuous_coe.comp continuous_snd) continuous_const
  · exact isClosed_le (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp
      ((continuous_eval_const t).comp continuous_fst)).abs) continuous_const

/-- Eventual full mass on a closed set passes to a weak limit of probability
measures. -/
theorem ae_mem_closed_of_tendsto_probabilityMeasure
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    (μn : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (hμ : Tendsto μn atTop (𝓝 μ)) (S : Set E) (hS : IsClosed S)
    (hfull : ∀ᶠ n in atTop, ∀ᵐ x ∂(μn n : Measure E), x ∈ S) :
    ∀ᵐ x ∂(μ : Measure E), x ∈ S := by
  have hmass : ∀ᶠ n in atTop, (μn n : Measure E) S = 1 := by
    filter_upwards [hfull] with n hn
    exact (prob_compl_eq_zero_iff (μ := (μn n : Measure E)) hS.measurableSet).mp (ae_iff.mp hn)
  have hlimsup : limsup (fun n => (μn n : Measure E) S) atTop = (1 : ℝ≥0∞) := by
    rw [Filter.limsup_congr hmass, limsup_const]
  have hle : (1 : ℝ≥0∞) ≤ (μ : Measure E) S := by
    have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hS
    rwa [hlimsup] at h
  have heq : (μ : Measure E) S = 1 := le_antisymm (by simpa only [measure_univ] using measure_mono (μ := (μ : Measure E)) (subset_univ S)) hle
  exact ae_iff.mpr ((prob_compl_eq_zero_iff (μ := (μ : Measure E)) hS.measurableSet).mpr heq)

/-- If pre-stop cube constraints hold in cubes of every larger width
asymptotically, they hold at the limiting width under weak convergence. -/
theorem ae_cube_constraint_of_tendsto_probabilityMeasure
    {d : ℕ} (μn : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0))
    (μ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0))
    (hμ : Tendsto μn atTop (𝓝 μ)) (L : ℝ)
    (hfull : ∀ ε > 0, ∀ᶠ n in atTop, ∀ᵐ p ∂(μn n : Measure _),
      p ∈ cubeConstrainedPaths (d := d) (L + ε)) :
    ∀ᵐ p ∂(μ : Measure _), p ∈ cubeConstrainedPaths (d := d) L := by
  have hall : ∀ k : ℕ, ∀ᵐ p ∂(μ : Measure _),
      p ∈ cubeConstrainedPaths (d := d) (L + 1 / ((k : ℝ) + 1)) := by
    intro k
    apply ae_mem_closed_of_tendsto_probabilityMeasure μn μ hμ _ (isClosed_cubeConstrainedPaths _)
    exact hfull _ (by positivity)
  filter_upwards [ae_all_iff.mpr hall] with p hp
  intro t ht i
  have hlim : Tendsto (fun k : ℕ => L + 1 / ((k : ℝ) + 1)) atTop (𝓝 L) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := L)).add tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun k => hp k t ht i)

end Sandpile.External.Stopping
