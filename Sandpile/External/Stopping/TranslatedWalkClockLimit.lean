import Sandpile.External.Stopping.TranslatedWalkConstraint

/-!
# Translated cube constraints for weak walk-clock limits

Weak limits of killed walk-clock laws preserve the cube constraint around the
limit of their rescaled lattice centers.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A weak limit of killed uncentered walk-clock laws remains in the limiting
unit cube strictly before the decoded stopping time. -/
theorem ae_translated_cube_constraint_of_walk_clock_law_limit
    {d : ℕ} [NeZero d] {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (R : ℕ → ℝ) (q : ℕ → Site d) (hRpos : ∀ n, 0 < R n)
    (hR : Tendsto R atTop atTop) (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    (θ : A → ℝ≥0) (hθ : Continuous θ)
    (α : ℕ → (ℕ → Site d) → A) (hαm : ∀ n, Measurable (α n))
    (hkill : ∀ n, ∀ᵐ X ∂(walkLaw d (q n)), ∀ j : ℕ,
      (j : ℝ) < R n ^ 2 * (θ (α n X) : ℝ) → X j ∈ supBox (q n) (R n))
    (μn : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × A))
    (μ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × A))
    (hμn : ∀ n, (μn n : Measure _) = (walkLaw d (q n)).map
      (fun X => (diffusiveWalkPath (R n) X, α n X)))
    (hμ : Tendsto μn atTop (𝓝 μ)) :
    ∀ᵐ p ∂(μ : Measure (C(ℝ≥0, Continuum.Space d) × A)),
      (p.1, θ p.2) ∈ translatedCubeConstrainedPaths a 1 := by
  let F : C(ℝ≥0, Continuum.Space d) × A → C(ℝ≥0, Continuum.Space d) × ℝ≥0 :=
    fun p => (p.1, θ p.2)
  have hF : Continuous F := continuous_fst.prodMk (hθ.comp continuous_snd)
  let νn : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0) := fun n => (μn n).map F
  let ν : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0) := μ.map F
  have hν : Tendsto νn atTop (𝓝 ν) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μn μ hμ hF
  have hνn (n : ℕ) : (νn n : Measure _) = (walkLaw d (q n)).map
      (fun X => (diffusiveWalkPath (R n) X, θ (α n X))) := by
    change (μn n : Measure _).map F = _
    rw [hμn n, Measure.map_map hF.measurable
      ((measurable_diffusiveWalkPath (R n)).prodMk (hαm n))]
    rfl
  have hinv : Tendsto (fun n => 1 / R n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hR
  have hcenter : Tendsto (fun n => ‖Lclt.scaledSite (R n) (q n) - a‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hstart.sub (tendsto_const_nhds (x := a))).norm
  have herr : Tendsto (fun n => 1 / R n + ‖Lclt.scaledSite (R n) (q n) - a‖) atTop (𝓝 0) := by
    simpa only [zero_add] using hinv.add hcenter
  have hbound : ∀ᵐ p ∂(ν : Measure _), p ∈ translatedCubeConstrainedPaths a 1 := by
    apply ae_translated_cube_constraint_of_tendsto_probabilityMeasure νn ν hν a 1
    intro ε hε
    filter_upwards [herr.eventually (Iio_mem_nhds hε)] with n hn
    rw [hνn n]
    change ∀ᵐ p ∂(walkLaw d (q n)).map (fun X => (diffusiveWalkPath (R n) X, θ (α n X))),
      ∀ t < p.2, ∀ i, |p.1 t i - a i| ≤ 1 + ε
    have hm : Measurable (fun X => (diffusiveWalkPath (R n) X, θ (α n X))) :=
      (measurable_diffusiveWalkPath (R n)).prodMk (hθ.measurable.comp (hαm n))
    rw [ae_map_iff hm.aemeasurable
      (isClosed_translatedCubeConstrainedPaths a (1 + ε)).measurableSet]
    filter_upwards [ae_diffusiveWalkPath_translated_cube_constraint (hRpos n) (q n) a
      (fun X => θ (α n X)) (hkill n)] with X hX
    intro t ht i
    exact (hX t ht i).trans (by linarith)
  exact ae_of_ae_map hF.measurable.aemeasurable hbound

end Sandpile.External.Stopping
