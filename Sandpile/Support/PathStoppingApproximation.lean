import Sandpile.Support.PathStoppingFunctional

/-!
# Approximating stopping rules on path space

A bounded Brownian stopping time can be approximated almost surely by bounded
raw stopping functionals on the full path space. These functionals remain raw
stopping rules when read along any other process.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

/-- A raw stopping functional on path space remains a raw stopping rule when
read along any process. -/
theorem Sandpile.Support.isBrownianStopping_path_comp
    {Ω : Type*} {d : ℕ} (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (θ : (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0)
    (hθ : IsStoppingTime (LatticeProb.natFiltration
      (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
      (fun t => (measurable_pi_apply t).stronglyMeasurable))
      (fun p => (θ p : ℝ≥0∞))) :
    Sandpile.Continuum.IsBrownianStopping B (fun ω => θ (fun t => B t ω)) := by
  intro t
  have hθt := hθ t
  rw [LatticeProb.natFiltration_eq_comap] at hθt
  obtain ⟨S, hS, he⟩ := hθt
  rw [Sandpile.Continuum.brownianFiltration, Filtration.natural_eq_comap]
  refine ⟨S, hS, ?_⟩
  ext ω
  exact Set.ext_iff.mp he (fun t => B t ω)

/-- A bounded Brownian stopping time is the almost-sure limit of a sequence of
bounded raw stopping functionals on path space. -/
theorem Sandpile.Support.exists_raw_path_stoppingTime_seq
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hBm : ∀ t, StronglyMeasurable (B t))
    (τ : Ω → ℝ≥0) (hτ : Sandpile.Continuum.IsBrownianStopping B τ)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    ∃ θ : ℕ → (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0,
      (∀ n, IsStoppingTime (LatticeProb.natFiltration
        (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
        (fun t => (measurable_pi_apply t).stronglyMeasurable))
        (fun p => (θ n p : ℝ≥0∞))) ∧
      (∀ n p, θ n p ≤ T) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => θ n (fun t => B t ω)) atTop (𝓝 (τ ω)) := by
  obtain ⟨θ, hθ, hθT, hθeq⟩ :=
    Sandpile.Support.exists_path_stoppingTime_of_brownianStopping P B hBm τ hτ T hτT
  obtain ⟨σ, hσ, hσT, hσlim⟩ :=
    Sandpile.Support.exists_stoppingTime_seq_tendsto_of_rightCont
      (LatticeProb.natFiltration
        (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
        (fun t => (measurable_pi_apply t).stronglyMeasurable)) θ hθ T hθT
  refine ⟨σ, hσ, hσT, ?_⟩
  filter_upwards [hθeq] with ω hω
  simpa only [hω] using hσlim (fun t => B t ω)
