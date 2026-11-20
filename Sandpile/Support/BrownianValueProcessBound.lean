import Sandpile.Support.BrownianValueGrowth
import Sandpile.Support.BrownianValueProcess
import Sandpile.Support.StopMeasurable

/-!
# Integrable bounds for the Brownian value process

Polynomial growth of the Brownian stopping value gives an integrable bound
uniformly over the finite horizon and hence integrability at bounded stops.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- A continuous Brownian value process has an integrable pathwise bound and
is integrable at every bounded measurable random time. -/
theorem Sandpile.Support.exists_integrable_brownian_value_process_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t))
    (x : Sandpile.Continuum.Space d) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (M : ℝ≥0 → Ω → ℝ) (hMm : ∀ s, Measurable (M s))
    (hMc : ∀ ω, Continuous fun s => M s ω)
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s)) :
    ∃ D : Ω → ℝ, Integrable D P ∧
      (∀ᵐ ω ∂P, ∀ s ≤ T, ‖M s ω‖ ≤ D ω) ∧
      ∀ σ : Ω → ℝ≥0, Measurable σ → (∀ ω, σ ω ≤ T) →
        Integrable (fun ω => M (σ ω) ω) P := by
  obtain ⟨C, hC, n, hVgrowth⟩ :=
    Sandpile.Support.exists_brownian_snellValue_growth_bound P B hB hBm hBc T G hG hgrow
  let H : ℝ → Sandpile.Continuum.Space d → ℝ := fun r y =>
    Sandpile.External.Snell.snellValue (B y) P G r
  have hHgrow : ∃ C k : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |H r y| ≤ C * (1 + ‖y‖) ^ k := by
    refine ⟨C, n, ?_⟩
    intro r hr y
    have hrT : r.toNNReal ≤ T := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal r hr.1]
      exact hr.2
    have hh := hVgrowth r.toNNReal hrT y
    rw [Real.coe_toNNReal r hr.1] at hh
    simpa only [H, Real.rpow_natCast] using hh
  obtain ⟨D, hDi, hD⟩ := Sandpile.Support.exists_integrable_brownian_reward_uniform_bound
    x P (B x) (hB x) (hBm x) (hBc x) T H hHgrow
  have hMbound : ∀ᵐ ω ∂P, ∀ s ≤ T, ‖M s ω‖ ≤ D ω := by
    filter_upwards [hD] with ω hω s hs
    rw [hMval s hs ω]
    apply hω ((T : ℝ) - s) ⟨?_, ?_⟩ s hs
    · exact sub_nonneg.mpr (by exact_mod_cast hs)
    · exact sub_le_self _ s.coe_nonneg
  refine ⟨D, hDi, hMbound, ?_⟩
  intro σ hσm hσT
  have hst : Measurable (fun ω => M (σ ω) ω) :=
    (measurable_uncurry_of_continuous_of_measurable hMc hMm).comp (hσm.prodMk measurable_id)
  apply hDi.mono' hst.stronglyMeasurable.aestronglyMeasurable
  filter_upwards [hMbound] with ω hω
  exact hω (σ ω) (hσT ω)

/-- The Brownian value process starts almost surely at the deterministic
stopping value. -/
theorem Sandpile.Support.brownian_value_process_zero_ae
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (x : Sandpile.Continuum.Space d) (hB : Sandpile.Continuum.IsBrownian d x (B x) P)
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ) (M : ℝ≥0 → Ω → ℝ)
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s)) :
    M 0 =ᵐ[P] fun _ => Sandpile.External.Snell.snellValue (B x) P G T := by
  filter_upwards [hB.start] with ω hω
  simpa only [NNReal.coe_zero, sub_zero, hω] using hMval 0 zero_le ω

/-- The expectation of the initial value process equals the deterministic
stopping value. -/
theorem Sandpile.Support.integral_brownian_value_process_zero
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (x : Sandpile.Continuum.Space d) (hB : Sandpile.Continuum.IsBrownian d x (B x) P)
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ) (M : ℝ≥0 → Ω → ℝ)
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s)) :
    (∫ ω, M 0 ω ∂P) = Sandpile.External.Snell.snellValue (B x) P G T := by
  rw [integral_congr_ae (Sandpile.Support.brownian_value_process_zero_ae P B x hB T G M hMval)]
  simp
