import Sandpile.Support.BrownianValueProcess

/-!
# Adapted Brownian value processes

The value process frozen at the horizon is strongly adapted to the raw
Brownian natural filtration.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- A continuous Markovian value function yields a strongly adapted value
process when frozen at the horizon. -/
theorem Sandpile.Support.stronglyAdapted_value_process_of_continuous
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (x : Sandpile.Continuum.Space d) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hV : ContinuousOn (fun p : ℝ≥0 × Sandpile.Continuum.Space d =>
      Sandpile.External.Snell.snellValue (B p.2) P G ((T : ℝ) - p.1))
      (Set.Icc 0 T ×ˢ Set.univ))
    (M : ℝ≥0 → Ω → ℝ) (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s)) :
    StronglyAdapted (Sandpile.Continuum.brownianFiltration (B x))
      (fun s ω => M (min s T) ω) := by
  intro s
  let r := min s T
  have hrT : r ≤ T := min_le_right _ _
  have hrs : r ≤ s := min_le_left _ _
  have hVcont : Continuous (fun y =>
      Sandpile.External.Snell.snellValue (B y) P G ((T : ℝ) - r)) := by
    change Continuous ((fun p : ℝ≥0 × Sandpile.Continuum.Space d =>
      Sandpile.External.Snell.snellValue (B p.2) P G ((T : ℝ) - p.1)) ∘ fun y => (r, y))
    apply hV.comp_continuous
    · exact continuous_const.prodMk continuous_id
    · intro y
      exact ⟨⟨zero_le, hrT⟩, Set.mem_univ _⟩
  have hBad : StronglyMeasurable[Sandpile.Continuum.brownianFiltration (B x) r] (B x r) :=
    (Sandpile.Continuum.measurable_brownianFiltration (B x) r r le_rfl).stronglyMeasurable
  have hmeas : StronglyMeasurable[Sandpile.Continuum.brownianFiltration (B x) r]
      (fun ω => Sandpile.External.Snell.snellValue (B (B x r ω)) P G ((T : ℝ) - r)) :=
    hVcont.comp_stronglyMeasurable hBad
  have hmeas' := hmeas.mono ((Sandpile.Continuum.brownianFiltration (B x)).mono hrs)
  have heq : (fun ω => M (min s T) ω) =
      fun ω => Sandpile.External.Snell.snellValue (B (B x r ω)) P G ((T : ℝ) - r) :=
    funext (hMval r hrT)
  change StronglyMeasurable[Sandpile.Continuum.brownianFiltration (B x) s]
    (fun ω => M (min s T) ω)
  rw [heq]
  exact hmeas'

/-- The Brownian value process frozen at its horizon is strongly adapted to
the raw natural filtration. -/
theorem Sandpile.Support.stronglyAdapted_brownian_value_process
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
    (M : ℝ≥0 → Ω → ℝ) (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s)) :
    StronglyAdapted (Sandpile.Continuum.brownianFiltration (B x))
      (fun s ω => M (min s T) ω) := by
  exact Sandpile.Support.stronglyAdapted_value_process_of_continuous P B x T G
    (Sandpile.Support.continuousOn_brownian_snellValue P B hB hBm hBc T G hG hgrow) M hMval
