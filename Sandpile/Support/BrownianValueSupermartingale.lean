import Sandpile.Support.BrownianValueStoppedComparison
import Mathlib.Probability.Martingale.Basic

/-!
# The Brownian value supermartingale

The Brownian stopping-value process, frozen at the horizon, is a
supermartingale in the raw natural filtration.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

/-- A continuous adapted Brownian value process frozen at the horizon is a
supermartingale. -/
theorem Sandpile.Support.brownian_value_process_supermartingale
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
    (hMad : StronglyAdapted (LatticeProb.natFiltration (B x) (hBm x)) M)
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s))
    (hMfreeze : ∀ s ω, M s ω = M (min s T) ω) :
    Supermartingale M (LatticeProb.natFiltration (B x) (hBm x)) P := by
  let 𝓕 := LatticeProb.natFiltration (B x) (hBm x)
  obtain ⟨D, hDi, hD, hMint⟩ :=
    Sandpile.Support.exists_integrable_brownian_value_process_bound
      P B hB hBc hBm x T G hG hgrow M hMm hMc hMval
  have hMi : ∀ s, Integrable (M s) P := by
    intro s
    have hi := hMint (fun _ => min s T) measurable_const (fun _ => min_le_right _ _)
    have heq : M s = fun ω => M (min s T) ω := funext fun ω => hMfreeze s ω
    rwa [heq]
  have hneg : Submartingale (-M) 𝓕 P := by
    apply submartingale_of_setIntegral_le hMad.neg (fun s => (hMi s).neg)
    intro s t hst E hE
    by_cases hsT : s ≤ T
    · have htT : min t T ≤ T := min_le_right _ _
      have hst' : s ≤ min t T := le_min hst hsT
      have hσ : IsStoppingTime 𝓕 (fun _ : Ω => ((s : ℝ≥0) : ℝ≥0∞)) :=
        isStoppingTime_const 𝓕 s
      have hτ : IsStoppingTime 𝓕 (fun _ : Ω => ((min t T : ℝ≥0) : ℝ≥0∞)) :=
        isStoppingTime_const 𝓕 (min t T)
      have hEσ : MeasurableSet[hσ.measurableSpace] E :=
        (hσ.le_measurableSpace_of_const_le (fun _ => le_rfl)) _ hE
      have hh := Sandpile.Support.setIntegral_brownian_value_stopped_le
        P B hB hBc hBm x T G hG hgrow M hMval (fun _ => s) (fun _ => min t T)
        hσ hτ (fun _ => htT) E hEσ (fun _ _ => hst')
      have hh' : (∫ ω in E, M (min t T) ω ∂P) ≤ ∫ ω in E, M s ω ∂P := by
        rw [integral_sub (hMi (min t T)).integrableOn (hMi s).integrableOn] at hh
        linarith
      change (∫ ω in E, -M s ω ∂P) ≤ ∫ ω in E, -M t ω ∂P
      rw [integral_neg, integral_neg]
      have heq : M t = M (min t T) := funext fun ω => hMfreeze t ω
      rw [heq]
      linarith
    · have hTs : T ≤ s := le_of_not_ge hsT
      have hTt : T ≤ t := hTs.trans hst
      have heqs : M s = M T := funext fun ω => by simpa only [min_eq_right hTs] using hMfreeze s ω
      have heqt : M t = M T := funext fun ω => by simpa only [min_eq_right hTt] using hMfreeze t ω
      change (∫ ω in E, -M s ω ∂P) ≤ ∫ ω in E, -M t ω ∂P
      rw [heqs, heqt]
  simpa only [neg_neg] using hneg.neg
