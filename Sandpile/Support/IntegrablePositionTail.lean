import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Integrable tails outside large balls

An integrable function has arbitrarily small integral outside a sufficiently
large ball in the image of a measurable random variable.
-/

open MeasureTheory Filter Topology

/-- The integral of the norm of an integrable function over the event that a
measurable random variable lies outside a large ball tends to zero. -/
theorem Sandpile.Support.tendsto_integral_norm_on_position_tail
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (Y : Ω → E) (hY : Measurable Y) (D : Ω → ℝ) (hD : Integrable D P) :
    Tendsto (fun n : ℕ => ∫ ω in {ω | (n : ℝ) < ‖Y ω‖}, ‖D ω‖ ∂P) atTop (𝓝 0) := by
  let A : ℕ → Set Ω := fun n => {ω | (n : ℝ) < ‖Y ω‖}
  have hAm : ∀ n, MeasurableSet (A n) := fun n => measurableSet_lt measurable_const hY.norm
  let F : ℕ → Ω → ℝ := fun n => (A n).indicator (fun ω => ‖D ω‖)
  have hlim : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 (∫ _ : Ω, (0 : ℝ) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun ω => ‖D ω‖)
    · intro n
      exact hD.norm.aestronglyMeasurable.indicator (hAm n)
    · exact hD.norm
    · intro n
      exact Eventually.of_forall fun ω => by
        by_cases hω : ω ∈ A n
        · simp only [F, Set.indicator_of_mem hω, norm_norm, le_refl]
        · simp only [F, Set.indicator_of_notMem hω, norm_zero, norm_nonneg]
    · exact Eventually.of_forall fun ω => by
        obtain ⟨n, hn⟩ := exists_nat_gt ‖Y ω‖
        have he : ∀ᶠ m : ℕ in atTop, F m ω = 0 := by
          filter_upwards [eventually_ge_atTop n] with m hnm
          have hω : ω ∉ A m := by
            change ¬(m : ℝ) < ‖Y ω‖
            exact not_lt_of_ge (le_trans hn.le (by exact_mod_cast hnm))
          exact Set.indicator_of_notMem hω _
        exact tendsto_const_nhds.congr' (he.mono fun n hn => hn.symm)
  simpa only [integral_zero, F, integral_indicator (hAm _)] using hlim
