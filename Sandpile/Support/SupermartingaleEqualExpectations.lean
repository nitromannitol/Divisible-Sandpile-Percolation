import Mathlib.Probability.Martingale.Basic

/-!
# Supermartingales with constant expectations

An integrable supermartingale whose expectations are constant is a martingale.
-/

open MeasureTheory ProbabilityTheory

/-- A supermartingale with constant expectations is a martingale. -/
theorem Sandpile.Support.martingale_of_supermartingale_integral_eq
    {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι] (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ι (inferInstance : MeasurableSpace Ω)) (M : ι → Ω → ℝ)
    (hM : Supermartingale M 𝓕 P) (v : ℝ) (hmean : ∀ i, (∫ ω, M i ω ∂P) = v) :
    Martingale M 𝓕 P := by
  refine ⟨hM.stronglyAdapted, fun i j hij => ?_⟩
  apply (integral_eq_iff_of_ae_le integrable_condExp (hM.integrable i) (hM.condExp_ae_le hij)).1
  rw [integral_condExp (𝓕.le i), hmean j, hmean i]
