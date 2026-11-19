import Sandpile.External.RSW.Association

/-!
# Probability bound for a quasi-crossing cascade

If the intersection of two increasing events is covered by two increasing events, positive
association bounds the product of the first two probabilities using the complements of the
covering events. This form remains meaningful when either probability vanishes.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A division-free bound for two increasing events whose intersection is covered by two other
increasing events. -/
theorem measureReal_mul_le_one_sub_mul_of_inter_subset_union
    (μ : Measure (Site 2 → ℝ)) [IsProbabilityMeasure μ] (hμ : IsAssociatedPlanarLaw μ)
    {E L A B : Set (Site 2 → ℝ)}
    (hE : IsUpperSet E) (hL : IsUpperSet L) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hEm : MeasurableSet E) (hLm : MeasurableSet L)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hsub : E ∩ L ⊆ A ∪ B) :
    μ.real E * μ.real L ≤ 1 - (1 - μ.real A) * (1 - μ.real B) := by
  have hEL := hμ E L hE hL hEm hLm
  have hmono := measureReal_mono (μ := μ) hsub (measure_ne_top μ (A ∪ B))
  have hcompl := measureReal_mul_le_inter_of_lower μ hμ hA.compl hB.compl hAm.compl hBm.compl
  rw [← compl_union, probReal_compl_eq_one_sub hAm, probReal_compl_eq_one_sub hBm,
    probReal_compl_eq_one_sub (hAm.union hBm)] at hcompl
  linarith

/-- The cascade bound when the two covering events have the same probability. -/
theorem measureReal_mul_le_one_sub_sq_of_inter_subset_union
    (μ : Measure (Site 2 → ℝ)) [IsProbabilityMeasure μ] (hμ : IsAssociatedPlanarLaw μ)
    {E L A B : Set (Site 2 → ℝ)}
    (hE : IsUpperSet E) (hL : IsUpperSet L) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hEm : MeasurableSet E) (hLm : MeasurableSet L)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hsub : E ∩ L ⊆ A ∪ B)
    (heq : μ.real A = μ.real B) :
    μ.real E * μ.real L ≤ 1 - (1 - μ.real A) ^ 2 := by
  have h := measureReal_mul_le_one_sub_mul_of_inter_subset_union μ hμ
    hE hL hA hB hEm hLm hAm hBm hsub
  rw [← heq] at h
  nlinarith

/-- The division-free probability implication in the quasi-crossing cascade. If the
first covering event has probability below `δ`, the second one has probability at least
`δ`; the second inclusion then gives the bridge bound. -/
theorem cascade_probability_bound
    (μ : Measure (Site 2 → ℝ)) [IsProbabilityMeasure μ] (hμ : IsAssociatedPlanarLaw μ)
    {T C E L A B : Set (Site 2 → ℝ)}
    (hC : IsUpperSet C) (hE : IsUpperSet E) (hL : IsUpperSet L)
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hCm : MeasurableSet C) (hEm : MeasurableSet E) (hLm : MeasurableSet L)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hcover : T ⊆ C ∪ E) (hbridge : E ∩ L ⊆ A ∪ B) (heq : μ.real A = μ.real B)
    {δ : ℝ} (hδ : δ ≤ 1) (hCsmall : μ.real C < δ)
    (hTlarge : 1 - (1 - δ) ^ 2 ≤ μ.real T) :
    δ * μ.real L ≤ 1 - (1 - μ.real A) ^ 2 := by
  have hcompl := measureReal_mul_le_inter_of_lower μ hμ hC.compl hE.compl hCm.compl hEm.compl
  rw [← compl_union, probReal_compl_eq_one_sub hCm, probReal_compl_eq_one_sub hEm,
    probReal_compl_eq_one_sub (hCm.union hEm)] at hcompl
  have hcoverprob := measureReal_mono (μ := μ) hcover (measure_ne_top μ (C ∪ E))
  have hElarge : δ ≤ μ.real E := by
    by_contra! hEsmall
    have hp : 0 < (δ - μ.real C) * (δ - μ.real E) :=
      mul_pos (by linarith) (by linarith)
    have hn : 0 ≤ (1 - δ) * ((δ - μ.real C) + (δ - μ.real E)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hbridgeprob := measureReal_mul_le_one_sub_sq_of_inter_subset_union μ hμ
    hE hL hA hB hEm hLm hAm hBm hbridge heq
  exact (mul_le_mul_of_nonneg_right hElarge measureReal_nonneg).trans hbridgeprob

end Sandpile.External.RSW
