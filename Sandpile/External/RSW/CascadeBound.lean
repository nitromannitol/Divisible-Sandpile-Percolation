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

end Sandpile.External.RSW
