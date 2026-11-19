import Sandpile.Support.PlanarLaw
import LatticeProb.Bonanno.LQGMetric.Gaussian.AssociationSqrt

/-!
# Association inequalities for planar percolation

Positive association also applies to decreasing events. In particular, finitely many
increasing events satisfy the square-root bound used in crossing constructions.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Sandpile.External.RSW

/-- Decreasing events are positively correlated under an associated probability law. -/
theorem measureReal_mul_le_inter_of_lower (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsAssociatedPlanarLaw μ)
    {A B : Set (Site 2 → ℝ)} (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    μ.real A * μ.real B ≤ μ.real (A ∩ B) := by
  have hass := hμ Aᶜ Bᶜ hA.compl hB.compl hAm.compl hBm.compl
  rw [← compl_union, probReal_compl_eq_one_sub hAm, probReal_compl_eq_one_sub hBm,
    probReal_compl_eq_one_sub (hAm.union hBm)] at hass
  have hu := measureReal_union_add_inter (μ := μ) hBm (measure_ne_top μ A) (measure_ne_top μ B)
  nlinarith

/-- The product of the probabilities of finitely many decreasing events is at most the
probability of their intersection. -/
theorem prod_measureReal_le_biInter_of_lower (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsAssociatedPlanarLaw μ)
    {κ : Type*} (A : κ → Set (Site 2 → ℝ)) (hA : ∀ i, IsLowerSet (A i))
    (hAm : ∀ i, MeasurableSet (A i)) (s : Finset κ) :
    ∏ i ∈ s, μ.real (A i) ≤ μ.real (⋂ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.set_biInter_insert]
    have hm : MeasurableSet (⋂ j ∈ s, A j) := Finset.measurableSet_biInter s fun j _ => hAm j
    have hl : IsLowerSet (⋂ j ∈ s, A j) := isLowerSet_iInter₂ fun j _ => hA j
    exact (mul_le_mul_of_nonneg_left ih measureReal_nonneg).trans
      (measureReal_mul_le_inter_of_lower μ hμ (hA i) hl (hAm i) hm)

/-- The product of the probabilities of finitely many increasing events is at most the
probability of their intersection. -/
theorem prod_measureReal_le_biInter_of_upper (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsAssociatedPlanarLaw μ)
    {κ : Type*} (A : κ → Set (Site 2 → ℝ)) (hA : ∀ i, IsUpperSet (A i))
    (hAm : ∀ i, MeasurableSet (A i)) (s : Finset κ) :
    ∏ i ∈ s, μ.real (A i) ≤ μ.real (⋂ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.set_biInter_insert]
    have hm : MeasurableSet (⋂ j ∈ s, A j) := Finset.measurableSet_biInter s fun j _ => hAm j
    have hu : IsUpperSet (⋂ j ∈ s, A j) := isUpperSet_iInter₂ fun j _ => hA j
    exact (mul_le_mul_of_nonneg_left ih measureReal_nonneg).trans
      (hμ (A i) (⋂ j ∈ s, A j) (hA i) hu (hAm i) hm)

/-- Among finitely many increasing events, one has probability at least the square-root
bound in terms of the probability of their union. -/
theorem exists_measureReal_ge_sqrt_union (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsAssociatedPlanarLaw μ)
    {κ : Type*} [Fintype κ] [Nonempty κ] (A : κ → Set (Site 2 → ℝ))
    (hA : ∀ i, IsUpperSet (A i)) (hAm : ∀ i, MeasurableSet (A i)) :
    ∃ i, 1 - (1 - μ.real (⋃ i, A i)) ^ (1 / (Fintype.card κ : ℝ)) ≤ μ.real (A i) := by
  have hprod : ∏ i, μ.real (A i)ᶜ ≤ μ.real (⋂ i, (A i)ᶜ) := by
    simpa only [Finset.mem_univ, iInter_true] using
      prod_measureReal_le_biInter_of_lower μ hμ (fun i => (A i)ᶜ)
        (fun i => (hA i).compl) (fun i => (hAm i).compl) Finset.univ
  simpa only [compl_compl] using
    (LQGMetric.Pitt.sqrt_trick (P := μ) (A := fun i => (A i)ᶜ)
      (fun i => (hAm i).compl.nullMeasurableSet) hprod)

end Sandpile.External.RSW
