import Sandpile.External.RSW.UnorientedCascadeCover
import Sandpile.External.RSW.QuasiCascadeProbability

/-!
# The unoriented quasi-crossing cascade

Positive association gives the cascade estimate when exceptional paths have no
smaller subpath in either direction.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The division-free cascade estimate with unoriented exceptional paths. -/
theorem kstUnorientedQuasiCascade_probability (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (n m k : ℕ) {A B : Set (Sym2 (Site 2) → Bool)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hbridge : kstUnorientedExceptionalPathEvent n m k ∩ kstQuasiCrossingEvent m k ⊆ A ∪ B)
    (heq : μ.real A = μ.real B) {δ : ℝ} (hδ : δ ≤ 1)
    (hsmall : μ.real (kstQuasiCrossingEvent n k) < δ)
    (hlarge : 1 - (1 - δ) ^ 2 ≤ μ.real (kstQuasiCrossingEvent n m)) :
    δ * μ.real (kstQuasiCrossingEvent m k) ≤ 1 - (1 - μ.real A) ^ 2 := by
  let C := kstQuasiCrossingEvent n k
  let E := kstUnorientedExceptionalPathEvent n m k
  let L := kstQuasiCrossingEvent m k
  have hC : IsUpperSet C := isUpperSet_kstQuasiCrossingEvent n k
  have hE : IsUpperSet E := isUpperSet_kstUnorientedExceptionalPathEvent n m k
  have hL : IsUpperSet L := isUpperSet_kstQuasiCrossingEvent m k
  have hCm : MeasurableSet C := measurableSet_kstQuasiCrossingEvent n k
  have hEm : MeasurableSet E := measurableSet_kstUnorientedExceptionalPathEvent n m k
  have hLm : MeasurableSet L := measurableSet_kstQuasiCrossingEvent m k
  have hcompl := bond_measureReal_mul_le_inter_of_lower μ ha hC.compl hE.compl hCm.compl hEm.compl
  rw [← compl_union, probReal_compl_eq_one_sub hCm, probReal_compl_eq_one_sub hEm,
    probReal_compl_eq_one_sub (hCm.union hEm)] at hcompl
  have hcover := measureReal_mono (μ := μ)
    (kstQuasiCrossing_subset_smaller_union_unoriented_exceptional n m k)
    (measure_ne_top μ (C ∪ E))
  have hElarge : δ ≤ μ.real E := by
    by_contra! hEsmall
    have hp : 0 < (δ - μ.real C) * (δ - μ.real E) :=
      mul_pos (by linarith) (by linarith)
    have hn : 0 ≤ (1 - δ) * ((δ - μ.real C) + (δ - μ.real E)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hEL := ha E L hE hL hEm hLm
  have hsub := measureReal_mono (μ := μ) hbridge (measure_ne_top μ (A ∪ B))
  have hbridgecompl := bond_measureReal_mul_le_inter_of_lower μ ha
    hA.compl hB.compl hAm.compl hBm.compl
  rw [← compl_union, probReal_compl_eq_one_sub hAm, probReal_compl_eq_one_sub hBm,
    probReal_compl_eq_one_sub (hAm.union hBm), ← heq] at hbridgecompl
  have hfinal : μ.real E * μ.real L ≤ 1 - (1 - μ.real A) ^ 2 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hElarge measureReal_nonneg).trans hfinal

end Sandpile.External.RSW
