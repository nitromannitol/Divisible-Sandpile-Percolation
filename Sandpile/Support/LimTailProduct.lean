/-
Finite coordinate changes and Kolmogorov's zero-one law.
Erasing a finite prefix is measurable for the remaining coordinate sigma-algebra.
Thus a measurable event invariant under every finite coordinate change is a tail
event. Under independent coordinates, positive probability makes it almost sure.
The invariance hypothesis is pointwise on the sequence space.
-/
import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
abbrev Sandpile.Support.coordinateSigma (i : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  MeasurableSpace.comap (fun x : ℕ → ℝ => x i) inferInstance
def Sandpile.Support.erasePrefix (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i < n then 0 else x i
open Sandpile.Support

theorem Sandpile.Support.measurable_erasePrefix_tail (n : ℕ) :
    @Measurable (ℕ → ℝ) (ℕ → ℝ)
      (⨆ i, ⨆ (_ : n ≤ i), coordinateSigma i) inferInstance (erasePrefix n) := by
  refine @measurable_pi_lambda _ _ _
    (⨆ i, ⨆ (_ : n ≤ i), coordinateSigma i) _ _ (fun i => ?_)
  by_cases hi : i < n
  · simpa only [erasePrefix, if_pos hi] using
      (measurable_const : @Measurable (ℕ → ℝ) ℝ
        (⨆ j, ⨆ (_ : n ≤ j), coordinateSigma j) inferInstance (fun _ => (0 : ℝ)))
  · have hm : @Measurable (ℕ → ℝ) ℝ (coordinateSigma i) inferInstance (fun x => x i) :=
      comap_measurable _
    have hle : coordinateSigma i ≤ ⨆ j, ⨆ (_ : n ≤ j), coordinateSigma j := by
      exact (le_iSup (fun (_ : n ≤ i) => coordinateSigma i) (Nat.le_of_not_gt hi)).trans
        (le_iSup (fun j => ⨆ (_ : n ≤ j), coordinateSigma j) i)
    simpa only [erasePrefix, if_neg hi] using hm.mono hle le_rfl


theorem Sandpile.Support.measurableSet_tail_of_finite_changes {E : Set (ℕ → ℝ)}
    (hE : MeasurableSet E)
    (hinv : ∀ x y : ℕ → ℝ, (∃ n : ℕ, ∀ i, n ≤ i → x i = y i) → (x ∈ E ↔ y ∈ E)) :
    MeasurableSet[Filter.limsup coordinateSigma Filter.atTop] E := by
  rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
  intro n
  have heq : erasePrefix n ⁻¹' E = E := by
    ext x
    exact hinv (erasePrefix n x) x ⟨n, fun i hi => by simp [erasePrefix, Nat.not_lt.mpr hi]⟩
  rw [← heq]
  exact hE.preimage (measurable_erasePrefix_tail n)


theorem Sandpile.Support.ae_of_finite_changes (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P]
    (hind : iIndepFun (fun (i : ℕ) (x : ℕ → ℝ) => x i) P) {E : Set (ℕ → ℝ)}
    (hE : MeasurableSet E)
    (hinv : ∀ x y : ℕ → ℝ, (∃ n : ℕ, ∀ i, n ≤ i → x i = y i) → (x ∈ E ↔ y ∈ E))
    (hpos : 0 < P E) : ∀ᵐ x ∂P, x ∈ E := by
  have ht := measurableSet_tail_of_finite_changes hE hinv
  have hle : ∀ i, coordinateSigma i ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
    fun i => (measurable_pi_apply i).comap_le
  rcases measure_zero_or_one_of_measurableSet_limsup_atTop hle hind ht with h0 | h1
  · exact False.elim (hpos.ne' h0)
  · exact ae_iff.mpr ((prob_compl_eq_zero_iff hE).mpr h1)

