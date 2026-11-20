import Sandpile.External.RSW.MatrixMeasure
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Crossing inequalities for finite random matrices

A full column intersects every row. Independent rows and columns turn this inclusion
into a comparison of elementary powers.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Sandpile.External.RSW

/-- The probability of a finite product of identical events is the corresponding power. -/
theorem measureReal_pi_const {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (A : Set α) (n : ℕ) :
    (Measure.pi fun _ : Fin n => μ).real (Set.univ.pi fun _ => A) = (μ.real A) ^ n := by
  simp only [measureReal_def, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow]

/-- For a product law on Boolean matrices, the full-column event is contained in the
intersection of the events that each row contains a true entry. -/
theorem matrix_crossing_power_bound (ν : Measure Bool) [IsProbabilityMeasure ν] (n : ℕ) :
    1 - (1 - (ν.real {true}) ^ n) ^ n ≤ (1 - (1 - ν.real {true}) ^ n) ^ n := by
  classical
  let rowLaw := Measure.pi fun _ : Fin n => ν
  let P := Measure.pi fun _ : Fin n => rowLaw
  let f : Fin n → Bool := fun _ => false
  let t : Fin n → Bool := fun _ => true
  let A : Set (Fin n → Fin n → Bool) := Set.univ.pi fun _ => {f}ᶜ
  let B : Set (Fin n → Fin n → Bool) := Set.univ.pi fun _ => {t}ᶜ
  let T : (Fin n → Fin n → Bool) → (Fin n → Fin n → Bool) := fun ω i j => ω j i
  have hT : MeasurePreserving T P P := measurePreserving_matrix_transpose ν
  have hAm : MeasurableSet A := by
    exact MeasurableSet.pi countable_univ (fun _ _ => (measurableSet_singleton f).compl)
  have hBm : MeasurableSet B := by
    exact MeasurableSet.pi countable_univ (fun _ _ => (measurableSet_singleton t).compl)
  have hsub : Aᶜ ⊆ T ⁻¹' B := by
    intro ω hω
    simp only [A, mem_compl_iff, Set.mem_pi, mem_univ, true_implies,
      mem_singleton_iff] at hω
    push Not at hω
    obtain ⟨i, hi⟩ := hω
    simp only [T, B, mem_preimage, Set.mem_pi, mem_univ, true_implies,
      mem_compl_iff, mem_singleton_iff]
    change ∀ j, (fun k => ω k j) ≠ t
    intro j hj
    have ha := congrFun hi j
    have hb := congrFun hj i
    change ω i j = false at ha
    change ω i j = true at hb
    simp_all
  have hfalse : ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by
    ext b
    cases b <;> simp
  have hrowf : rowLaw.real {f} = (1 - ν.real {true}) ^ n := by
    rw [measureReal_def, Measure.pi_singleton]
    change (∏ _ : Fin n, ν {false}).toReal = _
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
    change (ν.real {false}) ^ n = _
    rw [hfalse, probReal_compl_eq_one_sub (measurableSet_singleton true)]
  have hrowt : rowLaw.real {t} = (ν.real {true}) ^ n := by
    rw [measureReal_def, Measure.pi_singleton]
    change (∏ _ : Fin n, ν {true}).toReal = _
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
    rfl
  have hA : P.real A = (1 - (1 - ν.real {true}) ^ n) ^ n := by
    rw [show P.real A = (rowLaw.real {f}ᶜ) ^ n from measureReal_pi_const rowLaw {f}ᶜ n,
      probReal_compl_eq_one_sub (measurableSet_singleton f), hrowf]
  have hB : P.real B = (1 - (ν.real {true}) ^ n) ^ n := by
    rw [show P.real B = (rowLaw.real {t}ᶜ) ^ n from measureReal_pi_const rowLaw {t}ᶜ n,
      probReal_compl_eq_one_sub (measurableSet_singleton t), hrowt]
  have hm := measureReal_mono (μ := P) hsub (measure_ne_top P _)
  have hpres : P.real (T ⁻¹' B) = P.real B := hT.measureReal_preimage hBm.nullMeasurableSet
  rw [hpres, probReal_compl_eq_one_sub hAm, hA, hB] at hm
  linarith

/-- The finite matrix inequality for any parameter in the unit interval. -/
theorem matrix_crossing_power_bound_unit (n : ℕ) (t : Icc (0 : ℝ) 1) :
    1 - (1 - (t : ℝ) ^ n) ^ n ≤ (1 - (1 - (t : ℝ)) ^ n) ^ n := by
  let ν := ProbabilityTheory.bernoulliMeasure true false t
  have hp : ν.real {true} = (t : ℝ) := by
    simp [ν]
  simpa only [hp] using matrix_crossing_power_bound ν n

end Sandpile.External.RSW
