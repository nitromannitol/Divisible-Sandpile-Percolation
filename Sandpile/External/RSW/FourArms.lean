import Sandpile.External.RSW.TranslatedArm
import Sandpile.External.RSW.BaseScaleArithmetic

/-!
# Four-arm events

Two translated arms at scale `m` and two translated arms at scale `5m/2` form the
initial configuration in the adjacent-scale quasi-crossing construction.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- An arm event translated by a lattice vector. -/
def translatedKSTArmEvent (m : ℕ) (v : Site 2) : Set (Sym2 (Site 2) → Bool) :=
  (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + v)) ⁻¹' kstArmEvent m

/-- A translated arm event is increasing. -/
theorem isUpperSet_translatedKSTArmEvent (m : ℕ) (v : Site 2) :
    IsUpperSet (translatedKSTArmEvent m v) := by
  intro ω η hω h
  exact isUpperSet_kstArmEvent m (fun e => hω _) h

/-- A translated arm event is measurable. -/
theorem measurableSet_translatedKSTArmEvent (m : ℕ) (v : Site 2) :
    MeasurableSet (translatedKSTArmEvent m v) := by
  apply (measurableSet_kstArmEvent m).preimage
  exact Measurable.of_eval (fun e => measurable_pi_apply _)

/-- A translation-invariant law assigns the same probability to a translated arm. -/
theorem measureReal_translatedKSTArmEvent (μ : Measure (Sym2 (Site 2) → Bool))
    (m : ℕ) (v : Site 2) (ht : MeasurePreserving
      (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + v)) μ μ) :
    μ.real (translatedKSTArmEvent m v) = μ.real (kstArmEvent m) :=
  ht.measureReal_preimage (measurableSet_kstArmEvent m).nullMeasurableSet

/-- The intersection of the four translated arms in the quasi-crossing construction. -/
def kstFourArmEvent (m : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  let α := ((m / 64 : ℕ) : ℤ)
  let t := ((3 * m / 2 : ℕ) : ℤ)
  translatedKSTArmEvent m ![4 * α, 0] ∩
    (translatedKSTArmEvent m ![-(4 * α), 0] ∩
      (translatedKSTArmEvent (5 * m / 2) ![0, t] ∩
        translatedKSTArmEvent (5 * m / 2) ![0, -t]))

/-- The four-arm event is increasing. -/
theorem isUpperSet_kstFourArmEvent (m : ℕ) : IsUpperSet (kstFourArmEvent m) := by
  exact (isUpperSet_translatedKSTArmEvent _ _).inter
    ((isUpperSet_translatedKSTArmEvent _ _).inter
      ((isUpperSet_translatedKSTArmEvent _ _).inter (isUpperSet_translatedKSTArmEvent _ _)))

/-- The four-arm event is measurable. -/
theorem measurableSet_kstFourArmEvent (m : ℕ) : MeasurableSet (kstFourArmEvent m) := by
  exact (measurableSet_translatedKSTArmEvent _ _).inter
    ((measurableSet_translatedKSTArmEvent _ _).inter
      ((measurableSet_translatedKSTArmEvent _ _).inter (measurableSet_translatedKSTArmEvent _ _)))

/-- Positive association bounds the probability of the four-arm event by the product of
the two squared arm probabilities. -/
theorem measureReal_kstFourArmEvent_ge (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ) (m : ℕ) :
    μ.real (kstArmEvent m) ^ 2 * μ.real (kstArmEvent (5 * m / 2)) ^ 2 ≤
      μ.real (kstFourArmEvent m) := by
  let α := ((m / 64 : ℕ) : ℤ)
  let t := ((3 * m / 2 : ℕ) : ℤ)
  let A := translatedKSTArmEvent m ![4 * α, 0]
  let B := translatedKSTArmEvent m ![-(4 * α), 0]
  let C := translatedKSTArmEvent (5 * m / 2) ![0, t]
  let D := translatedKSTArmEvent (5 * m / 2) ![0, -t]
  have hA : μ.real A = μ.real (kstArmEvent m) := measureReal_translatedKSTArmEvent μ m _ (ht _)
  have hB : μ.real B = μ.real (kstArmEvent m) := measureReal_translatedKSTArmEvent μ m _ (ht _)
  have hC : μ.real C = μ.real (kstArmEvent (5 * m / 2)) :=
    measureReal_translatedKSTArmEvent μ _ _ (ht _)
  have hD : μ.real D = μ.real (kstArmEvent (5 * m / 2)) :=
    measureReal_translatedKSTArmEvent μ _ _ (ht _)
  have hCD := ha C D (isUpperSet_translatedKSTArmEvent _ _) (isUpperSet_translatedKSTArmEvent _ _)
    (measurableSet_translatedKSTArmEvent _ _) (measurableSet_translatedKSTArmEvent _ _)
  have hBCD := ha B (C ∩ D) (isUpperSet_translatedKSTArmEvent _ _)
    ((isUpperSet_translatedKSTArmEvent _ _).inter (isUpperSet_translatedKSTArmEvent _ _))
    (measurableSet_translatedKSTArmEvent _ _)
    ((measurableSet_translatedKSTArmEvent _ _).inter (measurableSet_translatedKSTArmEvent _ _))
  have hABCD := ha A (B ∩ (C ∩ D)) (isUpperSet_translatedKSTArmEvent _ _)
    ((isUpperSet_translatedKSTArmEvent _ _).inter
      ((isUpperSet_translatedKSTArmEvent _ _).inter (isUpperSet_translatedKSTArmEvent _ _)))
    (measurableSet_translatedKSTArmEvent _ _)
    ((measurableSet_translatedKSTArmEvent _ _).inter
      ((measurableSet_translatedKSTArmEvent _ _).inter (measurableSet_translatedKSTArmEvent _ _)))
  calc
    _ = μ.real A * (μ.real B * (μ.real C * μ.real D)) := by rw [hA, hB, hC, hD]; ring
    _ ≤ μ.real A * (μ.real B * μ.real (C ∩ D)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCD measureReal_nonneg) measureReal_nonneg
    _ ≤ μ.real A * μ.real (B ∩ (C ∩ D)) := mul_le_mul_of_nonneg_left hBCD measureReal_nonneg
    _ ≤ _ := hABCD

end Sandpile.External.RSW
