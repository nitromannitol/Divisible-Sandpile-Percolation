import Sandpile.External.RSW.FourArms
import Sandpile.External.RSW.ArmCrossing

/-!
# Six events for adjacent-scale quasi-crossings

The four-arm event and two translated rectangle crossings have probability at least
the product of the three squared arm probabilities.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The translation of an auxiliary horizontal crossing rectangle. -/
def kstAuxCrossingShift (m : ℕ) (left : Bool) : Site 2 :=
  ![if left then -(5 * (m : ℤ)) else -(3 * (m : ℤ)) + 3 * ((m / 12 : ℕ) : ℤ),
    -(4 * (m : ℤ))]

/-- One of the two auxiliary horizontal crossings in the adjacent-scale construction. -/
def kstAuxCrossingEvent (m : ℕ) (left : Bool) : Set (Sym2 (Site 2) → Bool) :=
  (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + kstAuxCrossingShift m left)) ⁻¹'
    bondCrossingEvent (8 * m - 3 * (m / 12)) (8 * m)

/-- An auxiliary crossing event is increasing. -/
theorem isUpperSet_kstAuxCrossingEvent (m : ℕ) (left : Bool) :
    IsUpperSet (kstAuxCrossingEvent m left) := by
  intro ω η hω h
  exact isUpperSet_bondCrossingEvent _ _ (fun e => hω _) h

/-- An auxiliary crossing event is measurable. -/
theorem measurableSet_kstAuxCrossingEvent (m : ℕ) (left : Bool) :
    MeasurableSet (kstAuxCrossingEvent m left) := by
  apply (measurableSet_bondCrossingEvent _ _).preimage
  exact Measurable.of_eval (fun e => measurable_pi_apply _)

/-- The four arms and two auxiliary crossings. -/
def kstAdjacentSixEvent (m : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  kstFourArmEvent m ∩ (kstAuxCrossingEvent m true ∩ kstAuxCrossingEvent m false)

/-- The six-event configuration is increasing. -/
theorem isUpperSet_kstAdjacentSixEvent (m : ℕ) : IsUpperSet (kstAdjacentSixEvent m) :=
  (isUpperSet_kstFourArmEvent m).inter
    ((isUpperSet_kstAuxCrossingEvent m true).inter (isUpperSet_kstAuxCrossingEvent m false))

/-- The six-event configuration is measurable. -/
theorem measurableSet_kstAdjacentSixEvent (m : ℕ) : MeasurableSet (kstAdjacentSixEvent m) :=
  (measurableSet_kstFourArmEvent m).inter
    ((measurableSet_kstAuxCrossingEvent m true).inter (measurableSet_kstAuxCrossingEvent m false))

/-- At a divisible base scale the six-event probability dominates the product of three
squared arm probabilities. -/
theorem measureReal_kstAdjacentSixEvent_ge (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (j : ℕ) :
    μ.real (kstArmEvent (kstBaseScale j)) ^ 2 *
      μ.real (kstArmEvent (5 * kstBaseScale j / 2)) ^ 2 *
      μ.real (kstArmEvent (31 * kstBaseScale j / 8)) ^ 2 ≤
        μ.real (kstAdjacentSixEvent (kstBaseScale j)) := by
  let m := kstBaseScale j
  let E := kstFourArmEvent m
  let A := kstAuxCrossingEvent m true
  let B := kstAuxCrossingEvent m false
  let a := μ.real (kstArmEvent m)
  let b := μ.real (kstArmEvent (5 * m / 2))
  let c := μ.real (kstArmEvent (31 * m / 8))
  let p := μ.real (bondCrossingEvent (8 * m - 3 * (m / 12)) (8 * m))
  have hA : μ.real A = p :=
    (ht (kstAuxCrossingShift m true)).measureReal_preimage
      (measurableSet_bondCrossingEvent _ _).nullMeasurableSet
  have hB : μ.real B = p :=
    (ht (kstAuxCrossingShift m false)).measureReal_preimage
      (measurableSet_bondCrossingEvent _ _).nullMeasurableSet
  have hc : c ≤ p := measureReal_kstArm_intermediate_le_crossing μ ht hs j
  have hC : c ^ 2 ≤ μ.real (A ∩ B) := by
    have hAB := ha A B (isUpperSet_kstAuxCrossingEvent m true)
      (isUpperSet_kstAuxCrossingEvent m false) (measurableSet_kstAuxCrossingEvent m true)
      (measurableSet_kstAuxCrossingEvent m false)
    rw [hA, hB, ← sq] at hAB
    exact (pow_le_pow_left₀ measureReal_nonneg hc 2).trans hAB
  have hE : a ^ 2 * b ^ 2 ≤ μ.real E := measureReal_kstFourArmEvent_ge μ ha ht m
  have hEA := ha E (A ∩ B) (isUpperSet_kstFourArmEvent m)
    ((isUpperSet_kstAuxCrossingEvent m true).inter (isUpperSet_kstAuxCrossingEvent m false))
    (measurableSet_kstFourArmEvent m)
    ((measurableSet_kstAuxCrossingEvent m true).inter (measurableSet_kstAuxCrossingEvent m false))
  exact (mul_le_mul hE hC (sq_nonneg _) measureReal_nonneg).trans hEA

end Sandpile.External.RSW
