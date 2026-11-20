import Sandpile.External.RSW.QuasiCrossing

/-!
# Arm and bridge events

The arm and bridge events are open connections between the boundary targets of their
centered rectangles. At scales divisible by 64 and 12, respectively, their dimensions
agree with the fractional constants in the planar crossing argument.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- An open connection inside a finite induced rectangle graph. -/
def bondConnectionEvent (Q : Finset (Site 2)) (A B : Set Q) :
    Set (Sym2 (Site 2) → Bool) :=
  {ω | ∃ (a b : Q) (p : (rectangleGraph Q).Walk a b),
    a ∈ A ∧ b ∈ B ∧ IsBondOpenWalk ω p}

/-- A connection event is increasing. -/
theorem isUpperSet_bondConnectionEvent (Q : Finset (Site 2)) (A B : Set Q) :
    IsUpperSet (bondConnectionEvent Q A B) := by
  intro ω η hωη
  rintro ⟨a, b, p, ha, hb, hp⟩
  exact ⟨a, b, p, ha, hb, hp.mono hωη p⟩

/-- A connection event is measurable. -/
theorem measurableSet_bondConnectionEvent (Q : Finset (Site 2)) (A B : Set Q) :
    MeasurableSet (bondConnectionEvent Q A B) := by
  let (a b : Q) : Countable ((rectangleGraph Q).Walk a b) :=
    SimpleGraph.Walk.support_injective.countable
  have hm (a b : Q) (p : (rectangleGraph Q).Walk a b) :
      MeasurableSet {ω : Sym2 (Site 2) → Bool |
        a ∈ A ∧ b ∈ B ∧ IsBondOpenWalk ω p} :=
    (MeasurableSet.const _).inter ((MeasurableSet.const _).inter (measurableSet_isBondOpenWalk p))
  simpa only [bondConnectionEvent, ofPred_exists] using
    (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      MeasurableSet.iUnion fun p => hm a b p)

/-- The arm event connects the two central vertical boundary targets at scale `m`. -/
def kstArmEvent (m : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  let Q := centeredPlaneRectangle (m + m / 64) m
  bondConnectionEvent Q
    {z | (z : Site 2) 1 = m ∧ -((m / 64 : ℕ) : ℤ) ≤ (z : Site 2) 0 ∧
      (z : Site 2) 0 ≤ (m / 64 : ℕ)}
    {z | (z : Site 2) 1 = -(m : ℤ) ∧ -((m / 64 : ℕ) : ℤ) ≤ (z : Site 2) 0 ∧
      (z : Site 2) 0 ≤ (m / 64 : ℕ)}

/-- The left boundary target of the scale-`m` bridge rectangle. -/
def kstBridgeLeft (m : ℕ) (z : centeredPlaneRectangle (m + m / 12) m) : Prop :=
  (z : Site 2) 0 = -((m + m / 12 : ℕ) : ℤ) ∨
    ((z : Site 2) 0 ≤ -((m / 12 : ℕ) : ℤ) ∧
      ((z : Site 2) 1 = -(m : ℤ) ∨ (z : Site 2) 1 = m))

/-- The right boundary target of the scale-`m` bridge rectangle. -/
def kstBridgeRight (m : ℕ) (z : centeredPlaneRectangle (m + m / 12) m) : Prop :=
  (z : Site 2) 0 = ((m + m / 12 : ℕ) : ℤ) ∨
    (((m / 12 : ℕ) : ℤ) ≤ (z : Site 2) 0 ∧
      ((z : Site 2) 1 = -(m : ℤ) ∨ (z : Site 2) 1 = m))

/-- The bridge event connects the left and right boundary targets at scale `m`. -/
def kstBridgeEvent (m : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  bondConnectionEvent (centeredPlaneRectangle (m + m / 12) m)
    {z | kstBridgeLeft m z} {z | kstBridgeRight m z}

/-- The arm event is increasing. -/
theorem isUpperSet_kstArmEvent (m : ℕ) : IsUpperSet (kstArmEvent m) :=
  isUpperSet_bondConnectionEvent _ _ _

/-- The arm event is measurable. -/
theorem measurableSet_kstArmEvent (m : ℕ) : MeasurableSet (kstArmEvent m) :=
  measurableSet_bondConnectionEvent _ _ _

/-- The bridge event is increasing. -/
theorem isUpperSet_kstBridgeEvent (m : ℕ) : IsUpperSet (kstBridgeEvent m) :=
  isUpperSet_bondConnectionEvent _ _ _

/-- The bridge event is measurable. -/
theorem measurableSet_kstBridgeEvent (m : ℕ) : MeasurableSet (kstBridgeEvent m) :=
  measurableSet_bondConnectionEvent _ _ _

end Sandpile.External.RSW
