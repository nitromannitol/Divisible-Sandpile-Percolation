import Sandpile.External.RSW.CenteredGeometry
import Sandpile.External.RSW.RectangleGluing

/-!
# Quasi-crossings

At an integer scale divisible by twelve, an `m`-path crosses the centered
`(m + m / 12) × m` rectangle vertically with both endpoints in the central target.
A quasi-crossing has two such open paths, one connected to each horizontal boundary
of a larger centered rectangle.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A simple vertical path with endpoints in the central targets and support in the
scale-`m` rectangle. -/
def IsKSTPath (m : ℕ) {Q : Finset (Site 2)} {a b : Q} (p : (rectangleGraph Q).Walk a b) : Prop :=
  p.IsPath ∧
  (a : Site 2) 1 = m ∧ (b : Site 2) 1 = -(m : ℤ) ∧
  -((m / 12 : ℕ) : ℤ) ≤ (a : Site 2) 0 ∧ (a : Site 2) 0 ≤ (m / 12 : ℕ) ∧
  -((m / 12 : ℕ) : ℤ) ≤ (b : Site 2) 0 ∧ (b : Site 2) 0 ≤ (m / 12 : ℕ) ∧
  ∀ z ∈ p.support, (z : Site 2) ∈ centeredPlaneRectangle (m + m / 12) m

/-- A wall is an open scale-`m` path joined to one horizontal side of the scale-`n`
quasi-crossing rectangle. The Boolean parameter selects the left side when true. -/
def kstWallEvent (n m : ℕ) (left : Bool) : Set (Sym2 (Site 2) → Bool) :=
  let Q := centeredPlaneRectangle (n + 3 * (n / 12)) n
  {ω | ∃ (a b x c : Q) (p : (rectangleGraph Q).Walk a b)
      (q : (rectangleGraph Q).Walk x c),
    IsKSTPath m p ∧ x ∈ p.support ∧
    (c : Site 2) 0 = (if left then -((n + 3 * (n / 12) : ℕ) : ℤ)
      else ((n + 3 * (n / 12) : ℕ) : ℤ)) ∧
    IsBondOpenWalk ω p ∧ IsBondOpenWalk ω q}

/-- A quasi-crossing has a left wall and a right wall. -/
def kstQuasiCrossingEvent (n m : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  kstWallEvent n m true ∩ kstWallEvent n m false

/-- Wall events are increasing in the bond configuration. -/
theorem isUpperSet_kstWallEvent (n m : ℕ) (left : Bool) :
    IsUpperSet (kstWallEvent n m left) := by
  intro ω η hωη
  rintro ⟨a, b, x, c, p, q, hp, hx, hc, hpo, hqo⟩
  exact ⟨a, b, x, c, p, q, hp, hx, hc, hpo.mono hωη p, hqo.mono hωη q⟩

/-- Quasi-crossing events are increasing in the bond configuration. -/
theorem isUpperSet_kstQuasiCrossingEvent (n m : ℕ) :
    IsUpperSet (kstQuasiCrossingEvent n m) :=
  (isUpperSet_kstWallEvent n m true).inter (isUpperSet_kstWallEvent n m false)

/-- Wall events are measurable. -/
theorem measurableSet_kstWallEvent (n m : ℕ) (left : Bool) :
    MeasurableSet (kstWallEvent n m left) := by
  let Q := centeredPlaneRectangle (n + 3 * (n / 12)) n
  let (a b : Q) : Countable ((rectangleGraph Q).Walk a b) :=
    SimpleGraph.Walk.support_injective.countable
  have hm (a b x c : Q) (p : (rectangleGraph Q).Walk a b)
      (q : (rectangleGraph Q).Walk x c) :
      MeasurableSet {ω : Sym2 (Site 2) → Bool |
        IsKSTPath m p ∧ x ∈ p.support ∧
        (c : Site 2) 0 = (if left then -((n + 3 * (n / 12) : ℕ) : ℤ)
          else ((n + 3 * (n / 12) : ℕ) : ℤ)) ∧
        IsBondOpenWalk ω p ∧ IsBondOpenWalk ω q} :=
    (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      ((MeasurableSet.const _).inter ((measurableSet_isBondOpenWalk p).inter
        (measurableSet_isBondOpenWalk q))))
  change MeasurableSet {ω : Sym2 (Site 2) → Bool | ∃ (a b x c : Q)
    (p : (rectangleGraph Q).Walk a b) (q : (rectangleGraph Q).Walk x c),
      IsKSTPath m p ∧ x ∈ p.support ∧
      (c : Site 2) 0 = (if left then -((n + 3 * (n / 12) : ℕ) : ℤ)
        else ((n + 3 * (n / 12) : ℕ) : ℤ)) ∧
      IsBondOpenWalk ω p ∧ IsBondOpenWalk ω q}
  simpa only [ofPred_exists] using
    (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun c =>
      MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun q => hm a b x c p q)

/-- Quasi-crossing events are measurable. -/
theorem measurableSet_kstQuasiCrossingEvent (n m : ℕ) :
    MeasurableSet (kstQuasiCrossingEvent n m) :=
  (measurableSet_kstWallEvent n m true).inter (measurableSet_kstWallEvent n m false)

end Sandpile.External.RSW
