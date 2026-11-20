import Sandpile.External.RSW.FourArmBottomConnection

/-!
# Measurability of connected KST paths

The events that a KST path connects to a specified vertex set are increasing and
measurable. This applies to the top- and bottom-connected paths of the four-arm event.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- An open KST path joined by an open walk to a specified set of vertices. -/
def kstConnectedPathEvent (Q : Finset (Site 2)) (m : ℕ) (A : Set Q) :
    Set (Sym2 (Site 2) → Bool) :=
  {ω | ∃ (a b x d : Q) (p : (rectangleGraph Q).Walk a b) (q : (rectangleGraph Q).Walk x d),
    IsKSTPath m p ∧ x ∈ p.support ∧ d ∈ A ∧ IsBondOpenWalk ω p ∧ IsBondOpenWalk ω q}

/-- Connecting a KST path to a vertex set is an increasing event. -/
theorem isUpperSet_kstConnectedPathEvent (Q : Finset (Site 2)) (m : ℕ) (A : Set Q) :
    IsUpperSet (kstConnectedPathEvent Q m A) := by
  intro ω η hω
  rintro ⟨a, b, x, d, p, q, hp, hx, hd, hpo, hqo⟩
  exact ⟨a, b, x, d, p, q, hp, hx, hd, hpo.mono hω p, hqo.mono hω q⟩

/-- Connecting a KST path to a vertex set is a measurable event. -/
theorem measurableSet_kstConnectedPathEvent (Q : Finset (Site 2)) (m : ℕ) (A : Set Q) :
    MeasurableSet (kstConnectedPathEvent Q m A) := by
  let (a b : Q) : Countable ((rectangleGraph Q).Walk a b) :=
    SimpleGraph.Walk.support_injective.countable
  have hm (a b x d : Q) (p : (rectangleGraph Q).Walk a b)
      (q : (rectangleGraph Q).Walk x d) :
      MeasurableSet {ω : Sym2 (Site 2) → Bool |
        IsKSTPath m p ∧ x ∈ p.support ∧ d ∈ A ∧ IsBondOpenWalk ω p ∧ IsBondOpenWalk ω q} :=
    (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      ((MeasurableSet.const _).inter ((measurableSet_isBondOpenWalk p).inter
        (measurableSet_isBondOpenWalk q))))
  change MeasurableSet {ω : Sym2 (Site 2) → Bool | ∃ (a b x d : Q)
    (p : (rectangleGraph Q).Walk a b) (q : (rectangleGraph Q).Walk x d),
      IsKSTPath m p ∧ x ∈ p.support ∧ d ∈ A ∧ IsBondOpenWalk ω p ∧ IsBondOpenWalk ω q}
  simpa only [ofPred_exists] using
    (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun d =>
      MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun q => hm a b x d p q)

/-- A top-connected KST path is an increasing event. -/
theorem isUpperSet_kstTopConnectedEvent (W n m : ℕ) : IsUpperSet (kstTopConnectedEvent W n m) :=
  isUpperSet_kstConnectedPathEvent _ _ _

/-- A top-connected KST path is a measurable event. -/
theorem measurableSet_kstTopConnectedEvent (W n m : ℕ) : MeasurableSet (kstTopConnectedEvent W n m) :=
  measurableSet_kstConnectedPathEvent _ _ _

/-- A bottom-connected KST path is an increasing event. -/
theorem isUpperSet_kstBottomConnectedEvent (W n m : ℕ) : IsUpperSet (kstBottomConnectedEvent W n m) :=
  isUpperSet_kstConnectedPathEvent _ _ _

/-- A bottom-connected KST path is a measurable event. -/
theorem measurableSet_kstBottomConnectedEvent (W n m : ℕ) : MeasurableSet (kstBottomConnectedEvent W n m) :=
  measurableSet_kstConnectedPathEvent _ _ _

end Sandpile.External.RSW
