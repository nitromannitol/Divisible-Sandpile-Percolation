import Sandpile.External.RSW.SiteBondCrossing

/-!
# Measurability of bond crossing events

A finite rectangle has countably many walks, and openness of each walk depends on finitely
many bonds. Hence its bond crossing event is measurable.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The event that a fixed rectangle walk is bond-open is measurable. -/
theorem measurableSet_isBondOpenWalk {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b) :
    MeasurableSet {ω : Sym2 (Site 2) → Bool | IsBondOpenWalk ω p} := by
  induction p with
  | nil => simp [IsBondOpenWalk]
  | @cons a b c hab p ih =>
    change MeasurableSet ({ω : Sym2 (Site 2) → Bool | ω s((a : Site 2), (b : Site 2)) = true} ∩
      {ω : Sym2 (Site 2) → Bool | IsBondOpenWalk ω p})
    exact ((measurableSet_singleton true).preimage
      (measurable_pi_apply s((a : Site 2), (b : Site 2)))).inter ih

/-- A rectangle bond crossing event is measurable. -/
theorem measurableSet_bondCrossingEvent (w h : ℕ) : MeasurableSet (bondCrossingEvent w h) := by
  let (a b : planeRectangle w h) : Countable ((rectangleGraph (planeRectangle w h)).Walk a b) :=
    SimpleGraph.Walk.support_injective.countable
  have hm (a b : planeRectangle w h) (p : (rectangleGraph (planeRectangle w h)).Walk a b) :
      MeasurableSet {ω : Sym2 (Site 2) → Bool |
        a ∈ rectangleLeft (planeRectangle w h) ∧ b ∈ rectangleRight (planeRectangle w h) ∧
          IsBondOpenWalk ω p} :=
    (MeasurableSet.const _).inter ((MeasurableSet.const _).inter (measurableSet_isBondOpenWalk p))
  simpa only [bondCrossingEvent, ofPred_exists] using
    (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun p => hm a b p)

end Sandpile.External.RSW
