import Sandpile.External.RSW.EmbeddedConnectedWalls
import Sandpile.External.RSW.ConnectedWallCrossing

/-!
# Quasi-crossings from joined vertical walls

Two horizontal side walks and intersecting top- and bottom-connected KST paths
supply both walls of a quasi-crossing.
-/

namespace Sandpile.External.RSW

/-- Joined vertical walls and two spanning side walks yield a quasi-crossing. -/
theorem kstQuasiCrossing_of_joined_vertical_walls (n m M : ℕ) (hM : 0 < M)
    {ω : Sym2 (Site 2) → Bool}
    {a b x top c d y bottom left leftEnd right rightEnd :
      centeredPlaneRectangle (n + 3 * (n / 12)) n}
    (upper : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b)
    (upperLink : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk x top)
    (lower : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk c d)
    (lowerLink : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk y bottom)
    (leftWalk : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk left leftEnd)
    (rightWalk : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk right rightEnd)
    (hp : IsKSTPath m upper) (hq : IsKSTPath m lower)
    (hx : x ∈ upper.support) (hy : y ∈ lower.support)
    (hpOpen : IsBondOpenWalk ω upper) (huOpen : IsBondOpenWalk ω upperLink)
    (hqOpen : IsBondOpenWalk ω lower) (hvOpen : IsBondOpenWalk ω lowerLink)
    (hlOpen : IsBondOpenWalk ω leftWalk) (hrOpen : IsBondOpenWalk ω rightWalk)
    (hleft : (left : Site 2) 0 = -((n + 3 * (n / 12) : ℕ) : ℤ))
    (hright : (right : Site 2) 0 = ((n + 3 * (n / 12) : ℕ) : ℤ))
    (hleftStart : (left : Site 2) 0 ≤ -(M : ℤ))
    (hleftEnd : (M : ℤ) ≤ (leftEnd : Site 2) 0)
    (hrightStart : (M : ℤ) ≤ (right : Site 2) 0)
    (hrightEnd : (rightEnd : Site 2) 0 ≤ -(M : ℤ))
    (htop : (top : Site 2) 1 = n) (hbottom : (bottom : Site 2) 1 = -(n : ℤ))
    (hupper : ∀ z, (z ∈ upper.support ∨ z ∈ upperLink.support) →
      (z : Site 2) ∈ centeredPlaneRectangle M n)
    (hlower : ∀ z, (z ∈ lower.support ∨ z ∈ lowerLink.support) →
      (z : Site 2) ∈ centeredPlaneRectangle M n)
    (hjoin : ∃ z, (z ∈ upper.support ∨ z ∈ upperLink.support) ∧
      (z ∈ lower.support ∨ z ∈ lowerLink.support)) :
    ω ∈ kstQuasiCrossingEvent n m := by
  have hhor {u v : centeredPlaneRectangle (n + 3 * (n / 12)) n}
      (walk : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk u v) :
      ∀ z ∈ walk.support, -(n : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ n := by
    intro z _
    exact ⟨((mem_centeredPlaneRectangle _ _ _).mp z.property).2.2.1,
      ((mem_centeredPlaneRectangle _ _ _).mp z.property).2.2.2⟩
  have hleftMeet := horizontal_walk_intersects_joined_vertical_walls hM leftWalk
    upper upperLink lower lowerLink hleftStart hleftEnd (hhor leftWalk)
    hupper hlower hx hy htop hbottom hjoin
  have hrightMeet := horizontal_walk_intersects_joined_vertical_walls hM rightWalk.reverse
    upper upperLink lower lowerLink hrightEnd hrightStart (hhor rightWalk.reverse)
    hupper hlower hx hy htop hbottom hjoin
  apply kstQuasiCrossing_of_side_walks_meeting_connected_paths n m upper upperLink lower
    lowerLink leftWalk rightWalk hp hq hx hy hpOpen huOpen hqOpen hvOpen hlOpen hrOpen hleft hright
  intro side
  cases side
  · obtain ⟨z, hz, hwall⟩ := hrightMeet
    refine ⟨z, hwall, ?_⟩
    simpa only [Bool.false_eq_true, ↓reduceIte, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] using hz
  · obtain ⟨z, hz, hwall⟩ := hleftMeet
    exact ⟨z, hwall, by simpa using hz⟩

end Sandpile.External.RSW
