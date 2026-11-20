import Sandpile.External.RSW.RectangleCrossingIntersection
import Sandpile.External.RSW.WallGluing

/-!
# Quasi-crossings from a doubly connected path

A KST path connected to both horizontal sides meets each full horizontal crossing
through one of its three constituent walks.
-/

open Set

namespace Sandpile.External.RSW

/-- A KST path connected to both horizontal boundaries and a horizontal crossing give
both walls of a quasi-crossing. -/
theorem kstQuasiCrossing_of_doubly_connected_path (n m : ℕ)
    {ω : Sym2 (Site 2) → Bool}
    {a b x y bottom top left right : centeredPlaneRectangle (n + 3 * (n / 12)) n}
    (middle : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b)
    (lower : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk x bottom)
    (upper : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk y top)
    (horizontal : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk left right)
    (hp : IsKSTPath m middle) (hx : x ∈ middle.support) (hy : y ∈ middle.support)
    (hmid : IsBondOpenWalk ω middle) (hlow : IsBondOpenWalk ω lower)
    (hup : IsBondOpenWalk ω upper) (hhor : IsBondOpenWalk ω horizontal)
    (hbottom : (bottom : Site 2) 1 = -(n : ℤ)) (htop : (top : Site 2) 1 = n)
    (hleft : (left : Site 2) 0 = -((n + 3 * (n / 12) : ℕ) : ℤ))
    (hright : (right : Site 2) 0 = ((n + 3 * (n / 12) : ℕ) : ℤ)) :
    ω ∈ kstQuasiCrossingEvent n m := by
  obtain ⟨z, hzH, hz⟩ := centered_rectangle_crossing_intersects_connected_walks
    horizontal middle lower upper hx hy hleft hright hbottom htop
  have hwall (side : Bool) {u v : centeredPlaneRectangle (n + 3 * (n / 12)) n}
      (walk : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk u v)
      (hopen : IsBondOpenWalk ω walk)
      (hu : (u : Site 2) 0 = (if side then -((n + 3 * (n / 12) : ℕ) : ℤ)
        else ((n + 3 * (n / 12) : ℕ) : ℤ))) (hzw : z ∈ walk.support) :
      ω ∈ kstWallEvent n m side := by
    rcases hz with hzmid | hzlow | hzup
    · exact kstWallEvent_of_intersecting_walks n m side middle lower walk hp hx hmid hlow
        hopen hu ⟨z, Or.inl hzmid, hzw⟩
    · exact kstWallEvent_of_intersecting_walks n m side middle lower walk hp hx hmid hlow
        hopen hu ⟨z, Or.inr hzlow, hzw⟩
    · exact kstWallEvent_of_intersecting_walks n m side middle upper walk hp hy hmid hup
        hopen hu ⟨z, Or.inr hzup, hzw⟩
  exact ⟨hwall true horizontal hhor (by simpa using hleft) hzH,
    hwall false horizontal.reverse hhor.reverse (by simpa using hright)
      (by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzH)⟩

/-- Intersecting unions of two connected open walks join their attachment vertices. -/
theorem exists_openWalk_between_connected_walks {Q : Finset (Site 2)}
    {ω : Sym2 (Site 2) → Bool} {a b x d c e y f : Q}
    (first : (rectangleGraph Q).Walk a b) (firstLink : (rectangleGraph Q).Walk x d)
    (second : (rectangleGraph Q).Walk c e) (secondLink : (rectangleGraph Q).Walk y f)
    (hx : x ∈ first.support) (hy : y ∈ second.support)
    (hfirst : IsBondOpenWalk ω first) (hfirstLink : IsBondOpenWalk ω firstLink)
    (hsecond : IsBondOpenWalk ω second) (hsecondLink : IsBondOpenWalk ω secondLink)
    (hint : ∃ z, (z ∈ first.support ∨ z ∈ firstLink.support) ∧
      (z ∈ second.support ∨ z ∈ secondLink.support)) :
    ∃ walk : (rectangleGraph Q).Walk x y, IsBondOpenWalk ω walk := by
  obtain ⟨z, hzfirst, hzsecond⟩ := hint
  have hfirstJoin : ∃ walk : (rectangleGraph Q).Walk x z, IsBondOpenWalk ω walk := by
    rcases hzfirst with hz | hz
    · obtain ⟨walk, hw, _⟩ := exists_openWalk_of_mem_support first hfirst hx hz
      exact ⟨walk, hw⟩
    · obtain ⟨walk, hw, _⟩ := exists_openWalk_of_mem_support firstLink hfirstLink
        firstLink.start_mem_support hz
      exact ⟨walk, hw⟩
  have hsecondJoin : ∃ walk : (rectangleGraph Q).Walk z y, IsBondOpenWalk ω walk := by
    rcases hzsecond with hz | hz
    · obtain ⟨walk, hw, _⟩ := exists_openWalk_of_mem_support second hsecond hz hy
      exact ⟨walk, hw⟩
    · obtain ⟨walk, hw, _⟩ := exists_openWalk_of_mem_support secondLink hsecondLink
        hz secondLink.start_mem_support
      exact ⟨walk, hw⟩
  obtain ⟨firstWalk, hfirstWalk⟩ := hfirstJoin
  obtain ⟨secondWalk, hsecondWalk⟩ := hsecondJoin
  exact ⟨firstWalk.append secondWalk, hfirstWalk.append hsecondWalk⟩

/-- Intersecting top- and bottom-connected KST paths form both quasi-crossing walls
when there is an open horizontal crossing. -/
theorem kstQuasiCrossing_of_intersecting_vertical_connections (n m : ℕ)
    {ω : Sym2 (Site 2) → Bool}
    {a b x top c d y bottom left right : centeredPlaneRectangle (n + 3 * (n / 12)) n}
    (upperPath : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b)
    (upperLink : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk x top)
    (lowerPath : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk c d)
    (lowerLink : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk y bottom)
    (horizontal : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk left right)
    (hp : IsKSTPath m upperPath) (hx : x ∈ upperPath.support) (hy : y ∈ lowerPath.support)
    (hpOpen : IsBondOpenWalk ω upperPath) (htOpen : IsBondOpenWalk ω upperLink)
    (hqOpen : IsBondOpenWalk ω lowerPath) (hbOpen : IsBondOpenWalk ω lowerLink)
    (hhOpen : IsBondOpenWalk ω horizontal)
    (htop : (top : Site 2) 1 = n) (hbottom : (bottom : Site 2) 1 = -(n : ℤ))
    (hleft : (left : Site 2) 0 = -((n + 3 * (n / 12) : ℕ) : ℤ))
    (hright : (right : Site 2) 0 = ((n + 3 * (n / 12) : ℕ) : ℤ))
    (hint : ∃ z, (z ∈ upperPath.support ∨ z ∈ upperLink.support) ∧
      (z ∈ lowerPath.support ∨ z ∈ lowerLink.support)) :
    ω ∈ kstQuasiCrossingEvent n m := by
  obtain ⟨join, hjoin⟩ := exists_openWalk_between_connected_walks upperPath upperLink
    lowerPath lowerLink hx hy hpOpen htOpen hqOpen hbOpen hint
  exact kstQuasiCrossing_of_doubly_connected_path n m upperPath (join.append lowerLink)
    upperLink horizontal hp hx hx hpOpen (hjoin.append hbOpen) htOpen hhOpen
    hbottom htop hleft hright

end Sandpile.External.RSW
