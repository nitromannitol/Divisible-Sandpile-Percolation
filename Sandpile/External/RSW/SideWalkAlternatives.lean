import Sandpile.External.RSW.SideWalkSubpath
import Sandpile.External.RSW.WallGluing

/-!
# Side-walk alternatives for quasi-crossings

Each side walk may independently contain a KST subpath or meet an open walk
connected to a KST path. Either alternative supplies the corresponding wall.
-/

open Set

namespace Sandpile.External.RSW

/-- A walk meets an open KST path or an open walk starting on one. -/
def HasKSTContact {Q : Finset (Site 2)} (ω : Sym2 (Site 2) → Bool) (m : ℕ)
    {s t : Q} (walk : (rectangleGraph Q).Walk s t) : Prop :=
  ∃ (a b x y : Q) (path : (rectangleGraph Q).Walk a b)
    (link : (rectangleGraph Q).Walk x y),
    IsKSTPath m path ∧ x ∈ path.support ∧ IsBondOpenWalk ω path ∧
      IsBondOpenWalk ω link ∧
      ∃ z, (z ∈ path.support ∨ z ∈ link.support) ∧ z ∈ walk.support

/-- Either side-walk alternative supplies the corresponding wall. -/
theorem kstWallEvent_of_side_walk_alternatives (n m : ℕ) (left : Bool)
    {ω : Sym2 (Site 2) → Bool}
    {a b : centeredPlaneRectangle (n + 3 * (n / 12)) n}
    (walk : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b)
    (hopen : IsBondOpenWalk ω walk)
    (ha : (a : Site 2) 0 = (if left then -((n + 3 * (n / 12) : ℕ) : ℤ)
      else ((n + 3 * (n / 12) : ℕ) : ℤ)))
    (halt : HasKSTSubpath m walk ∨ HasKSTContact ω m walk) :
    ω ∈ kstWallEvent n m left := by
  rcases halt with hsub | ⟨_, _, _, _, path, link, hp, hx, hpOpen, hlOpen, hint⟩
  · exact kstWallEvent_of_side_walk_has_subpath n m left walk hopen hsub ha
  · exact kstWallEvent_of_intersecting_walks n m left path link walk hp hx
      hpOpen hlOpen hopen ha hint

/-- The two side walks may use different alternatives to form a quasi-crossing. -/
theorem kstQuasiCrossing_of_side_walk_alternatives (n m : ℕ)
    {ω : Sym2 (Site 2) → Bool}
    {a b c d : centeredPlaneRectangle (n + 3 * (n / 12)) n}
    (leftWalk : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b)
    (rightWalk : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk c d)
    (hlOpen : IsBondOpenWalk ω leftWalk) (hrOpen : IsBondOpenWalk ω rightWalk)
    (ha : (a : Site 2) 0 = -((n + 3 * (n / 12) : ℕ) : ℤ))
    (hc : (c : Site 2) 0 = ((n + 3 * (n / 12) : ℕ) : ℤ))
    (hl : HasKSTSubpath m leftWalk ∨ HasKSTContact ω m leftWalk)
    (hr : HasKSTSubpath m rightWalk ∨ HasKSTContact ω m rightWalk) :
    ω ∈ kstQuasiCrossingEvent n m :=
  ⟨kstWallEvent_of_side_walk_alternatives n m true leftWalk hlOpen (by simpa using ha) hl,
    kstWallEvent_of_side_walk_alternatives n m false rightWalk hrOpen (by simpa using hc) hr⟩

end Sandpile.External.RSW
