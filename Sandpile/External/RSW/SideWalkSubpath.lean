import Sandpile.External.RSW.QuasiCascadeCover

/-!
# Walls from side walks containing KST paths

An open walk from a side of the quasi-crossing rectangle supplies a wall whenever it
contains a KST subpath. This is one of the alternatives in the corridor argument.
-/

open Set

namespace Sandpile.External.RSW

/-- An open side walk containing a KST subpath supplies the corresponding wall. -/
theorem kstWallEvent_of_side_walk_has_subpath (n m : ℕ) (left : Bool)
    {ω : Sym2 (Site 2) → Bool}
    {a b : centeredPlaneRectangle (n + 3 * (n / 12)) n}
    (p : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b)
    (hp : IsBondOpenWalk ω p) (hsub : HasKSTSubpath m p)
    (ha : (a : Site 2) 0 = (if left then -((n + 3 * (n / 12) : ℕ) : ℤ)
      else ((n + 3 * (n / 12) : ℕ) : ℤ))) :
    ω ∈ kstWallEvent n m left := by
  obtain ⟨c, d, q, hqp, hq⟩ := hsub
  have hc : c ∈ p.support := hqp.support_subset q.start_mem_support
  obtain ⟨r, hr, _⟩ := exists_openWalk_of_mem_support p hp hc p.start_mem_support
  exact ⟨c, d, c, a, q, r, hq, q.start_mem_support, ha, hp.subwalk hqp, hr⟩

/-- Side walks that both contain KST subpaths supply a quasi-crossing. -/
theorem kstQuasiCrossing_of_side_walks_have_subpaths (n m : ℕ)
    {ω : Sym2 (Site 2) → Bool}
    {a b c d : centeredPlaneRectangle (n + 3 * (n / 12)) n}
    (p : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b)
    (q : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk c d)
    (hp : IsBondOpenWalk ω p) (hq : IsBondOpenWalk ω q)
    (hpsub : HasKSTSubpath m p) (hqsub : HasKSTSubpath m q)
    (ha : (a : Site 2) 0 = -((n + 3 * (n / 12) : ℕ) : ℤ))
    (hc : (c : Site 2) 0 = ((n + 3 * (n / 12) : ℕ) : ℤ)) :
    ω ∈ kstQuasiCrossingEvent n m :=
  ⟨kstWallEvent_of_side_walk_has_subpath n m true p hp hpsub (by simpa using ha),
    kstWallEvent_of_side_walk_has_subpath n m false q hq hqsub (by simpa using hc)⟩

end Sandpile.External.RSW
