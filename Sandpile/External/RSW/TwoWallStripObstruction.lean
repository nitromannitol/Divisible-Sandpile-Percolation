import Sandpile.External.RSW.StripWallOrder
import Sandpile.External.RSW.StripPathObstruction

/-!
# Strip subpaths avoiding two walls

A path avoiding two KST walls either has a smaller KST subpath or has a strip
subpath that leaves the scale box or begins outside the two upper wall endpoints.
-/

namespace Sandpile.External.RSW

/-- A path with no KST subpath has a strip segment obstructed by the box or upper endpoints. -/
theorem exists_strip_two_wall_obstruction {Q : Finset (Site 2)}
    {a b c d e f : Q} (p : (rectangleGraph Q).Walk a b)
    (left : (rectangleGraph Q).Walk c d) (right : (rectangleGraph Q).Walk e f)
    {k : ℕ} (hk : 0 < k) (hpath : p.IsPath)
    (hleft : IsKSTPath k left) (hright : IsKSTPath k right)
    (ha : (k : ℤ) ≤ (a : Site 2) 1) (hb : (b : Site 2) 1 ≤ -(k : ℤ))
    (hl : ∀ z ∈ p.support, z ∉ left.support)
    (hr : ∀ z ∈ p.support, z ∉ right.support)
    (hbad : ¬ HasKSTSubpath k p) :
    ∃ (u v : Q) (q : (rectangleGraph Q).Walk u v),
      q.IsSubwalk p ∧ q.IsPath ∧ (u : Site 2) 1 = k ∧ (v : Site 2) 1 = -(k : ℤ) ∧
      (∀ z ∈ q.support, -(k : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k) ∧
      (∀ z ∈ q.support, ((z : Site 2) 1 = k → z = u) ∧
        ((z : Site 2) 1 = -(k : ℤ) → z = v)) ∧
      ((∃ z ∈ q.support, (z : Site 2) ∉ centeredPlaneRectangle (k + k / 12) k) ∨
        (u : Site 2) 0 < (c : Site 2) 0 ∨ (e : Site 2) 0 < (u : Site 2) 0) := by
  obtain ⟨u, v, q, hsub, hqpath, hu, hv, hstrip, hboundary⟩ :=
    exists_vertical_strip_subpath_with_boundary p hpath (B := -(k : ℤ)) (T := k)
      (by omega) ha hb
  refine ⟨u, v, q, hsub, hqpath, hu, hv, hstrip, hboundary, ?_⟩
  by_contra hn
  push Not at hn
  apply hbad
  refine ⟨u, v, q, hsub, ?_⟩
  apply isKSTPath_of_strip_walk_between_walls q left right hk hqpath hleft hright hn.1 hu hv
  · intro z hz
    exact hl z (hsub.support_subset hz)
  · intro z hz
    exact hr z (hsub.support_subset hz)
  · omega
  · omega

end Sandpile.External.RSW
