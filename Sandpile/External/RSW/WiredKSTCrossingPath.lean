import Sandpile.External.RSW.WiredKSTDualWalk
import Sandpile.External.RSW.WiredKSTBoundaryPath

/-!
# A simple wired dual crossing

Loop erasure yields a dual path across the enlarged rectangle, and its central
vertices avoid the two wired boundary rows.
-/

namespace Sandpile.External.RSW

/-- An exceptional path yields a simple wired dual crossing avoiding the central boundary. -/
theorem exists_wiredKST_dual_crossing_path_of_no_subpath (m : ℕ) (hm : 0 < m)
    {Q : Finset (Site 2)} {u v : Q} (r : (rectangleGraph Q).Walk u v)
    (hr : r.IsPath) (hsub : ¬ HasKSTSubpath m r)
    (hsubrev : ¬ HasKSTSubpath m r.reverse)
    (hQR : centeredPlaneRectangle (m + m / 12) (m + 1) ⊆ Q) :
    ∃ (a b : centeredPlaneRectangle (m + m / 12 + 1) (m + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (m + m / 12 + 1) (m + 1))).Walk a b),
      p.IsPath ∧ IsBondOpenWalk (dualBondConfig (wiredKSTConfig m (pathBondConfig r))) p ∧
      (a : Site 2) 0 = -((m + m / 12 : ℕ) : ℤ) - 1 ∧
      (b : Site 2) 0 = ((m + m / 12 : ℕ) : ℤ) ∧
      (∀ z ∈ p.support, -((m + m / 12 : ℕ) : ℤ) - 1 ≤ (z : Site 2) 0 ∧
        (z : Site 2) 0 ≤ ((m + m / 12 : ℕ) : ℤ) ∧
        -((m : ℤ) + 1) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m) ∧
      ∀ z ∈ p.support, -((m / 12 : ℕ) : ℤ) ≤ (z : Site 2) 0 →
        (z : Site 2) 0 < ((m / 12 : ℕ) : ℤ) →
        -((m : ℤ) + 1) < (z : Site 2) 1 ∧ (z : Site 2) 1 < m := by
  obtain ⟨a, b, p, hpath, hpopen, ha, hb, hs⟩ :=
    exists_wiredKST_dual_walk_of_no_subpath m hm r hr hsub hsubrev hQR
  have hys : ∀ z ∈ p.support,
      -((m : ℤ) + 1) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m := by
    intro z hz
    have hz' := hs z hz
    push_cast at hz'
    exact ⟨hz'.2.2.1, hz'.2.2.2⟩
  refine ⟨a, b, p, hpath, hpopen, ha, hb, ?_, ?_⟩
  · intro z hz
    have hz' := hs z hz
    push_cast at hz'
    exact hz'
  · intro z hz hl hu
    have hy := hys z hz
    have hrow : (z : Site 2) 1 ≠ -((m : ℤ) + 1) ∧ (z : Site 2) 1 ≠ m := by
      constructor <;> intro hr
      · have he := hpopen.wiredKST_dual_central_boundary_eq_endpoint m (pathBondConfig r) p hpath hys hz
          (Or.inl hr) hl hu
        rcases he with he | he <;> subst z <;> push_cast at * <;> omega
      · have he := hpopen.wiredKST_dual_central_boundary_eq_endpoint m (pathBondConfig r) p hpath hys hz
          (Or.inr hr) hl hu
        rcases he with he | he <;> subst z <;> push_cast at * <;> omega
    omega

end Sandpile.External.RSW
