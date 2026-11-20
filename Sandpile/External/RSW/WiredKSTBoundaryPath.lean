import Sandpile.External.RSW.WiredKSTCentralBoundary
import Sandpile.External.RSW.PathLeaf
import Sandpile.External.RSW.BondWalk

/-!
# Simple dual paths near wired boundaries

A simple open dual path cannot visit a central wired-boundary vertex in its
interior, because that vertex has at most one available neighbor.
-/

namespace Sandpile.External.RSW

/-- A central wired-boundary vertex on a simple open dual path is an endpoint. -/
theorem IsBondOpenWalk.wiredKST_dual_central_boundary_eq_endpoint
    (m : ℕ) (ω : Sym2 (Site 2) → Bool) {Q : Finset (Site 2)} {a b z : Q}
    (p : (rectangleGraph Q).Walk a b) (hpath : p.IsPath)
    (hp : IsBondOpenWalk (dualBondConfig (wiredKSTConfig m ω)) p)
    (hs : ∀ v ∈ p.support, -((m : ℤ) + 1) ≤ (v : Site 2) 1 ∧ (v : Site 2) 1 ≤ m)
    (hz : z ∈ p.support)
    (hrow : (z : Site 2) 1 = -((m : ℤ) + 1) ∨ (z : Site 2) 1 = m)
    (hl : -((m / 12 : ℕ) : ℤ) ≤ (z : Site 2) 0)
    (hu : (z : Site 2) 0 < m / 12) : z = a ∨ z = b := by
  let E : Set (Sym2 Q) := {e | (∀ v ∈ e, -((m : ℤ) + 1) ≤ (v : Site 2) 1 ∧
    (v : Site 2) 1 ≤ m) ∧ dualBondConfig (wiredKSTConfig m ω) (Sym2.map Subtype.val e) = true}
  have hedges : ∀ e ∈ p.edges, e ∈ E := by
    intro e he
    refine ⟨?_, (isBondOpenWalk_iff_local_edges _ p).mp hp e he⟩
    intro v hv
    exact hs v (SimpleGraph.Walk.mem_support_of_mem_edges he hv)
  apply SimpleGraph.Walk.IsPath.eq_endpoint_of_unique_neighbor hpath hz E hedges
  intro x y hzx hzy hx hy
  have hxBound := hx.1 x (by simp only [Sym2.mem_iff, or_true])
  have hyBound := hy.1 y (by simp only [Sym2.mem_iff, or_true])
  have hxopen : dualBondConfig (wiredKSTConfig m ω) s((z : Site 2), (x : Site 2)) = true :=
    hx.2
  have hyopen : dualBondConfig (wiredKSTConfig m ω) s((z : Site 2), (y : Site 2)) = true :=
    hy.2
  rcases hrow with hrow | hrow
  · have hx' := wiredKST_dual_lower_central_neighbor m ω hzx hrow hxBound.1 hl hu hxopen
    have hy' := wiredKST_dual_lower_central_neighbor m ω hzy hrow hyBound.1 hl hu hyopen
    apply Subtype.ext
    exact hx'.trans hy'.symm
  · have hx' := wiredKST_dual_upper_central_neighbor m ω hzx hrow hxBound.2 hl hu hxopen
    have hy' := wiredKST_dual_upper_central_neighbor m ω hzy hrow hyBound.2 hl hu hyopen
    apply Subtype.ext
    exact hx'.trans hy'.symm

end Sandpile.External.RSW
