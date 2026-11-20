import Sandpile.External.RSW.HorizontalStripSubpath
import Sandpile.External.RSW.RectangleCrossingIntersection

/-!
# Crossings of an embedded rectangle

A horizontal walk that spans a smaller centered rectangle meets every vertical
crossing contained in that rectangle.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- A horizontal walk spanning a rectangle meets a vertical crossing inside it. -/
theorem horizontal_walk_intersects_embedded_vertical_crossing
    {Q : Finset (Site 2)} {a b c d : Q} {M N : ℕ} (hM : 0 < M)
    (horizontal : (rectangleGraph Q).Walk a b)
    (vertical : (rectangleGraph Q).Walk c d)
    (ha : (a : Site 2) 0 ≤ -(M : ℤ)) (hb : (M : ℤ) ≤ (b : Site 2) 0)
    (hhor : ∀ z ∈ horizontal.support, -(N : ℤ) ≤ (z : Site 2) 1 ∧
      (z : Site 2) 1 ≤ N)
    (hver : ∀ z ∈ vertical.support,
      (z : Site 2) ∈ centeredPlaneRectangle M N)
    (hc : (c : Site 2) 1 = -(N : ℤ)) (hd : (d : Site 2) 1 = N) :
    ∃ z, z ∈ horizontal.support ∧ z ∈ vertical.support := by
  let simple := horizontal.bypass
  obtain ⟨u, v, p, hpSub, _, hu, hv, hpBox, _⟩ :=
    exists_horizontal_strip_subpath simple horizontal.bypass_isPath
      (L := -(M : ℤ)) (R := M) (by omega) ha hb
  let f : rectangleGraph Q →g LatticeModels.zdGraph 2 :=
    ⟨Subtype.val, fun h => by rw [← lattice_eq_zdGraph]; exact h⟩
  have hpSupport : ∀ z ∈ p.support, z ∈ horizontal.support := by
    intro z hz
    exact horizontal.support_bypass_subset_support (hpSub.support_subset hz)
  have hpBounds : ∀ z ∈ (p.map f).support,
      -(M : ℤ) ≤ z 0 ∧ z 0 ≤ M ∧ -(N : ℤ) ≤ z 1 ∧ z 1 ≤ N := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact ⟨(hpBox z' hz').1, (hpBox z' hz').2, (hhor z' (hpSupport z' hz')).1,
      (hhor z' (hpSupport z' hz')).2⟩
  have hvBounds : ∀ z ∈ (vertical.map f).support,
      -(M : ℤ) ≤ z 0 ∧ z 0 ≤ M ∧ -(N : ℤ) ≤ z 1 ∧ z 1 ≤ N := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact (mem_centeredPlaneRectangle _ _ _).mp (hver z' hz')
  obtain ⟨z, hzH, hzV⟩ := exists_mem_support_of_crossing
    (p.map f) (vertical.map f) hpBounds hvBounds hu hv hc hd
  rw [SimpleGraph.Walk.support_map] at hzH hzV
  obtain ⟨x, hx, hxz⟩ := List.mem_map.mp hzH
  obtain ⟨y, hy, hyz⟩ := List.mem_map.mp hzV
  have hxy : x = y := Subtype.ext (hxz.trans hyz.symm)
  exact ⟨x, hpSupport x hx, hxy ▸ hy⟩

end Sandpile.External.RSW
