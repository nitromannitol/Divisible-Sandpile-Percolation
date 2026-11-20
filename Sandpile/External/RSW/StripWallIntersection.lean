import Sandpile.External.RSW.ArcIntersection
import Sandpile.External.RSW.VerticalStripSubpath

/-!
# Strip paths and KST walls

A walk inside a scale rectangle that joins opposite boundary arcs intersects every
KST path at that scale. In particular, a strip path avoiding a wall cannot have its
endpoints on opposite sides of the target intervals.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- A walk joining opposite boundary arcs intersects a KST path. -/
theorem kstPath_intersects_boundary_walk {Q : Finset (Site 2)} {a b c d : Q}
    (p : (rectangleGraph Q).Walk a b) (q : (rectangleGraph Q).Walk c d)
    {k : ℕ} (hk : 0 < k) (hp : IsKSTPath k p)
    (hq : ∀ z ∈ q.support, (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k)
    (hc : (c : Site 2) 0 = -((k + k / 12 : ℕ) : ℤ) ∨
      ((c : Site 2) 0 ≤ -((k / 12 : ℕ) : ℤ) ∧
        ((c : Site 2) 1 = -(k : ℤ) ∨ (c : Site 2) 1 = k)))
    (hd : (d : Site 2) 0 = ((k + k / 12 : ℕ) : ℤ) ∨
      (((k / 12 : ℕ) : ℤ) ≤ (d : Site 2) 0 ∧
        ((d : Site 2) 1 = -(k : ℤ) ∨ (d : Site 2) 1 = k))) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  let f : rectangleGraph Q →g LatticeModels.zdGraph 2 :=
    ⟨Subtype.val, fun h => by rw [← lattice_eq_zdGraph]; exact h⟩
  have hpbox : ∀ z ∈ (p.map f).support,
      -((k + k / 12 : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ ((k + k / 12 : ℕ) : ℤ) ∧
        -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact (mem_centeredPlaneRectangle _ _ z').mp (hp.2.2.2.2.2.2.2 z' hz')
  have hqbox : ∀ z ∈ (q.map f).support,
      -((k + k / 12 : ℕ) : ℤ) ≤ z 0 ∧ z 0 ≤ ((k + k / 12 : ℕ) : ℤ) ∧
        -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact (mem_centeredPlaneRectangle _ _ z').mp (hq z' hz')
  have hL : -((k + k / 12 : ℕ) : ℤ) < -((k / 12 : ℕ) : ℤ) := by
    push_cast
    omega
  have hR : ((k / 12 : ℕ) : ℤ) < ((k + k / 12 : ℕ) : ℤ) := by
    push_cast
    omega
  have hBT : -(k : ℤ) < k := by omega
  obtain ⟨z, hzp, hzq⟩ := alternating_boundary_paths_intersect hL hR hBT
    (p.map f) (q.map f) hpbox hqbox
    ⟨hp.2.1, hp.2.2.2.1, hp.2.2.2.2.1⟩
    ⟨hp.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1⟩ hc hd
  rw [SimpleGraph.Walk.support_map] at hzp hzq
  obtain ⟨z₁, hz₁, he₁⟩ := List.mem_map.mp hzp
  obtain ⟨z₂, hz₂, he₂⟩ := List.mem_map.mp hzq
  have he : z₁ = z₂ := Subtype.ext (he₁.trans he₂.symm)
  subst z₂
  exact ⟨z₁, hz₁, hz₂⟩

/-- A strip walk with endpoints on opposite sides of the targets meets a KST path. -/
theorem kstPath_intersects_strip_walk_of_opposite_targets
    {Q : Finset (Site 2)} {a b c d : Q}
    (p : (rectangleGraph Q).Walk a b) (q : (rectangleGraph Q).Walk c d)
    {k : ℕ} (hk : 0 < k) (hp : IsKSTPath k p)
    (hq : ∀ z ∈ q.support, (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k)
    (hc : (c : Site 2) 1 = k) (hd : (d : Site 2) 1 = -(k : ℤ))
    (hside : ((c : Site 2) 0 ≤ -((k / 12 : ℕ) : ℤ) ∧
        ((k / 12 : ℕ) : ℤ) ≤ (d : Site 2) 0) ∨
      (((k / 12 : ℕ) : ℤ) ≤ (c : Site 2) 0 ∧
        (d : Site 2) 0 ≤ -((k / 12 : ℕ) : ℤ))) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  rcases hside with h | h
  · exact kstPath_intersects_boundary_walk p q hk hp hq
      (Or.inr ⟨h.1, Or.inr hc⟩) (Or.inr ⟨h.2, Or.inl hd⟩)
  · have hqrev : ∀ z ∈ q.reverse.support,
        (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k := by
      intro z hz
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
      exact hq z hz
    obtain ⟨z, hzp, hzq⟩ := kstPath_intersects_boundary_walk p q.reverse hk hp hqrev
      (Or.inr ⟨h.2, Or.inl hd⟩) (Or.inr ⟨h.1, Or.inr hc⟩)
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hzq
    exact ⟨z, hzp, hzq⟩

end Sandpile.External.RSW
