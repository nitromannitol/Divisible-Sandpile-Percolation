import Sandpile.External.RSW.CorridorWallSeparation
import Sandpile.External.RSW.HorizontalWalk
import Sandpile.External.RSW.QuasiCrossing

/-!
# Boundary contacts between corridor walls

A vertical crossing avoiding structures attached to opposite sides meets the
horizontal segment joining any pair of their vertices at the same height.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Two vertices on one row of a centered rectangle are joined by a walk on that row. -/
theorem exists_centered_horizontal_walk {M N : ℕ} (u v : centeredPlaneRectangle M N)
    (huv : (u : Site 2) 0 ≤ (v : Site 2) 0) (hrow : (u : Site 2) 1 = (v : Site 2) 1) :
    ∃ w : (rectangleGraph (centeredPlaneRectangle M N)).Walk u v,
      ∀ z ∈ w.support, (u : Site 2) 0 ≤ (z : Site 2) 0 ∧
        (z : Site 2) 0 ≤ (v : Site 2) 0 ∧ (z : Site 2) 1 = (u : Site 2) 1 := by
  have hwExists := exists_horizontal_walk (u : Site 2) (v : Site 2) huv hrow
  rw [← lattice_eq_zdGraph] at hwExists
  obtain ⟨w, hw⟩ := hwExists
  have hu := (mem_centeredPlaneRectangle _ _ _).mp u.property
  have hv := (mem_centeredPlaneRectangle _ _ _).mp v.property
  have hwQ : ∀ z ∈ w.support, z ∈ (centeredPlaneRectangle M N : Set (Site 2)) := by
    intro z hz
    have h := hw z hz
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    omega
  let q := w.induce (centeredPlaneRectangle M N : Set (Site 2)) hwQ
  refine ⟨q, ?_⟩
  intro z hz
  have hz' : (z : Site 2) ∈ w.support := by
    change z ∈ (w.induce (centeredPlaneRectangle M N : Set (Site 2)) hwQ).support at hz
    have hm : (z : Site 2) ∈
        (w.induce (centeredPlaneRectangle M N : Set (Site 2)) hwQ).support.map Subtype.val :=
      List.mem_map.mpr ⟨z, hz, rfl⟩
    rw [SimpleGraph.Walk.support_induce, List.attachWith_map_subtype_val] at hm
    exact hm
  exact hw z hz'

/-- A crossing avoiding opposite-side structures meets the segment between their vertices. -/
theorem centered_crossing_meets_segment_between_attached_walks {M N : ℕ}
    {a b c d x left e f u right s t : centeredPlaneRectangle M N}
    (p : (rectangleGraph (centeredPlaneRectangle M N)).Walk a b)
    (r : (rectangleGraph (centeredPlaneRectangle M N)).Walk c d)
    (q : (rectangleGraph (centeredPlaneRectangle M N)).Walk x left)
    (r' : (rectangleGraph (centeredPlaneRectangle M N)).Walk e f)
    (q' : (rectangleGraph (centeredPlaneRectangle M N)).Walk u right)
    (ha : (a : Site 2) 1 = N) (hb : (b : Site 2) 1 = -(N : ℤ))
    (hx : x ∈ r.support) (hu : u ∈ r'.support)
    (hleft : (left : Site 2) 0 = -(M : ℤ)) (hright : (right : Site 2) 0 = M)
    (hs : s ∈ r.support ∨ s ∈ q.support)
    (ht : t ∈ r'.support ∨ t ∈ q'.support)
    (hrow : (s : Site 2) 1 = (t : Site 2) 1)
    (havoid : ∀ z ∈ p.support, z ∉ r.support ∧ z ∉ q.support ∧
      z ∉ r'.support ∧ z ∉ q'.support) :
    ∃ z ∈ p.support, (z : Site 2) 1 = (s : Site 2) 1 ∧
      (((s : Site 2) 0 ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ (t : Site 2) 0) ∨
       ((t : Site 2) 0 ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ (s : Site 2) 0)) := by
  by_cases hst : (s : Site 2) 0 ≤ (t : Site 2) 0
  · obtain ⟨w, hw⟩ := exists_centered_horizontal_walk s t hst hrow
    obtain ⟨z, hzp, hzw⟩ := centered_rectangle_connection_intersects_crossing
      p r q r' q' w ha hb hx hu hleft hright hs ht havoid
    have hz := hw z hzw
    exact ⟨z, hzp, hz.2.2, Or.inl ⟨hz.1, hz.2.1⟩⟩
  · obtain ⟨w, hw⟩ := exists_centered_horizontal_walk t s (by omega) hrow.symm
    obtain ⟨z, hzp, hzw⟩ := centered_rectangle_connection_intersects_crossing
      p r q r' q' w.reverse ha hb hx hu hleft hright hs ht havoid
    have hzw' : z ∈ w.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzw
    have hz := hw z hzw'
    exact ⟨z, hzp, hz.2.2.trans hrow.symm, Or.inr ⟨hz.1, hz.2.1⟩⟩

/-- An avoiding crossing meets both boundary segments joining the endpoints of two walls. -/
theorem centered_crossing_meets_kst_wall_endpoint_segments {M N k : ℕ}
    {a b c d x left e f u right : centeredPlaneRectangle M N}
    (p : (rectangleGraph (centeredPlaneRectangle M N)).Walk a b)
    (r : (rectangleGraph (centeredPlaneRectangle M N)).Walk c d)
    (q : (rectangleGraph (centeredPlaneRectangle M N)).Walk x left)
    (r' : (rectangleGraph (centeredPlaneRectangle M N)).Walk e f)
    (q' : (rectangleGraph (centeredPlaneRectangle M N)).Walk u right)
    (ha : (a : Site 2) 1 = N) (hb : (b : Site 2) 1 = -(N : ℤ))
    (hr : IsKSTPath k r) (hr' : IsKSTPath k r')
    (hx : x ∈ r.support) (hu : u ∈ r'.support)
    (hleft : (left : Site 2) 0 = -(M : ℤ)) (hright : (right : Site 2) 0 = M)
    (havoid : ∀ z ∈ p.support, z ∉ r.support ∧ z ∉ q.support ∧
      z ∉ r'.support ∧ z ∉ q'.support) :
    (∃ z ∈ p.support, (z : Site 2) 1 = k ∧
      (((c : Site 2) 0 ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ (e : Site 2) 0) ∨
       ((e : Site 2) 0 ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ (c : Site 2) 0))) ∧
    (∃ z ∈ p.support, (z : Site 2) 1 = -(k : ℤ) ∧
      (((d : Site 2) 0 ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ (f : Site 2) 0) ∨
       ((f : Site 2) 0 ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ (d : Site 2) 0))) := by
  constructor
  · obtain ⟨z, hzp, hzrow, hzorder⟩ := centered_crossing_meets_segment_between_attached_walks
      p r q r' q' ha hb hx hu hleft hright (Or.inl r.start_mem_support)
      (Or.inl r'.start_mem_support) (hr.2.1.trans hr'.2.1.symm) havoid
    exact ⟨z, hzp, hzrow.trans hr.2.1, hzorder⟩
  · obtain ⟨z, hzp, hzrow, hzorder⟩ := centered_crossing_meets_segment_between_attached_walks
      p r q r' q' ha hb hx hu hleft hright (Or.inl r.end_mem_support)
      (Or.inl r'.end_mem_support) (hr.2.2.1.trans hr'.2.2.1.symm) havoid
    exact ⟨z, hzp, hzrow.trans hr.2.2.1, hzorder⟩

end Sandpile.External.RSW
