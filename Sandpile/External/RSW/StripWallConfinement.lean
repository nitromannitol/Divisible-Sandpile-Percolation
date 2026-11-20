import Sandpile.External.RSW.OrderedArcIntersection
import Sandpile.External.RSW.VerticalStripSubpath

/-!
# Confinement between vertical walls

A strip walk that begins between two vertical walls and avoids them stays inside
their common bounding rectangle.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- A strip walk beginning between two walls cannot reach either side of their box. -/
theorem strip_walk_bounded_between_walls {L R B T : ℤ} (hBT : B < T)
    {a b c d u v : Site 2}
    (left : (LatticeModels.zdGraph 2).Walk a b)
    (right : (LatticeModels.zdGraph 2).Walk c d)
    (p : (LatticeModels.zdGraph 2).Walk u v)
    (hlbox : ∀ z ∈ left.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hrbox : ∀ z ∈ right.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hpstrip : ∀ z ∈ p.support, B ≤ z 1 ∧ z 1 ≤ T)
    (ha : a 1 = T) (hb : b 1 = B) (hc : c 1 = T) (hd : d 1 = B)
    (hu : u 1 = T) (hleft : L < a 0) (hright : c 0 < R)
    (huLeft : a 0 ≤ u 0) (huRight : u 0 ≤ c 0)
    (hdisL : ∀ z ∈ p.support, z ∉ left.support)
    (hdisR : ∀ z ∈ p.support, z ∉ right.support) :
    ∀ z ∈ p.support, L ≤ z 0 ∧ z 0 ≤ R := by
  classical
  have huL : L ≤ u 0 := by omega
  have huR : u 0 ≤ R := by omega
  let O : Set (Site 2) := {z | z 0 = L ∨ z 0 = R}
  have hno : ∀ z ∈ p.support, z ∉ O := by
    intro z hz hzO
    obtain ⟨w, hwO, q, hqs, _, hqd⟩ := exists_prefix_first_mem (O := O) p ⟨z, hz, hzO⟩
    have hqL : ∀ z ∈ q.support, L ≤ z 0 :=
      apply_ge_of_darts q 0 L huL (fun d hd he => hqd d hd (Or.inl he))
    have hqR : ∀ z ∈ q.support, z 0 ≤ R :=
      apply_le_of_darts q 0 R huR (fun d hd he => hqd d hd (Or.inr he))
    have hqbox : ∀ z ∈ q.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T := by
      intro z hz
      exact ⟨hqL z hz, hqR z hz, hpstrip z (hqs z hz)⟩
    rcases hwO with hw | hw
    · have hqrbox : ∀ z ∈ q.reverse.support,
          L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T := by
        intro z hz
        rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
        exact hqbox z hz
      obtain ⟨t, htl, htq⟩ := vertical_walk_intersects_ordered_boundary_walk hBT left q.reverse
        hlbox hqrbox ha hb (Or.inl hw) (Or.inr (Or.inr ⟨hu, huLeft⟩))
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at htq
      exact hdisL t (hqs t htq) htl
    · obtain ⟨t, htr, htq⟩ := vertical_walk_intersects_ordered_boundary_walk hBT right q
        hrbox hqbox hc hd (Or.inr (Or.inl ⟨hu, huRight⟩)) (Or.inl hw)
      exact hdisR t (hqs t htq) htr
  have hpL : ∀ z ∈ p.support, L ≤ z 0 :=
    apply_ge_of_darts p 0 L huL (fun d hd he =>
      hno d.fst (p.dart_fst_mem_support_of_mem_darts hd) (Or.inl he))
  have hpR : ∀ z ∈ p.support, z 0 ≤ R :=
    apply_le_of_darts p 0 R huR (fun d hd he =>
      hno d.fst (p.dart_fst_mem_support_of_mem_darts hd) (Or.inr he))
  exact fun z hz => ⟨hpL z hz, hpR z hz⟩

end Sandpile.External.RSW
