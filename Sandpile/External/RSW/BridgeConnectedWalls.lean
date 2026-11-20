import Sandpile.External.RSW.ConnectedCorridorWalls
import Sandpile.External.RSW.BoundaryExtension

/-!
# A bridge joining attached walls

A bridge joining two connected wall structures produces a horizontal crossing,
which intersects every vertical crossing of the same rectangle.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- A point in two attached walks is connected to the attachment endpoint. -/
theorem exists_walk_in_attached_graph_walks {V : Type*} {G : SimpleGraph V}
    {a b x y z : V} (p : G.Walk a b) (q : G.Walk x y)
    (hx : x ∈ p.support) (hz : z ∈ p.support ∨ z ∈ q.support) :
    ∃ w : G.Walk y z, ∀ t ∈ w.support, t ∈ p.support ∨ t ∈ q.support := by
  classical
  rcases hz with hp | hq
  · let w := q.reverse.append ((p.takeUntil x hx).reverse.append (p.takeUntil z hp))
    refine ⟨w, ?_⟩
    intro t ht
    change t ∈ (q.reverse.append ((p.takeUntil x hx).reverse.append (p.takeUntil z hp))).support at ht
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at ht
    rcases ht with ht | ht | ht
    · exact Or.inr ht
    · exact Or.inl (p.support_takeUntil_subset_support hx ht)
    · exact Or.inl (p.support_takeUntil_subset_support hp ht)
  · have hz' : z ∈ q.reverse.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hq
    refine ⟨q.reverse.takeUntil z hz', ?_⟩
    intro t ht
    right
    have ht' := q.reverse.support_takeUntil_subset_support hz' ht
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using ht'

/-- A bridge between attached walls meets every vertical crossing of their rectangle. -/
theorem vertical_crossing_intersects_bridged_walls {L R B T : ℤ}
    {a b c d x y e f u v s t : Site 2}
    (p : (LatticeModels.zdGraph 2).Walk a b)
    (left : (LatticeModels.zdGraph 2).Walk c d)
    (leftLink : (LatticeModels.zdGraph 2).Walk x y)
    (right : (LatticeModels.zdGraph 2).Walk e f)
    (rightLink : (LatticeModels.zdGraph 2).Walk u v)
    (bridge : (LatticeModels.zdGraph 2).Walk s t)
    (hp : ∀ z ∈ p.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hl : ∀ z ∈ left.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hll : ∀ z ∈ leftLink.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hr : ∀ z ∈ right.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hrl : ∀ z ∈ rightLink.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hbr : ∀ z ∈ bridge.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (ha : a 1 = T) (hb : b 1 = B) (hx : x ∈ left.support) (hu : u ∈ right.support)
    (hy : y 0 = L) (hv : v 0 = R)
    (hleft : ∃ z, z ∈ left.support ∧ z ∈ bridge.support)
    (hright : ∃ z, z ∈ right.support ∧ z ∈ bridge.support) :
    ∃ z, z ∈ p.support ∧ (z ∈ left.support ∨ z ∈ leftLink.support ∨
      z ∈ bridge.support ∨ z ∈ right.support ∨ z ∈ rightLink.support) := by
  classical
  obtain ⟨z₁, hz₁, hz₁b⟩ := hleft
  obtain ⟨z₂, hz₂, hz₂b⟩ := hright
  obtain ⟨wl, hwl⟩ := exists_walk_in_attached_graph_walks left leftLink hx (Or.inl hz₁)
  obtain ⟨wr, hwr⟩ := exists_walk_in_attached_graph_walks right rightLink hu (Or.inl hz₂)
  let middle := (bridge.takeUntil z₁ hz₁b).reverse.append (bridge.takeUntil z₂ hz₂b)
  let w := wl.append (middle.append wr.reverse)
  have hmiddle : ∀ z ∈ middle.support, z ∈ bridge.support := by
    intro z hz
    change z ∈ ((bridge.takeUntil z₁ hz₁b).reverse.append (bridge.takeUntil z₂ hz₂b)).support at hz
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hz
    rcases hz with hz | hz
    · exact bridge.support_takeUntil_subset_support hz₁b hz
    · exact bridge.support_takeUntil_subset_support hz₂b hz
  have hw : ∀ z ∈ w.support, z ∈ left.support ∨ z ∈ leftLink.support ∨
      z ∈ bridge.support ∨ z ∈ right.support ∨ z ∈ rightLink.support := by
    intro z hz
    change z ∈ (wl.append (middle.append wr.reverse)).support at hz
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hz
    rcases hz with hz | hz | hz
    · rcases hwl z hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl (hmiddle z hz)))
    · rcases hwr z hz with hz | hz
      · exact Or.inr (Or.inr (Or.inr (Or.inl hz)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hz)))
  have hwbox : ∀ z ∈ w.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T := by
    intro z hz
    rcases hw z hz with hz | hz | hz | hz | hz
    · exact hl z hz
    · exact hll z hz
    · exact hbr z hz
    · exact hr z hz
    · exact hrl z hz
  have hpbox : ∀ z ∈ p.reverse.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T := by
    intro z hz
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    exact hp z hz
  obtain ⟨z, hzw, hzp⟩ := exists_mem_support_of_crossing w p.reverse hwbox hpbox hy hv hb ha
  have hzp' : z ∈ p.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzp
  exact ⟨z, hzp', hw z hzw⟩

end Sandpile.External.RSW
