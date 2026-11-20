import Sandpile.External.RSW.BridgeConnectedWalls
import Sandpile.External.RSW.DualSwap

/-!
# Horizontal crossings and bridged walls

A bridge joining bottom- and top-attached walls forms a vertical crossing and
meets every horizontal crossing of the enclosing rectangle.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- A horizontal crossing meets a bridge joining bottom- and top-attached walls. -/
theorem horizontal_crossing_intersects_bridged_walls {L R B T : ℤ}
    {a b c d x y e f u v s t : Site 2}
    (p : (LatticeModels.zdGraph 2).Walk a b)
    (lower : (LatticeModels.zdGraph 2).Walk c d)
    (lowerLink : (LatticeModels.zdGraph 2).Walk x y)
    (upper : (LatticeModels.zdGraph 2).Walk e f)
    (upperLink : (LatticeModels.zdGraph 2).Walk u v)
    (bridge : (LatticeModels.zdGraph 2).Walk s t)
    (hp : ∀ z ∈ p.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hl : ∀ z ∈ lower.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hll : ∀ z ∈ lowerLink.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hu : ∀ z ∈ upper.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hul : ∀ z ∈ upperLink.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hbr : ∀ z ∈ bridge.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (ha : a 0 = R) (hb : b 0 = L) (hx : x ∈ lower.support) (hw : u ∈ upper.support)
    (hy : y 1 = B) (hv : v 1 = T)
    (hfirst : ∃ z, z ∈ lower.support ∧ z ∈ bridge.support)
    (hsecond : ∃ z, z ∈ upper.support ∧ z ∈ bridge.support) :
    ∃ z, z ∈ p.support ∧ (z ∈ lower.support ∨ z ∈ lowerLink.support ∨
      z ∈ bridge.support ∨ z ∈ upper.support ∨ z ∈ upperLink.support) := by
  let swap : LatticeModels.zdGraph 2 →g LatticeModels.zdGraph 2 :=
    ⟨swapPlaneSite, fun h => by
      rw [← lattice_eq_zdGraph] at h ⊢
      exact lattice_adj_swap_plane h⟩
  have hbox {i j : Site 2} (w : (LatticeModels.zdGraph 2).Walk i j)
      (hw : ∀ z ∈ w.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T) :
      ∀ z ∈ (w.map swap).support, B ≤ z 0 ∧ z 0 ≤ T ∧ L ≤ z 1 ∧ z 1 ≤ R := by
    intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have h := hw z' hz'
    change B ≤ z' 1 ∧ z' 1 ≤ T ∧ L ≤ z' 0 ∧ z' 0 ≤ R
    omega
  have hint {i j i' j' : Site 2} (w : (LatticeModels.zdGraph 2).Walk i j)
      (w' : (LatticeModels.zdGraph 2).Walk i' j')
      (h : ∃ z, z ∈ w.support ∧ z ∈ w'.support) :
      ∃ z, z ∈ (w.map swap).support ∧ z ∈ (w'.map swap).support := by
    obtain ⟨z, hz, hz'⟩ := h
    refine ⟨swap z, ?_, ?_⟩ <;> rw [SimpleGraph.Walk.support_map, List.mem_map]
    · exact ⟨z, hz, rfl⟩
    · exact ⟨z, hz', rfl⟩
  have hx' : swap x ∈ (lower.map swap).support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨x, hx, rfl⟩
  have hu' : swap u ∈ (upper.map swap).support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨u, hw, rfl⟩
  obtain ⟨z, hzp, hz⟩ := vertical_crossing_intersects_bridged_walls
    (L := B) (R := T) (B := L) (T := R)
    (p.map swap) (lower.map swap) (lowerLink.map swap) (upper.map swap)
    (upperLink.map swap) (bridge.map swap) (hbox p hp) (hbox lower hl)
    (hbox lowerLink hll) (hbox upper hu) (hbox upperLink hul) (hbox bridge hbr)
    ha hb hx' hu' hy hv (hint lower bridge hfirst) (hint upper bridge hsecond)
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hzp
  obtain ⟨z', hz', hze⟩ := hzp
  subst z
  refine ⟨z', hz', ?_⟩
  rcases hz with hz | hz | hz | hz | hz
  all_goals
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, he⟩ := hz
    have hwz : w = z' := by
      change swapPlaneSite w = swapPlaneSite z' at he
      exact swapPlaneSite_involutive.injective he
    subst w
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hw)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hw)))

end Sandpile.External.RSW
