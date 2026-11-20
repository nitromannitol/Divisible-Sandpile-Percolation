import Sandpile.External.RSW.DisjointCorridorWalls

/-!
# Corridors at small scales

When the scale is below twelve, the two paths forming the corridor walls share
their upper endpoint. Every vertical crossing therefore meets a wall.
-/

open LatticeProb

namespace Sandpile.External.RSW

/-- Below scale twelve, two KST paths have the same upper endpoint. -/
theorem kstPaths_share_upper_endpoint {Q : Finset (Site 2)} {a b c d : Q}
    (p : (rectangleGraph Q).Walk a b) (q : (rectangleGraph Q).Walk c d)
    {k : ℕ} (hk : k < 12) (hp : IsKSTPath k p) (hq : IsKSTPath k q) :
    a = c := by
  have hdiv : k / 12 = 0 := Nat.div_eq_of_lt hk
  have hax : (a : Site 2) 0 = 0 := by
    have h₁ := hp.2.2.2.1
    have h₂ := hp.2.2.2.2.1
    simp only [hdiv, Nat.cast_zero, neg_zero] at h₁ h₂
    omega
  have hcx : (c : Site 2) 0 = 0 := by
    have h₁ := hq.2.2.2.1
    have h₂ := hq.2.2.2.2.1
    simp only [hdiv, Nat.cast_zero, neg_zero] at h₁ h₂
    omega
  apply Subtype.ext
  funext i
  fin_cases i
  · change (a : Site 2) 0 = (c : Site 2) 0
    omega
  · change (a : Site 2) 1 = (c : Site 2) 1
    have h₁ := hp.2.1
    have h₂ := hq.2.1
    omega

/-- Every vertical crossing meets a corridor wall when the wall scale is below twelve. -/
theorem kstCorridorIntersects_of_small_scale (m k : ℕ) (hk : k < 12) :
    KSTCorridorIntersects m k := by
  intro a b c d x y e f u v p r q r' q' hp _ hr hx hy hr' hu hv
  have heq : c = e := kstPaths_share_upper_endpoint r r' hk hr hr'
  have hjoin : ∃ z, (z ∈ r.support ∨ z ∈ q.support) ∧
      (z ∈ r'.support ∨ z ∈ q'.support) := by
    refine ⟨c, Or.inl r.start_mem_support, Or.inl ?_⟩
    rw [heq]
    exact r'.start_mem_support
  obtain ⟨z, hz, hw⟩ := vertical_crossing_intersects_connected_walls
    p r q r' q' hp.2.1 hp.2.2.1 hx hu hy hv hjoin
  rcases hw with h | h | h | h
  · exact Or.inl ⟨z, hz, Or.inl h⟩
  · exact Or.inl ⟨z, hz, Or.inr h⟩
  · exact Or.inr ⟨z, hz, Or.inl h⟩
  · exact Or.inr ⟨z, hz, Or.inr h⟩

/-- The corridor bridge cover holds when the wall scale is below twelve. -/
theorem kstCorridorBridgeCover_of_small_scale (n m k : ℕ) (hm : 0 < m) (hk : k < 12) :
    KSTCorridorBridgeCover n m k :=
  kstCorridorBridgeCover_of_intersects n m k hm (kstCorridorIntersects_of_small_scale m k hk)

end Sandpile.External.RSW
