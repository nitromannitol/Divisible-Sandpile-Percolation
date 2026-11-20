import Sandpile.External.RSW.RefinedLatticeWalk

/-!
# Bounds for refined lattice walks

Coordinate bounds on a lattice walk pass to its scaled and subdivided image.
-/

namespace Sandpile.External.RSW

/-- Refinement preserves coordinate interval bounds, with scale two and the given offset. -/
theorem refinedLatticeWalk_coord_bounds (t : Site 2) {a b : Site 2}
    (p : (lattice 2).Walk a b) (i : Fin 2) (L U : ℤ)
    (hp : ∀ z ∈ p.support, L ≤ z i ∧ z i ≤ U) :
    ∀ z ∈ (refinedLatticeWalk t p).support,
      2 * L + t i ≤ z i ∧ z i ≤ 2 * U + t i := by
  intro z hz
  change z ∈ (subdividedWalk (G := lattice 2) (H := lattice 2)
    (refinedVertex t) (refinedMidpoint t) _ _ p).support at hz
  rw [mem_subdividedWalk_support_iff] at hz
  rcases hz with ⟨x, hx, h⟩ | ⟨e, he, h⟩
  · subst z
    have hx' := hp x hx
    simp only [refinedVertex]
    omega
  · subst z
    revert he
    refine Sym2.inductionOn e ?_
    intro x y hxy
    have hx := hp x (p.fst_mem_support_of_mem_edges hxy)
    have hy := hp y (p.snd_mem_support_of_mem_edges hxy)
    simp only [refinedMidpoint, Sym2.lift_mk]
    omega

end Sandpile.External.RSW
