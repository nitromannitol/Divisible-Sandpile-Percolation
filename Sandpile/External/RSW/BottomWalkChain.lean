import Sandpile.External.RSW.BottomWalkGluing

/-!
# Chains of bottom walks

Overlapping bottom endpoint intervals can be merged inductively into one open walk
spanning the full chain.
-/

open Set

namespace Sandpile.External.RSW

/-- A finite chain of overlapping bottom walks contains an open walk spanning the chain. -/
theorem exists_open_bottom_walk_spanning_chain {M n : ℕ} {ω : Sym2 (Site 2) → Bool}
    (t : ℕ → ℤ) (ht : Monotone t) (K : ℕ)
    (hwalk : ∀ i < K, ∃ (a b : centeredPlaneRectangle M n)
      (p : (rectangleGraph (centeredPlaneRectangle M n)).Walk a b),
      IsBondOpenWalk ω p ∧ (a : Site 2) 1 = -(n : ℤ) ∧ (b : Site 2) 1 = -(n : ℤ) ∧
      (a : Site 2) 0 ≤ t i ∧ t (i + 1) ≤ (b : Site 2) 0) :
    ∀ k < K, ∃ (a b : centeredPlaneRectangle M n)
      (p : (rectangleGraph (centeredPlaneRectangle M n)).Walk a b),
      IsBondOpenWalk ω p ∧ (a : Site 2) 1 = -(n : ℤ) ∧ (b : Site 2) 1 = -(n : ℤ) ∧
      (a : Site 2) 0 ≤ t 0 ∧ t (k + 1) ≤ (b : Site 2) 0 := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact hwalk 0 hk
  | succ k ih =>
    intro hk
    obtain ⟨a, b, p, hp, ha, hb, hal, hbr⟩ := ih (by omega)
    obtain ⟨c, d, q, hq, hc, hd, hcl, hdr⟩ := hwalk (k + 1) hk
    obtain ⟨x, y, r, hr, hx, hy, hxa, _, _, hdy⟩ :=
      exists_open_bottom_walk_spanning p q hp hq ha hb hc hd
        (by have := ht (show 0 ≤ k + 1 by omega); omega)
        (by have := ht (show k + 1 ≤ k + 1 + 1 by omega); omega)
        (by have := ht (show 0 ≤ k + 1 + 1 by omega); omega)
        (by omega)
    exact ⟨x, y, r, hr, hx, hy, hxa.trans hal, hdr.trans hdy⟩

end Sandpile.External.RSW
