import Sandpile.External.RSW.WiredDualClipped

/-!
# Transferring a clipped dual path

A wired dual walk in the original rectangle is also open in the original dual
configuration if it does not use an edge along the upper boundary row.
-/

namespace Sandpile.External.RSW

/-- Transfer openness from the wired dual to the original dual in the closed strip. -/
theorem IsBondOpenWalk.of_wired_dual_strip (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    {Q : Finset (Site 2)} {a b : Q} (p : (rectangleGraph Q).Walk a b)
    (hp : IsBondOpenWalk (dualBondConfig (wiredArmConfig m ω)) p)
    (hs : ∀ z ∈ p.support, -(m : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m)
    (htop : ∀ x ∈ p.support, ∀ y ∈ p.support, (rectangleGraph Q).Adj x y →
      ¬ ((x : Site 2) 1 = m ∧ (y : Site 2) 1 = m)) :
    IsBondOpenWalk (dualBondConfig ω) p := by
  induction p with
  | nil => trivial
  | @cons a b c hab p ih =>
    have ha := hs a (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, true_or])
    have htail : ∀ z ∈ p.support, -(m : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m :=
      fun z hz => hs z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, hz, or_true])
    have hb := htail b p.start_mem_support
    have habtop := htop a (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, true_or])
      b (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, p.start_mem_support, or_true]) hab
    have htailtop : ∀ x ∈ p.support, ∀ y ∈ p.support, (rectangleGraph Q).Adj x y →
        ¬ ((x : Site 2) 1 = m ∧ (y : Site 2) 1 = m) := by
      intro x hx y hy hxy
      exact htop x (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, hx, or_true])
        y (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, hy, or_true]) hxy
    refine ⟨?_, ih hp.2 htail htailtop⟩
    have hadj : (lattice 2).Adj (a : Site 2) (b : Site 2) := hab
    rw [← dualBondConfig_wiredArm_eq_of_adjacent_strip m ω hadj ha hb habtop]
    exact hp.1

end Sandpile.External.RSW
