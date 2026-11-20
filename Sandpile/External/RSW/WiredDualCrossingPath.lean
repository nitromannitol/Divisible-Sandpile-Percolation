import Sandpile.External.RSW.WiredDualWalk
import Sandpile.External.RSW.WiredDualBoundaryPath

/-!
# A simple wired dual crossing

Loop erasure yields a dual path across the enlarged rectangle, and its central
vertices avoid the two wired boundary rows.
-/

namespace Sandpile.External.RSW

/-- An absent arm yields a simple wired dual crossing avoiding the central boundary. -/
theorem exists_wired_dual_crossing_path_of_not_kstArmEvent (m : ℕ) (hm : 0 < m)
    (ω : Sym2 (Site 2) → Bool) (h : ω ∉ kstArmEvent m) :
    ∃ (a b : centeredPlaneRectangle (m + m / 64 + 1) (m + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (m + m / 64 + 1) (m + 1))).Walk a b),
      p.IsPath ∧ IsBondOpenWalk (dualBondConfig (wiredArmConfig m ω)) p ∧
      (a : Site 2) 0 = -((m + m / 64 : ℕ) : ℤ) - 1 ∧
      (b : Site 2) 0 = ((m + m / 64 : ℕ) : ℤ) ∧
      (∀ z ∈ p.support, -((m + m / 64 : ℕ) : ℤ) - 1 ≤ (z : Site 2) 0 ∧
        (z : Site 2) 0 ≤ ((m + m / 64 : ℕ) : ℤ) ∧
        -((m : ℤ) + 1) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m) ∧
      ∀ z ∈ p.support, -((m / 64 : ℕ) : ℤ) ≤ (z : Site 2) 0 →
        (z : Site 2) 0 < ((m / 64 : ℕ) : ℤ) →
        -((m : ℤ) + 1) < (z : Site 2) 1 ∧ (z : Site 2) 1 < m := by
  obtain ⟨a, b, p, hp, ha, hb, hs⟩ := exists_wired_dual_walk_of_not_kstArmEvent m hm ω h
  have hpath := p.bypass_isPath
  have hpopen := hp.bypass
  have hys : ∀ z ∈ p.bypass.support,
      -((m : ℤ) + 1) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m := by
    intro z hz
    have hz' := hs z (p.support_bypass_subset_support hz)
    push_cast at hz'
    exact ⟨hz'.2.2.1, hz'.2.2.2⟩
  refine ⟨a, b, p.bypass, hpath, hpopen, ha, hb, ?_, ?_⟩
  · intro z hz
    have hz' := hs z (p.support_bypass_subset_support hz)
    push_cast at hz'
    exact hz'
  · intro z hz hl hu
    have hy := hys z hz
    have hrow : (z : Site 2) 1 ≠ -((m : ℤ) + 1) ∧ (z : Site 2) 1 ≠ m := by
      constructor <;> intro hr
      · have he := hpopen.wired_dual_central_boundary_eq_endpoint m ω p.bypass hpath hys hz
          (Or.inl hr) hl hu
        rcases he with he | he <;> subst z <;> push_cast at * <;> omega
      · have he := hpopen.wired_dual_central_boundary_eq_endpoint m ω p.bypass hpath hys hz
          (Or.inr hr) hl hu
        rcases he with he | he <;> subst z <;> push_cast at * <;> omega
    omega

end Sandpile.External.RSW
