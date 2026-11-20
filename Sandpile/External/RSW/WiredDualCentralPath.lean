import Sandpile.External.RSW.WiredDualWalk
import Sandpile.External.RSW.WiredDualBoundaryPath
import Sandpile.External.RSW.HorizontalStripSubpath

/-!
# A central dual path around an absent arm

The dual crossing of the wired rectangle contains a simple path across the
central target interval. Its interior avoids both wired boundary rows.
-/

namespace Sandpile.External.RSW

/-- Absence of an arm gives a simple dual path across the central target interval. -/
theorem exists_wired_dual_central_path_of_not_kstArmEvent (m : ℕ) (hm : 0 < m)
    (ω : Sym2 (Site 2) → Bool) (h : ω ∉ kstArmEvent m) :
    ∃ (a b : centeredPlaneRectangle (m + m / 64 + 1) (m + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (m + m / 64 + 1) (m + 1))).Walk a b),
      p.IsPath ∧ IsBondOpenWalk (dualBondConfig (wiredArmConfig m ω)) p ∧
      (a : Site 2) 0 = -((m / 64 : ℕ) : ℤ) - 1 ∧
      (b : Site 2) 0 = ((m / 64 : ℕ) : ℤ) ∧
      (∀ z ∈ p.support, -((m / 64 : ℕ) : ℤ) - 1 ≤ (z : Site 2) 0 ∧
        (z : Site 2) 0 ≤ ((m / 64 : ℕ) : ℤ) ∧
        -((m : ℤ) + 1) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m) ∧
      ∀ z ∈ p.support, -((m / 64 : ℕ) : ℤ) ≤ (z : Site 2) 0 →
        (z : Site 2) 0 < ((m / 64 : ℕ) : ℤ) →
        -((m : ℤ) + 1) < (z : Site 2) 1 ∧ (z : Site 2) 1 < m := by
  obtain ⟨a, b, p, hp, ha, hb, hs⟩ := exists_wired_dual_walk_of_not_kstArmEvent m hm ω h
  have ha' : (a : Site 2) 0 ≤ -((m / 64 : ℕ) : ℤ) - 1 := by
    rw [ha]
    push_cast
    omega
  have hb' : ((m / 64 : ℕ) : ℤ) ≤ (b : Site 2) 0 := by
    rw [hb]
    push_cast
    omega
  obtain ⟨c, d, q, hq, hpath, hc, hd, hxs, _⟩ :=
    exists_horizontal_strip_subpath p.bypass p.bypass_isPath (L := -((m / 64 : ℕ) : ℤ) - 1)
      (R := ((m / 64 : ℕ) : ℤ)) (by omega) ha' hb'
  have hqopen := hp.bypass.subwalk hq
  have hys : ∀ z ∈ q.support, -((m : ℤ) + 1) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m := by
    intro z hz
    have hz' := hs z (p.support_bypass_subset_support (hq.support_subset hz))
    push_cast at hz'
    exact ⟨hz'.2.2.1, hz'.2.2.2⟩
  refine ⟨c, d, q, hpath, hqopen, hc, hd, ?_, ?_⟩
  · intro z hz
    exact ⟨(hxs z hz).1, (hxs z hz).2, (hys z hz).1, (hys z hz).2⟩
  · intro z hz hl hu
    have hy := hys z hz
    have hne : (z : Site 2) 1 ≠ -((m : ℤ) + 1) ∧ (z : Site 2) 1 ≠ m := by
      constructor <;> intro hrow
      · have he := hqopen.wired_dual_central_boundary_eq_endpoint m ω q hpath hys hz
          (Or.inl hrow) hl hu
        rcases he with he | he
        · subst z
          omega
        · subst z
          omega
      · have he := hqopen.wired_dual_central_boundary_eq_endpoint m ω q hpath hys hz
          (Or.inr hrow) hl hu
        rcases he with he | he
        · subst z
          omega
        · subst z
          omega
    omega

end Sandpile.External.RSW
