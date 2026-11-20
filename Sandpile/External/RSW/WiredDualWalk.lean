import Sandpile.External.RSW.WiredDualCoordinates
import Sandpile.External.RSW.TranslatedCrossingWalk

/-!
# A dual walk around an absent arm

The crossing furnished by wired duality has a concrete open walk with explicit
face-coordinate bounds and endpoints on the two vertical sides.
-/

namespace Sandpile.External.RSW

/-- Absence of an arm yields an open dual walk across the enlarged face rectangle. -/
theorem exists_wired_dual_walk_of_not_kstArmEvent (m : ℕ) (hm : 0 < m)
    (ω : Sym2 (Site 2) → Bool) (h : ω ∉ kstArmEvent m) :
    ∃ (a b : centeredPlaneRectangle (m + m / 64 + 1) (m + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (m + m / 64 + 1) (m + 1))).Walk a b),
      IsBondOpenWalk (dualBondConfig (wiredArmConfig m ω)) p ∧
      (a : Site 2) 0 = -((m + m / 64 : ℕ) : ℤ) - 1 ∧
      (b : Site 2) 0 = ((m + m / 64 : ℕ) : ℤ) ∧
      ∀ z ∈ p.support,
        -((m + m / 64 : ℕ) : ℤ) - 1 ≤ (z : Site 2) 0 ∧
        (z : Site 2) 0 ≤ ((m + m / 64 : ℕ) : ℤ) ∧
        -((m + 1 : ℕ) : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ (m : ℤ) := by
  let M := m + m / 64
  let x : ℤ := -(M : ℤ) - 1
  let y : ℤ := -((m + 1 : ℕ) : ℤ)
  have hx : x + ((2 * M + 1 : ℕ) : ℤ) = M := by
    dsimp [x]
    omega
  have hy : y + ((2 * m + 1 : ℕ) : ℤ) = m := by
    dsimp [y]
    omega
  have hc := translated_dual_crossing_of_not_kstArmEvent m hm ω h
  change (dualBondConfig (wiredArmConfig m ω) ∘ Sym2.map (fun z => z + ![x, y])) ∈
    bondCrossingEvent (2 * M + 1) (2 * m + 1) at hc
  obtain ⟨a, b, p, hp, ha, hb, hs⟩ := translated_bondCrossingEvent_exists_walk
    (2 * M + 1) (2 * m + 1) (M + 1) (m + 1) x y
    (by dsimp [x]; omega) (by rw [hx]; push_cast; omega)
    (by dsimp [y]; omega) (by rw [hy]; push_cast; omega) hc
  refine ⟨a, b, p, hp, ha, ?_, ?_⟩
  · simpa only [hx, M] using hb
  · intro z hz
    simpa only [hx, hy, x, y, M] using hs z hz

end Sandpile.External.RSW
