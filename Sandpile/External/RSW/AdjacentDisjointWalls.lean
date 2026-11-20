import Sandpile.External.RSW.AdjacentJoinedWalls

/-!
# Adjacent-scale disjoint walls

The adjacent-scale six-event inclusion reduces to the case in which the two
vertical wall structures do not meet.
-/

open Set

namespace Sandpile.External.RSW

/-- The disjoint-wall case of the adjacent-scale construction. -/
def KSTAdjacentDisjointWalls (m : ℕ) : Prop :=
  let Q := centeredPlaneRectangle (3 * m - 3 * (m / 12)) (4 * m)
  ∀ (ω : Sym2 (Site 2) → Bool) (a b x top c d y bottom : Q)
    (upper : (rectangleGraph Q).Walk a b) (upperLink : (rectangleGraph Q).Walk x top)
    (lower : (rectangleGraph Q).Walk c d) (lowerLink : (rectangleGraph Q).Walk y bottom),
    IsKSTPath m upper → IsKSTPath m lower → x ∈ upper.support → y ∈ lower.support →
    IsBondOpenWalk ω upper → IsBondOpenWalk ω upperLink →
    IsBondOpenWalk ω lower → IsBondOpenWalk ω lowerLink →
    (top : Site 2) 1 = 4 * m → (bottom : Site 2) 1 = -((4 * m : ℕ) : ℤ) →
    (∀ z, (z ∈ upper.support ∨ z ∈ upperLink.support) →
      ¬ (z ∈ lower.support ∨ z ∈ lowerLink.support)) →
    ω ∈ kstAuxCrossingEvent m true → ω ∈ kstAuxCrossingEvent m false →
    ω ∈ kstQuasiCrossingEvent (4 * m) m

/-- The six-event inclusion follows from its disjoint-wall case. -/
theorem kstAdjacentSixEvent_subset_quasi_of_disjoint (j : ℕ)
    (hdisjoint : KSTAdjacentDisjointWalls (kstBaseScale j)) :
    kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j) := by
  intro ω hω
  let m := kstBaseScale j
  have hm : 0 < m := Nat.mul_pos (by norm_num) (pow_pos (by norm_num) j)
  have hdiv : 12 ∣ m := dvd_mul_of_dvd_left (by norm_num : 12 ∣ 1536) _
  have hwalls := kstFourArmEvent_subset_vertical_walls j hω.1
  obtain ⟨a, b, x, top, upper, upperLink, hp, hx, htop, hpOpen, huOpen⟩ := hwalls.1
  obtain ⟨c, d, y, bottom, lower, lowerLink, hq, hy, hbottom, hqOpen, hvOpen⟩ := hwalls.2
  by_cases hjoin : ∃ z, (z ∈ upper.support ∨ z ∈ upperLink.support) ∧
      (z ∈ lower.support ∨ z ∈ lowerLink.support)
  · exact kstAdjacentQuasi_of_joined_vertical_walls m hm hdiv upper upperLink lower
      lowerLink hp hq hx hy hpOpen huOpen hqOpen hvOpen htop hbottom hjoin hω.2.1 hω.2.2
  · apply hdisjoint ω a b x top c d y bottom upper upperLink lower lowerLink hp hq hx hy
      hpOpen huOpen hqOpen hvOpen htop hbottom
    · intro z hz hz'
      exact hjoin ⟨z, hz, hz'⟩
    · exact hω.2.1
    · exact hω.2.2

end Sandpile.External.RSW
