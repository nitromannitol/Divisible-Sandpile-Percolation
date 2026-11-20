import Sandpile.External.RSW.JoinedWallsWidth
import Sandpile.External.RSW.TranslatedCrossingWalk
import Sandpile.External.RSW.FourArmVerticalWalls

/-!
# Adjacent-scale construction with joined walls

Intersecting top- and bottom-connected KST paths in the central rectangle, together
with the two auxiliary crossings, supply the adjacent-scale quasi-crossing.
-/

open Set

namespace Sandpile.External.RSW

/-- Joined vertical KST walls and the two auxiliary crossings give the adjacent
quasi-crossing at a base scale. -/
theorem kstAdjacentQuasi_of_joined_vertical_walls (m : ℕ) (hm : 0 < m) (hdiv : 12 ∣ m)
    {ω : Sym2 (Site 2) → Bool}
    {a b x top c d y bottom :
      centeredPlaneRectangle (3 * m - 3 * (m / 12))
        (4 * m)}
    (upper : (rectangleGraph (centeredPlaneRectangle
      (3 * m - 3 * (m / 12)) (4 * m))).Walk a b)
    (upperLink : (rectangleGraph (centeredPlaneRectangle
      (3 * m - 3 * (m / 12)) (4 * m))).Walk x top)
    (lower : (rectangleGraph (centeredPlaneRectangle
      (3 * m - 3 * (m / 12)) (4 * m))).Walk c d)
    (lowerLink : (rectangleGraph (centeredPlaneRectangle
      (3 * m - 3 * (m / 12)) (4 * m))).Walk y bottom)
    (hp : IsKSTPath (m) upper) (hq : IsKSTPath (m) lower)
    (hx : x ∈ upper.support) (hy : y ∈ lower.support)
    (hpOpen : IsBondOpenWalk ω upper) (huOpen : IsBondOpenWalk ω upperLink)
    (hqOpen : IsBondOpenWalk ω lower) (hvOpen : IsBondOpenWalk ω lowerLink)
    (htop : (top : Site 2) 1 = 4 * m)
    (hbottom : (bottom : Site 2) 1 = -((4 * m : ℕ) : ℤ))
    (hjoin : ∃ z, (z ∈ upper.support ∨ z ∈ upperLink.support) ∧
      (z ∈ lower.support ∨ z ∈ lowerLink.support))
    (hl : ω ∈ kstAuxCrossingEvent (m) true)
    (hr : ω ∈ kstAuxCrossingEvent (m) false) :
    ω ∈ kstQuasiCrossingEvent (4 * m) m := by
  let M := 3 * m - 3 * (m / 12)
  let Q := centeredPlaneRectangle M (4 * m)
  let R := centeredPlaneRectangle (5 * m) (4 * m)
  have h12 : 12 * (m / 12) = m := Nat.mul_div_cancel' hdiv
  have hM : 0 < M := by dsimp [M]; omega
  have hQR : Q ⊆ R := by
    intro z hz
    have hz' := (mem_centeredPlaneRectangle _ _ _).mp hz
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    dsimp only [Q, R, M] at *
    push_cast at *
    omega
  let f := rectangleGraphInclusion hQR
  obtain ⟨l, l', lp, hlOpen, hla, hlb⟩ := kstAuxCrossingEvent_exists_walk m true hl
  obtain ⟨r', r, rp, hrOpen, hra, hrb⟩ := kstAuxCrossingEvent_exists_walk m false hr
  have hwidth : 4 * m + 3 * ((4 * m) / 12) = 5 * m := by omega
  have hp' : IsKSTPath m (upper.map f) := hp.map_inclusion hQR
  have hq' : IsKSTPath m (lower.map f) := hq.map_inclusion hQR
  have hquasi : ω ∈ kstQuasiCrossingEvent (4 * m) m := by
    apply @kstQuasiCrossing_of_joined_vertical_walls_width (4 * m) m M (5 * m)
      hM hwidth.symm ω (f a) (f b) (f x) (f top) (f c) (f d) (f y) (f bottom)
      l l' r r' (upper.map f) (upperLink.map f) (lower.map f) (lowerLink.map f)
      lp rp.reverse hp' hq'
    · rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    · rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨y, hy, rfl⟩
    · exact hpOpen.map_inclusion hQR
    · exact huOpen.map_inclusion hQR
    · exact hqOpen.map_inclusion hQR
    · exact hvOpen.map_inclusion hQR
    · exact hlOpen
    · exact hrOpen.reverse
    · rw [hwidth]
      simpa only [Bool.true_eq, ↓reduceIte, Nat.cast_mul, Nat.cast_ofNat] using hla
    · rw [hwidth]
      simpa only [Bool.false_eq_true, ↓reduceIte, Nat.cast_mul, Nat.cast_ofNat] using hrb
    · dsimp only [M]; simp only [↓reduceIte] at hla; push_cast at *; omega
    · dsimp only [M]; simp only [↓reduceIte] at hlb; push_cast at *; omega
    · dsimp only [M]; simp only [Bool.false_eq_true, ↓reduceIte] at hrb; push_cast at *; omega
    · dsimp only [M]; simp only [Bool.false_eq_true, ↓reduceIte] at hra; push_cast at *; omega
    · exact htop
    · exact hbottom
    · intro z hz
      rcases hz with hz | hz <;> rw [SimpleGraph.Walk.support_map] at hz <;>
        obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz <;> exact w.property
    · intro z hz
      rcases hz with hz | hz <;> rw [SimpleGraph.Walk.support_map] at hz <;>
        obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz <;> exact w.property
    · obtain ⟨z, hz, hz'⟩ := hjoin
      refine ⟨f z, ?_, ?_⟩
      · rcases hz with hz | hz
        · left; rw [SimpleGraph.Walk.support_map]; exact List.mem_map.mpr ⟨z, hz, rfl⟩
        · right; rw [SimpleGraph.Walk.support_map]; exact List.mem_map.mpr ⟨z, hz, rfl⟩
      · rcases hz' with hz | hz
        · left; rw [SimpleGraph.Walk.support_map]; exact List.mem_map.mpr ⟨z, hz, rfl⟩
        · right; rw [SimpleGraph.Walk.support_map]; exact List.mem_map.mpr ⟨z, hz, rfl⟩
  exact hquasi

end Sandpile.External.RSW
