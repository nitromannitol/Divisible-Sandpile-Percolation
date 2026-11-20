import Sandpile.External.RSW.TranslatedArmTargets
import Sandpile.External.RSW.FourArms

/-!
# The two inner paths of the four-arm event

The two small translated arms yield KST paths whose upper and lower targets lie on
opposite sides of the central axis.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The four-arm event contains two KST paths with the prescribed separated targets. -/
theorem kstFourArmEvent_two_paths (m : ℕ) {ω : Sym2 (Site 2) → Bool}
    (hω : ω ∈ kstFourArmEvent m) :
    ∃ (a₁ b₁ a₂ b₂ : centeredPlaneRectangle (m + m / 12) m)
      (p₁ : (rectangleGraph (centeredPlaneRectangle (m + m / 12) m)).Walk a₁ b₁)
      (p₂ : (rectangleGraph (centeredPlaneRectangle (m + m / 12) m)).Walk a₂ b₂),
      IsKSTPath m p₁ ∧ IsBondOpenWalk ω p₁ ∧ IsKSTPath m p₂ ∧ IsBondOpenWalk ω p₂ ∧
      (a₁ : Site 2) 0 ≤ -(3 * ((m / 64 : ℕ) : ℤ)) ∧
      (b₁ : Site 2) 0 ≤ -(3 * ((m / 64 : ℕ) : ℤ)) ∧
      3 * ((m / 64 : ℕ) : ℤ) ≤ (a₂ : Site 2) 0 ∧
      3 * ((m / 64 : ℕ) : ℤ) ≤ (b₂ : Site 2) 0 := by
  let α : ℤ := (m / 64 : ℕ)
  let β : ℤ := (m / 12 : ℕ)
  have hsep : 5 * α ≤ β := by
    dsimp only [α, β]
    exact_mod_cast five_arm_offsets_le_bridge_offset m
  obtain ⟨hplus, hminus, _, _⟩ := hω
  obtain ⟨a₂, b₂, p₂, hp₂, ho₂, ha₂, _, hb₂, _⟩ :=
    translated_kstArmEvent_exists_path_with_targets m (4 * α) (by omega) (by omega) hplus
  obtain ⟨a₁, b₁, p₁, hp₁, ho₁, _, ha₁, _, hb₁⟩ :=
    translated_kstArmEvent_exists_path_with_targets m (-(4 * α)) (by omega) (by omega) hminus
  exact ⟨a₁, b₁, a₂, b₂, p₁, p₂, hp₁, ho₁, hp₂, ho₂,
    by omega, by omega, by omega, by omega⟩

end Sandpile.External.RSW
