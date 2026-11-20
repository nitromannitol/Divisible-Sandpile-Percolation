import Sandpile.External.RSW.TopConnectedPath
import Sandpile.External.RSW.FourArmPaths
import Sandpile.External.RSW.FourArmOuterPaths

/-!
# Connecting the four-arm configuration to the top

The upper large arm and the two separated inner paths yield an open KST path
connected to the top of the vertical construction rectangle.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The four-arm event yields a KST path connected to the top of the vertical rectangle. -/
theorem kstFourArmEvent_subset_topConnected (j : ℕ) :
    kstFourArmEvent (kstBaseScale j) ⊆
      kstTopConnectedEvent (3 * kstBaseScale j - 3 * (kstBaseScale j / 12))
        (4 * kstBaseScale j) (kstBaseScale j) := by
  intro ω hω
  let m := kstBaseScale j
  let W := 3 * m - 3 * (m / 12)
  let H := centeredPlaneRectangle (m + m / 12) m
  let Q := centeredPlaneRectangle W (4 * m)
  have hm : 0 < m := Nat.mul_pos (by norm_num) (pow_pos (by norm_num) j)
  have hW : m + m / 12 ≤ W := by
    have hβ := (kstBaseScale_offsets j).2
    change m + m / 12 ≤ 3 * m - 3 * (m / 12)
    dsimp only [m, kstBaseScale] at hβ ⊢
    omega
  have hHQ : H ⊆ Q := by
    intro z hz
    have hh := (mem_centeredPlaneRectangle _ _ z).mp hz
    apply (mem_centeredPlaneRectangle _ _ z).mpr
    have hW' : ((m + m / 12 : ℕ) : ℤ) ≤ W := by exact_mod_cast hW
    push_cast at *
    omega
  let f := rectangleGraphInclusion hHQ
  obtain ⟨a₁, b₁, a₂, b₂, p₁, p₂, hp₁, ho₁, hp₂, ho₂, ha₁, hb₁, ha₂, hb₂⟩ :=
    kstFourArmEvent_two_paths m hω
  obtain ⟨a, b, c, d, p, q, _, hop, _, _, hay, hby, _, _, _, _, hbL, hbR, _, _, _, _, hpBottom, _⟩ :=
    kstFourArmEvent_outer_paths j hω
  have hstart : (b : Site 2) 1 = -(m : ℤ) ∧
      -(3 * ((m / 64 : ℕ) : ℤ)) ≤ (b : Site 2) 0 ∧
      (b : Site 2) 0 ≤ 3 * ((m / 64 : ℕ) : ℤ) := by
    push_cast at hbL hbR
    exact ⟨hby, hbL, hbR⟩
  have htop : (a : Site 2) 1 = (4 * m : ℕ) := by push_cast; exact hay
  have hbottom : ∀ z ∈ p.reverse.support, -(m : ℤ) ≤ (z : Site 2) 1 := by
    intro z hz
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    exact hpBottom z hz
  exact kstTopConnectedEvent_of_separated_paths hm hW (by omega)
    (p₁.map f) (p₂.map f) p.reverse (hp₁.map_inclusion hHQ) (hp₂.map_inclusion hHQ)
    (ho₁.map_inclusion hHQ) (ho₂.map_inclusion hHQ) hop.reverse
    ha₁ hb₁ ha₂ hb₂ hstart htop hbottom

end Sandpile.External.RSW
