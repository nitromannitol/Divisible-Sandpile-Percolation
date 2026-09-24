/-
Monotonicity of the crossing values and of the good-block event in the field
and the level: this is Step 3 of the dimension-four proof
(`sandpile.tex:4048-4065`) read on the block event, where the implication
`𝓑_r > -ε₀ log r ⟹ 𝓑_{r,N} + Y_r > b₀ log r / 2` turns crossings of the ball
field into crossings of the block field.
-/
import Sandpile.Support.D4BlockGood

noncomputable section
namespace Sandpile


lemma crossingValue_mono_of_level {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    (hN : Q.Nonempty) (F G : Q → ℝ) (ℓ ℓ' : ℝ) (h : ∀ u : Q, ℓ ≤ F u → ℓ' ≤ G u)
    (hF : ℓ ≤ crossingValue Q F) : ℓ' ≤ crossingValue Q G := by
  obtain ⟨a, b, p, ha, hb, hp⟩ := (le_crossingValue_iff_exists_walk hQ hN F ℓ).mp hF
  exact le_crossingValue_of_walk hQ p ha hb (fun z hz => h z (hp z hz))

lemma verticalCrossingValue_mono_of_level (w h' : ℕ)
    (F G : planeRectangle w h' → ℝ) (ℓ ℓ' : ℝ)
    (h : ∀ u : planeRectangle w h', ℓ ≤ F u → ℓ' ≤ G u)
    (hF : ℓ ≤ verticalCrossingValue w h' F) : ℓ' ≤ verticalCrossingValue w h' G := by
  unfold verticalCrossingValue at hF ⊢
  exact crossingValue_mono_of_level (isLatticeRectangle_planeRectangle h' w)
    (planeRectangle_nonempty h' w) _ _ ℓ ℓ' (fun u hu => h _ hu) hF

/-- Step 3 of the dimension-four proof at the level of the block event: if every
site above the level `ℓ` for `F` is above `ℓ'` for `G`, a good block for `F` at
level `ℓ` is a good block for `G` at level `ℓ'`. -/
lemma blockGood_mono (r : ℕ) (F G : Site 2 → ℝ) (ℓ ℓ' : ℝ) (z : Site 2)
    (h : ∀ u : Site 2, ℓ ≤ F u → ℓ' ≤ G u) (hz : BlockGood r F ℓ z) :
    BlockGood r G ℓ' z := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact crossingValue_mono_of_level (isLatticeRectangle_planeRectangle (2 * r) (2 * r))
      (planeRectangle_nonempty (2 * r) (2 * r)) _ _ ℓ ℓ'
      (fun u hu => h (blockShift r z (u : Site 2)) hu) h1
  · exact verticalCrossingValue_mono_of_level (2 * r) (2 * r) _ _ ℓ ℓ'
      (fun u hu => h (blockShift r z (u : Site 2)) hu) h2
  · exact crossingValue_mono_of_level (isLatticeRectangle_planeRectangle (4 * r) (2 * r))
      (planeRectangle_nonempty (4 * r) (2 * r)) _ _ ℓ ℓ'
      (fun u hu => h (blockShift r z (u : Site 2)) hu) h3
  · exact verticalCrossingValue_mono_of_level (2 * r) (4 * r) _ _ ℓ ℓ'
      (fun u hu => h (blockShift r z (u : Site 2)) hu) h4



/-- Step 3 of the dimension-four proof at the level of the block event: a good
block for the ball field at the level `-b₀ log(2r)/4` is a good block for the
block field `𝓑_{2r,N} + Y` at the level `b₀ log(2r)/2`, once the future height
is above `b₀ log(2r)` and the time truncation costs at most `b₀ log(2r)/4`. -/
lemma blockGood_block_of_ball (r : ℕ) (B BN Y : Site 2 → ℝ) (b₀ : ℝ) (z : Site 2)
    (hY : ∀ u, b₀ * Real.log ((2 * r : ℕ) : ℝ) ≤ Y u)
    (hBN : ∀ u, |B u - BN u| ≤ b₀ * Real.log ((2 * r : ℕ) : ℝ) / 4)
    (hbal : BlockGood r B (-(b₀ / 4 * Real.log ((2 * r : ℕ) : ℝ))) z) :
    BlockGood r (fun u => BN u + Y u) (b₀ * Real.log ((2 * r : ℕ) : ℝ) / 2) z := by
  refine blockGood_mono r B (fun u => BN u + Y u)
    (-(b₀ / 4 * Real.log ((2 * r : ℕ) : ℝ)))
    (b₀ * Real.log ((2 * r : ℕ) : ℝ) / 2) z ?_ hbal
  intro u hu
  have h1 := hY u
  have h2 := (abs_le.mp (hBN u)).2
  linarith

end Sandpile
