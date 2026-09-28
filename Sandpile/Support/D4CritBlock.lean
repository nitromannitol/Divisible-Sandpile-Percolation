import Sandpile.Support.D4BlockMono

/-!
# Step 3 of the dimension-four percolation proof, read on one block

This file localizes Step 3 of the dimension-four percolation proof (`sandpile.tex:4048-4065`) to
a single block: the implication `𝓑_r > -ε₀ log r ⟹ 𝓑_{r,N} + Y_r > b₀ log r / 2` only has to
hold at the finitely many sites of the block, so the future-height and time-truncation events
are needed only there (`blockGood_mono_on`, specialized to the ball field in
`blockGood_block_of_ball_on`). The four rectangles making up a block event all sit inside the
square of side `4r` anchored at the block corner (`planeRectangle_subset`), and
`measure_biUnion_card_le` records the union bound over a finite set of sites this localization
feeds into.
-/

open MeasureTheory

noncomputable section
namespace Sandpile

/-- Enlarging both half-widths of a plane rectangle only enlarges the rectangle. -/
lemma planeRectangle_subset {w h w' h' : ℕ} (hw : w ≤ w') (hh : h ≤ h') :
    planeRectangle w h ⊆ planeRectangle w' h' := by
  intro z hz
  rw [mem_planeRectangle] at hz ⊢
  exact ⟨hz.1, hz.2.1.trans (by exact_mod_cast hw), hz.2.2.1,
    hz.2.2.2.trans (by exact_mod_cast hh)⟩

/-- Step 3 on one block: the level implication is needed only at the sites of
the block. -/
lemma blockGood_mono_on (r : ℕ) (F G : Site 2 → ℝ) (ℓ ℓ' : ℝ) (z : Site 2)
    (h : ∀ v ∈ planeRectangle (4 * r) (4 * r),
      ℓ ≤ F (blockShift r z v) → ℓ' ≤ G (blockShift r z v))
    (hz : BlockGood r F ℓ z) : BlockGood r G ℓ' z := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact crossingValue_mono_of_level (isLatticeRectangle_planeRectangle (2 * r) (2 * r))
      (planeRectangle_nonempty (2 * r) (2 * r)) _ _ ℓ ℓ'
      (fun u hu => h (u : Site 2)
        (planeRectangle_subset (by omega) (by omega) u.2) hu) h1
  · exact verticalCrossingValue_mono_of_level (2 * r) (2 * r) _ _ ℓ ℓ'
      (fun u hu => h (u : Site 2)
        (planeRectangle_subset (by omega) (by omega) u.2) hu) h2
  · exact crossingValue_mono_of_level (isLatticeRectangle_planeRectangle (4 * r) (2 * r))
      (planeRectangle_nonempty (4 * r) (2 * r)) _ _ ℓ ℓ'
      (fun u hu => h (u : Site 2)
        (planeRectangle_subset (by omega) (by omega) u.2) hu) h3
  · exact verticalCrossingValue_mono_of_level (2 * r) (4 * r) _ _ ℓ ℓ'
      (fun u hu => h (u : Site 2)
        (planeRectangle_subset (by omega) (by omega) u.2) hu) h4

/-- Step 3 on one block for the ball field: a good block for `𝓑_{2r}` at level
`-b₀ log(2r)/4` is a good block for `𝓑_{2r,N} + Y` at level `b₀ log(2r)/2`,
once the future height is above `b₀ log(2r)` and the time truncation costs at
most `b₀ log(2r)/4` at the sites of the block. -/
lemma blockGood_block_of_ball_on (r : ℕ) (B BN Y : Site 2 → ℝ) (b₀ : ℝ) (z : Site 2)
    (hY : ∀ v ∈ planeRectangle (4 * r) (4 * r),
      b₀ * Real.log ((2 * r : ℕ) : ℝ) ≤ Y (blockShift r z v))
    (hBN : ∀ v ∈ planeRectangle (4 * r) (4 * r),
      |B (blockShift r z v) - BN (blockShift r z v)| ≤ b₀ * Real.log ((2 * r : ℕ) : ℝ) / 4)
    (hbal : BlockGood r B (-(b₀ / 4 * Real.log ((2 * r : ℕ) : ℝ))) z) :
    BlockGood r (fun u => BN u + Y u) (b₀ * Real.log ((2 * r : ℕ) : ℝ) / 2) z := by
  refine blockGood_mono_on r B (fun u => BN u + Y u)
    (-(b₀ / 4 * Real.log ((2 * r : ℕ) : ℝ)))
    (b₀ * Real.log ((2 * r : ℕ) : ℝ) / 2) z ?_ hbal
  intro v hv hu
  have h1 := hY v hv
  have h2 := (abs_le.mp (hBN v hv)).2
  linarith

/-- Union bound over a finite set of sites. -/
lemma measure_biUnion_card_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (K : Finset (Site 2)) (S : Site 2 → Set Ω) (δ : ENNReal)
    (h : ∀ v ∈ K, μ (S v) ≤ δ) : μ (⋃ v ∈ K, S v) ≤ K.card * δ := by
  refine (measure_biUnion_finset_le K S).trans ?_
  calc ∑ v ∈ K, μ (S v) ≤ ∑ _v ∈ K, δ := Finset.sum_le_sum h
    _ = K.card * δ := by simp [Finset.sum_const]

end Sandpile
