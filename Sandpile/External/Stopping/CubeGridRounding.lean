import Sandpile.External.Stopping.KilledLocalizedRounding

/-!
# Cube-killed grid rounding

For starting points in a compact set, all rescaled positions at which a walk
killed on cube exit can stop lie in one compact ball. The temporal rounding
comparison is therefore uniform over those starts and bounded horizons.
-/

open MeasureTheory Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Step-walk and lattice cube-killed values of a bounded continuous reward
are uniformly close at large scales over compact starts and bounded horizons. -/
theorem exists_large_scale_cube_grid_comparison {d : ℕ} [NeZero d]
    (K : Set (Continuum.Space d)) (hK : IsCompact K) (T₁ M : ℝ)
    (G : ℝ → Continuum.Space d → ℝ)
    (hG : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hM : ∀ s z, |G s z| ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ > 0, ∀ R ≥ R₀, ∀ T ∈ Icc (0 : ℝ) T₁, ∀ x ∈ K,
      |sSup (killedStepTimePayoffs R (supBox (fun i => ⌊R * x i⌋) R)
          (fun i => ⌊R * x i⌋) T G) -
        killedStoppingSup (supBox (fun i => ⌊R * x i⌋) R) ⌊R ^ 2 * T⌋₊
          (fun i => ⌊R * x i⌋) (fun k X =>
            G (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
              (Lclt.scaledSite R (X k)))| ≤ ε := by
  obtain ⟨ρ, hρ, hKρ⟩ := hK.isBounded.exists_pos_norm_le
  let A : ℝ := ρ + 3 * Real.sqrt d + 1
  have hA : 0 < A := by dsimp [A]; positivity
  let C : Set (Continuum.Space d) := Metric.closedBall 0 (2 * A)
  have hC : IsCompact C := isCompact_closedBall _ _
  obtain ⟨R₀, hR₀, hround⟩ :=
    exists_large_scale_killed_box_grid_comparison C hC T₁ M G hG hM hε
  refine ⟨max R₀ 1, hR₀.trans_le (le_max_left _ _), ?_⟩
  intro R hR T hT x hx
  have hR₀' : R₀ ≤ R := (le_max_left _ _).trans hR
  have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
  have hf : (0 : ℤ) ≤ ⌊R⌋ := Int.le_floor.mpr (by simpa using (show (0 : ℝ) ≤ R by linarith))
  apply hround R hR₀' T hT R (fun i => ⌊R * x i⌋) hf
  intro y hy
  have hone := cutoff_one_of_killed_site (ρ := ρ) (A := A)
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
    hR1 x (hKρ x hx) (by dsimp [A]; linarith) y hy
  change dist (Lclt.scaledSite R y) 0 ≤ 2 * A
  rw [dist_zero_right]
  by_contra hn
  have hz := Continuum.cutoff_eq_zero_of_norm_ge A hA (Lclt.scaledSite R y)
    (le_of_lt (lt_of_not_ge hn))
  linarith

end Sandpile.External.Stopping
