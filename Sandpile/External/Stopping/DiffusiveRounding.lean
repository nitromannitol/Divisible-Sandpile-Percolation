import Sandpile.External.Stopping.DiffusiveWalkStopping

/-!
# Diffusive time rounding

Rounding a diffusive time down to its lattice index changes time by less than
one diffusive lattice step and leaves the step-walk position unchanged. These
facts support comparison of time-dependent stopping rewards.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The lattice index observed at a diffusive time. -/
noncomputable def diffusiveTimeIndex (R : ℝ) (t : ℝ≥0) : ℕ := ⌊R ^ 2 * (t : ℝ)⌋₊

/-- A diffusive time rounded down to its preceding lattice time. -/
noncomputable def roundDiffusiveTime (R : ℝ) (_hR : 0 < R) (t : ℝ≥0) : ℝ≥0 :=
  (diffusiveTimeIndex R t : ℝ≥0) / ⟨R ^ 2, sq_nonneg R⟩

/-- A positive-scale rounded time is no later than the original time and is
less than one diffusive lattice step earlier. -/
theorem roundDiffusiveTime_bounds {R : ℝ} (hR : 0 < R) (t : ℝ≥0) :
    (roundDiffusiveTime R hR t : ℝ) ≤ (t : ℝ) ∧
      (t : ℝ) - (roundDiffusiveTime R hR t : ℝ) < 1 / R ^ 2 := by
  have hc : 0 < R ^ 2 := sq_pos_of_pos hR
  have hp : 0 ≤ R ^ 2 * (t : ℝ) := mul_nonneg hc.le t.property
  have hl := Nat.floor_le hp
  have hu := Nat.lt_floor_add_one (R ^ 2 * (t : ℝ))
  have hround : (roundDiffusiveTime R hR t : ℝ) =
      (diffusiveTimeIndex R t : ℝ) / R ^ 2 := by
    rfl
  rw [hround]
  constructor
  · apply (div_le_iff₀ hc).2
    change (⌊R ^ 2 * (t : ℝ)⌋₊ : ℝ) ≤ (t : ℝ) * R ^ 2
    nlinarith
  · have hu' : (t : ℝ) < ((diffusiveTimeIndex R t : ℝ) + 1) / R ^ 2 := by
      apply (lt_div_iff₀ hc).2
      change (t : ℝ) * R ^ 2 < (⌊R ^ 2 * (t : ℝ)⌋₊ : ℝ) + 1
      nlinarith
    rw [add_div] at hu'
    linarith

/-- The diffusive step walk is at the lattice site indexed by the rounded
time. -/
theorem diffusiveStepWalk_eq_at_index {d : ℕ} (R : ℝ) (t : ℝ≥0) (X : ℕ → Site d) :
    diffusiveStepWalk R t X = Lclt.scaledSite R (X (diffusiveTimeIndex R t)) := by
  change Lclt.scaledSite R (X ⌊((⟨R ^ 2, sq_nonneg R⟩ * t : ℝ≥0) : ℝ)⌋₊) = _
  have h : ((⟨R ^ 2, sq_nonneg R⟩ * t : ℝ≥0) : ℝ) = R ^ 2 * (t : ℝ) := rfl
  rw [h]
  rfl

/-- The diffusive step-walk position is unchanged when time is rounded down. -/
theorem diffusiveStepWalk_roundDiffusiveTime {d : ℕ} {R : ℝ} (hR : 0 < R)
    (t : ℝ≥0) (X : ℕ → Site d) :
    diffusiveStepWalk R (roundDiffusiveTime R hR t) X = diffusiveStepWalk R t X := by
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hc : 0 < c := by
    change (0 : ℝ) < R ^ 2
    exact sq_pos_of_pos hR
  rw [diffusiveStepWalk_eq_at_index]
  change stepWalk R (c * ((diffusiveTimeIndex R t : ℝ≥0) / c)) X = _
  rw [mul_div_cancel₀ _ hc.ne']
  rw [stepWalk_eq_linearWalk_floor]
  have hn : (((diffusiveTimeIndex R t : ℝ≥0) : ℝ)) = (diffusiveTimeIndex R t : ℝ) := rfl
  rw [hn, Nat.floor_natCast, linearWalk_nat]
  exact (diffusiveStepWalk_eq_at_index R t X).symm

end Sandpile.External.Stopping
