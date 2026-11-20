import Sandpile.External.Stopping.StepWalkAldous

/-!
# Stopping times of the step walk

A stopping time of the floor-time walk, rounded down to the preceding grid
point, is a stopping time for the discrete walk. Unlike linear interpolation,
the step walk does not reveal the next lattice position within a grid cell.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The step walk before the next lattice time is determined by the walk
through the current lattice time. -/
theorem stepWalk_grid_causal {d : ℕ} (R : ℝ) (k : ℕ) (X Y : ℕ → Site d)
    (hXY : ∀ j ≤ k, X j = Y j) (s : ℝ≥0) (hs : s < (k + 1 : ℕ)) :
    stepWalk R s X = stepWalk R s Y := by
  have hs' : (s : ℝ) < (k + 1 : ℕ) := by exact_mod_cast hs
  have hf : ⌊(s : ℝ)⌋₊ ≤ k := by
    have h : ⌊(s : ℝ)⌋₊ < k + 1 := (Nat.floor_lt s.property).2 hs'
    omega
  simp only [stepWalk, hXY _ hf]

/-- Rounding a step-walk stopping time down gives a discrete walk stopping
time. -/
theorem isWalkStopping_floor_of_stepWalk {d : ℕ} (R : ℝ)
    (τ : (ℕ → Site d) → ℝ≥0) (hτ : Continuum.IsBrownianStopping (stepWalk R) τ) :
    IsWalkStopping (fun X => ⌊(τ X : ℝ)⌋₊) := by
  intro k X Y hXY hk
  change ⌊(τ X : ℝ)⌋₊ = k at hk
  have hlt : τ X < (k + 1 : ℕ) := by
    have h := Nat.lt_floor_add_one (τ X : ℝ)
    rw [hk] at h
    exact_mod_cast h
  have heq : τ Y = τ X := hτ.galmarino (τ X) X Y rfl (fun s hs =>
    stepWalk_grid_causal R k X Y hXY s (lt_of_le_of_lt hs hlt))
  simpa only [heq] using hk

/-- Rounding the diffusively rescaled step-walk stopping time down to a lattice
index gives a discrete walk stopping time. -/
theorem isWalkStopping_floor_of_diffusiveStepWalk {d : ℕ} {R : ℝ} (hR : 0 < R)
    (τ : (ℕ → Site d) → ℝ≥0) (hτ : Continuum.IsBrownianStopping (diffusiveStepWalk R) τ) :
    IsWalkStopping (fun X => ⌊(R ^ 2) * (τ X : ℝ)⌋₊) := by
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hc : 0 < c := by
    change (0 : ℝ) < R ^ 2
    exact sq_pos_of_pos hR
  have hτ' : Continuum.IsBrownianStopping (stepWalk R) (fun X => c * τ X) :=
    isBrownianStopping_mul_timeChange (stepWalk R) c hc τ hτ
  have h := isWalkStopping_floor_of_stepWalk R (fun X => c * τ X) hτ'
  convert h using 1
  funext X
  congr 1

end Sandpile.External.Stopping
