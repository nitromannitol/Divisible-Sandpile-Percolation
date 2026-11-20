import Sandpile.External.Stopping.ClockHorizonWeakLimit

/-!
# Normalized lattice stopping clocks

A bounded lattice stopping time can be encoded in the compact unit interval
without changing its physical diffusive time.
-/

open MeasureTheory unitInterval
open scoped NNReal

namespace Sandpile.External.Stopping

/-- A lattice time below the rounded horizon has diffusive time at most the
original horizon. -/
theorem diffusiveLatticeClock_le_horizon (R : ℝ) (hR : 0 < R) (H : ℝ≥0) (n : ℕ)
    (hn : n ≤ ⌊R ^ 2 * (H : ℝ)⌋₊) : diffusiveLatticeClock R n ≤ H := by
  have hs : 0 < R ^ 2 := sq_pos_of_pos hR
  have hfloor : (n : ℝ) ≤ R ^ 2 * (H : ℝ) := by
    have hcast : (n : ℝ) ≤ ⌊R ^ 2 * (H : ℝ)⌋₊ := by exact_mod_cast hn
    exact hcast.trans (Nat.floor_le (by positivity))
  apply NNReal.coe_le_coe.mp
  simp only [diffusiveLatticeClock]
  change (n : ℝ) / R ^ 2 ≤ (H : ℝ)
  exact (div_le_iff₀ hs).2 (by nlinarith)

/-- A unit-time encoding below one recovers its original nonnegative time. -/
theorem unitClock_unitTime_of_le_one (t : ℝ≥0) (ht : t ≤ 1) :
    unitClock id (unitTime t) = t := by
  apply Subtype.ext
  change min (t : ℝ) 1 = (t : ℝ)
  rw [min_eq_left (by exact_mod_cast ht)]

/-- Normalize a discrete clock by a fixed positive physical horizon. -/
noncomputable def normalizedWalkClock {d : ℕ} (R : ℝ) (c : ℝ≥0)
    (τ : (ℕ → Site d) → ℕ) (X : ℕ → Site d) : I :=
  unitTime (diffusiveLatticeClock R (τ X) / c)

/-- A measurable discrete stopping clock has a measurable normalized clock. -/
theorem measurable_normalizedWalkClock {d : ℕ} (R : ℝ) (c : ℝ≥0)
    (τ : (ℕ → Site d) → ℕ) (hτ : Measurable τ) :
    Measurable (normalizedWalkClock R c τ) :=
  (measurable_of_countable (fun n : ℕ => unitTime (diffusiveLatticeClock R n / c))).comp hτ

/-- Decoding a normalized walk clock returns its diffusive time. -/
theorem decode_normalizedWalkClock {d : ℕ} (R : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (τ : (ℕ → Site d) → ℕ) (X : ℕ → Site d)
    (hτ : diffusiveLatticeClock R (τ X) ≤ c) :
    c * unitClock id (normalizedWalkClock R c τ X) = diffusiveLatticeClock R (τ X) := by
  have hratio : diffusiveLatticeClock R (τ X) / c ≤ 1 := by
    exact (div_le_one hc).2 hτ
  rw [normalizedWalkClock, unitClock_unitTime_of_le_one _ hratio, mul_div_cancel₀ _ hc.ne']

end Sandpile.External.Stopping
