import Sandpile.External.Stopping.WalkStoppingFiltration

/-!
# Discrete stopping times in diffusive time

A lattice stopping index divided by the diffusive speed is a stopping time for
the step walk, and the step walk then occupies exactly the stopped lattice
site. This complements the rounding of step-walk stops to lattice indices.
-/

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Dividing a stopping time by a positive time-change factor gives a stopping
time for the corresponding time-scaled process. -/
theorem isBrownianStopping_div_timeChange {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (c : ℝ≥0) (hc : 0 < c)
    (τ : Ω → ℝ≥0) (hτ : Continuum.IsBrownianStopping B τ) :
    Continuum.IsBrownianStopping (fun t => B (c * t)) (fun ω => τ ω / c) := by
  intro t
  change MeasurableSet[Continuum.brownianFiltration (fun u => B (c * u)) t]
    {ω | (((τ ω / c : ℝ≥0) : ℝ≥0∞)) ≤ (t : ℝ≥0∞)}
  rw [brownianFiltration_mul_timeChange B c hc t]
  have heq : {ω | (((τ ω / c : ℝ≥0) : ℝ≥0∞)) ≤ (t : ℝ≥0∞)} =
      {ω | ((τ ω : ℝ≥0) : ℝ≥0∞) ≤ ((c * t : ℝ≥0) : ℝ≥0∞)} := by
    ext ω
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe]
    rw [div_le_iff₀ hc, mul_comm]
  rw [heq]
  exact hτ (c * t)

/-- A lattice stopping index expressed in diffusive time at positive scale. -/
noncomputable def walkStopToDiffusiveTime {d : ℕ} (R : ℝ) (_hR : 0 < R)
    (τ : (ℕ → Site d) → ℕ) (X : ℕ → Site d) : ℝ≥0 :=
  (τ X : ℝ≥0) / ⟨R ^ 2, sq_nonneg R⟩

/-- A discrete walk stopping rule is a stopping time for the diffusive step
walk after the deterministic change of time. -/
theorem isBrownianStopping_diffusiveStepWalk_of_walkStopping {d : ℕ} {R : ℝ} (hR : 0 < R)
    (τ : (ℕ → Site d) → ℕ) (hτ : IsWalkStopping τ) :
    Continuum.IsBrownianStopping (diffusiveStepWalk R) (walkStopToDiffusiveTime R hR τ) := by
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hc : 0 < c := by
    change (0 : ℝ) < R ^ 2
    exact sq_pos_of_pos hR
  exact isBrownianStopping_div_timeChange (stepWalk R) c hc (fun X => (τ X : ℝ≥0))
    (isBrownianStopping_stepWalk_of_walkStopping hR τ hτ)

/-- At a lattice stop expressed in diffusive time, the step walk is at the
corresponding rescaled lattice site. -/
theorem diffusiveStepWalk_walkStopToDiffusiveTime {d : ℕ} {R : ℝ} (hR : 0 < R)
    (τ : (ℕ → Site d) → ℕ) (X : ℕ → Site d) :
    diffusiveStepWalk R (walkStopToDiffusiveTime R hR τ X) X = Lclt.scaledSite R (X (τ X)) := by
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hc : 0 < c := by
    change (0 : ℝ) < R ^ 2
    exact sq_pos_of_pos hR
  change stepWalk R (c * ((τ X : ℝ≥0) / c)) X = Lclt.scaledSite R (X (τ X))
  rw [mul_div_cancel₀ _ hc.ne']
  rw [stepWalk_eq_linearWalk_floor]
  have hn : (((τ X : ℝ≥0) : ℝ)) = (τ X : ℝ) := rfl
  rw [hn, Nat.floor_natCast, linearWalk_nat]

end Sandpile.External.Stopping
