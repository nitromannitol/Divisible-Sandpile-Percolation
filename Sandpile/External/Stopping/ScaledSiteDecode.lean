import Sandpile.External.Stopping.StepWalkStopping

/-!
# Recovering lattice observations from a step walk

At positive scale a rescaled lattice site determines the original site. The
step-walk filtration therefore contains every lattice observation made by the
current time.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Recover integer coordinates from a rescaled site. -/
noncomputable def decodeScaledSite {d : ℕ} (R : ℝ) (z : Continuum.Space d) : Site d :=
  fun i => ⌊R * z i⌋

/-- Decoding rescaled sites is measurable. -/
theorem measurable_decodeScaledSite {d : ℕ} (R : ℝ) : Measurable (decodeScaledSite (d := d) R) := by
  apply measurable_pi_iff.2
  intro i
  exact Int.measurable_floor.comp (measurable_const.mul
    (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable)

/-- A positive-scale rescaled site decodes to the original lattice site. -/
theorem decodeScaledSite_scaledSite {d : ℕ} {R : ℝ} (hR : 0 < R) (x : Site d) :
    decodeScaledSite R (Lclt.scaledSite R x) = x := by
  funext i
  change ⌊R * ((x i : ℝ) / R)⌋ = x i
  have h : R * ((x i : ℝ) / R) = (x i : ℝ) := by field_simp
  rw [h, Int.floor_intCast]

/-- A lattice observation is measurable in the step-walk filtration at any
later time. -/
theorem measurable_walk_coordinate_step_filtration {d : ℕ} {R : ℝ} (hR : 0 < R)
    (j : ℕ) (t : ℝ≥0) (hjt : (j : ℝ≥0) ≤ t) :
    @Measurable (ℕ → Site d) (Site d) (Continuum.brownianFiltration (stepWalk R) t)
      inferInstance (fun X => X j) := by
  have hm := Continuum.measurable_brownianFiltration (stepWalk (d := d) R) (j : ℝ≥0) t hjt
  have h := (measurable_decodeScaledSite R).comp hm
  have heq : (fun X : ℕ → Site d => decodeScaledSite R (stepWalk R (j : ℝ≥0) X)) = fun X => X j := by
    funext X
    change decodeScaledSite R (Lclt.scaledSite R (X ⌊((j : ℝ≥0) : ℝ)⌋₊)) = X j
    have hj : ((j : ℝ≥0) : ℝ) = (j : ℝ) := rfl
    rw [hj, Nat.floor_natCast]
    exact decodeScaledSite_scaledSite hR (X j)
  rw [← heq]
  exact h

end Sandpile.External.Stopping
