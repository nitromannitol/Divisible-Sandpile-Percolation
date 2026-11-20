import Sandpile.External.Stopping.CubeConstraintWeakLimit
import Sandpile.External.Stopping.KilledStepHorizon
import Sandpile.External.Stopping.CoupledStepWalkConvergence
import Sandpile.External.Stopping.LatticeCubeGeometry

/-!
# Cube constraints for interpolated walks

A step-walk rule killed at a lattice cube keeps its interpolated path within
one scaled lattice step of the unit cube before stopping.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A killed step-walk rule gives an interpolated path constrained to the
unit cube enlarged by one lattice spacing before the stopping time. -/
theorem ae_centeredWalkPath_cube_constraint
    {d : ℕ} [NeZero d] {R : ℝ} (hR : 0 < R) (q : Site d)
    (θ : (ℕ → Site d) → ℝ≥0)
    (hkill : ∀ᵐ X ∂(walkLaw d q), ∀ j : ℕ,
      (j : ℝ) < R ^ 2 * (θ X : ℝ) → X j ∈ supBox q R) :
    ∀ᵐ X ∂(walkLaw d q), (centeredWalkPath R q X, θ X) ∈
      cubeConstrainedPaths (1 + 1 / R) := by
  filter_upwards [hkill, ae_norm_diffusiveWalk_sub_stepWalk_le
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)) q R hR] with X hX herr
  intro t ht i
  let j : ℕ := ⌊R ^ 2 * (t : ℝ)⌋₊
  have hj : (j : ℝ) < R ^ 2 * (θ X : ℝ) := by
    have hfloor : (j : ℝ) ≤ R ^ 2 * (t : ℝ) :=
      Nat.floor_le (mul_nonneg (sq_nonneg R) t.property)
    exact hfloor.trans_lt (mul_lt_mul_of_pos_left (by exact_mod_cast ht) (sq_pos_of_pos hR))
  have hcenter := centeredScaledSite_mem_closedUnitCube hR (hX j hj) i
  have hstep : diffusiveStepWalk R t X - Lclt.scaledSite R q = centeredScaledSite R q (X j) := by
    have hs : ((⟨R ^ 2, sq_nonneg R⟩ * t : ℝ≥0) : ℝ) = R ^ 2 * (t : ℝ) := rfl
    ext k
    simp only [diffusiveStepWalk, stepWalk, hs, centeredScaledSite,
      Lclt.scaledSite, PiLp.sub_apply, Pi.sub_apply, Int.cast_sub, j]
    ring
  have hdist : ‖centeredWalkPath R q X t - centeredScaledSite R q (X j)‖ ≤ 1 / R := by
    rw [← hstep]
    change ‖(diffusiveWalk R t X - Lclt.scaledSite R q) -
      (diffusiveStepWalk R t X - Lclt.scaledSite R q)‖ ≤ 1 / R
    simpa only [sub_sub_sub_cancel_right] using herr t
  have hcoord : |(centeredWalkPath R q X t - centeredScaledSite R q (X j)) i| ≤ 1 / R := by
    have h := PiLp.norm_apply_le (centeredWalkPath R q X t - centeredScaledSite R q (X j)) i
    simpa only [Real.norm_eq_abs] using h.trans hdist
  have hcenter' : |centeredScaledSite R q (X j) i| ≤ 1 := by
    simpa only [PiLp.zero_apply, sub_zero] using hcenter
  have hid : centeredWalkPath R q X t i =
      (centeredWalkPath R q X t - centeredScaledSite R q (X j)) i + centeredScaledSite R q (X j) i := by
    simp only [PiLp.sub_apply, sub_add_cancel]
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith)

end Sandpile.External.Stopping
