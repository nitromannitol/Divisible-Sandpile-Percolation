import Sandpile.External.Stopping.WalkFloorInterpolation
import Sandpile.External.Stopping.TimeChange

/-!
# Step walks and interpolated walks

The floor-time walk uses only increments already made at each grid time. Its
natural filtration is contained in that of the linear interpolation, which
may reveal the next increment inside a grid interval. The two rescaled paths
are uniformly within one scaled step almost surely.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The rescaled walk held constant between successive lattice times. -/
noncomputable def stepWalk {d : ℕ} (R : ℝ) (s : ℝ≥0) (X : ℕ → Site d) : Continuum.Space d :=
  Lclt.scaledSite R (X ⌊(s : ℝ)⌋₊)

/-- The step walk at any time is the interpolation at the preceding grid time. -/
theorem stepWalk_eq_linearWalk_floor {d : ℕ} (R : ℝ) (s : ℝ≥0) (X : ℕ → Site d) :
    stepWalk R s X = linearWalk R (⌊(s : ℝ)⌋₊ : ℝ≥0) X := by
  simp only [stepWalk, linearWalk_nat]

/-- The natural filtration of the step walk is contained in that of the
interpolated walk. -/
theorem stepWalk_filtration_le_linearWalk {d : ℕ} (R : ℝ) (t : ℝ≥0) :
    Continuum.brownianFiltration (stepWalk (d := d) R) t ≤
      Continuum.brownianFiltration (linearWalk R) t := by
  apply Continuum.brownianFiltration_le
  intro s hs
  have hfloor : (⌊(s : ℝ)⌋₊ : ℝ≥0) ≤ s := by
    exact_mod_cast Nat.floor_le s.property
  have hm := Continuum.measurable_brownianFiltration (linearWalk (d := d) R)
    (⌊(s : ℝ)⌋₊ : ℝ≥0) t (hfloor.trans hs)
  have heq : stepWalk (d := d) R s = linearWalk (d := d) R (⌊(s : ℝ)⌋₊ : ℝ≥0) := by
    funext X
    exact stepWalk_eq_linearWalk_floor R s X
  rw [heq]
  exact hm

/-- Every step-walk stopping time is also a stopping time for the interpolated
walk's natural filtration. -/
theorem isBrownianStopping_linearWalk_of_stepWalk {d : ℕ} (R : ℝ)
    (τ : (ℕ → Site d) → ℝ≥0) (hτ : Continuum.IsBrownianStopping (stepWalk R) τ) :
    Continuum.IsBrownianStopping (linearWalk R) τ := by
  intro t
  exact stepWalk_filtration_le_linearWalk R t _ (hτ t)

/-- The floor-time walk in diffusive time. -/
noncomputable def diffusiveStepWalk {d : ℕ} (R : ℝ) (t : ℝ≥0) (X : ℕ → Site d) :
    Continuum.Space d :=
  stepWalk R (⟨R ^ 2, sq_nonneg R⟩ * t) X

/-- The diffusive step and interpolated paths differ by at most `1 / R` at
all times simultaneously, almost surely. -/
theorem ae_norm_diffusiveWalk_sub_stepWalk_le {d : ℕ} (hd : 1 ≤ d) (x : Site d)
    (R : ℝ) (hR : 0 < R) :
    ∀ᵐ X ∂(walkLaw d x), ∀ t : ℝ≥0,
      ‖diffusiveWalk R t X - diffusiveStepWalk R t X‖ ≤ 1 / R := by
  filter_upwards [ae_norm_linearWalk_sub_floor_le hd x R hR] with X hX
  intro t
  let s : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩ * t
  change ‖linearWalk R s X - Lclt.scaledSite R (X ⌊(s : ℝ)⌋₊)‖ ≤ 1 / R
  exact hX s

end Sandpile.External.Stopping
