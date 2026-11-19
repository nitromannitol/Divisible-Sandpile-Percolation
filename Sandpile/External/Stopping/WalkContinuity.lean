import Sandpile.External.Stopping.TimeChange
import LatticeProb.Walk.ConstantStepContinuous

/-!
# Continuity of the interpolated walk

The linear lattice interpolation is a continuous path. The proof uses the
constant-step interpolation at each coordinate.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The lattice-time interpolation is continuous for every walk path. -/
theorem continuous_linearWalk {d : ℕ} (R : ℝ) (X : ℕ → Site d) :
    Continuous (fun s => linearWalk R s X) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous.comp
  apply continuous_pi fun i => ?_
  let p : ℕ → ℂ := fun n => (Lclt.scaledSite R (X n) i : ℂ)
  have h := Complex.continuous_re.comp (LatticeProb.ConstantStepInterpolation.continuous_path 1 p)
  convert h using 1
  funext s
  simp [LatticeProb.ConstantStepInterpolation.path, p,
    AffineMap.lineMap_apply_module]

/-- The diffusively rescaled interpolation is continuous for every walk path. -/
theorem continuous_diffusiveWalk {d : ℕ} (R : ℝ) (X : ℕ → Site d) :
    Continuous (fun t => diffusiveWalk R t X) := by
  exact (continuous_linearWalk R X).comp (continuous_const.mul continuous_id)

/-- At each time, the interpolation is measurable in the walk path. -/
theorem measurable_linearWalk {d : ℕ} (R : ℝ) (s : ℝ≥0) :
    Measurable (fun X : ℕ → Site d => linearWalk R s X) := by
  have hm : Measurable (Lclt.scaledSite (d := d) R) := measurable_of_countable _
  have h₁ : Measurable (fun X : ℕ → Site d => Lclt.scaledSite R (X ⌊(s : ℝ)⌋₊)) :=
    hm.comp (measurable_pi_apply _)
  have h₂ : Measurable (fun X : ℕ → Site d => Lclt.scaledSite R (X (⌊(s : ℝ)⌋₊ + 1))) :=
    hm.comp (measurable_pi_apply _)
  have hc₁ : Measurable (fun _ : ℕ → Site d => (1 - ((s : ℝ) - ⌊(s : ℝ)⌋₊) : ℝ)) :=
    measurable_const
  have hc₂ : Measurable (fun _ : ℕ → Site d => ((s : ℝ) - ⌊(s : ℝ)⌋₊ : ℝ)) :=
    measurable_const
  exact (hc₁.smul h₁).add (hc₂.smul h₂)

/-- The diffusively rescaled walk as a continuous path. -/
noncomputable def diffusiveWalkPath {d : ℕ} (R : ℝ) (X : ℕ → Site d) :
    C(ℝ≥0, Continuum.Space d) :=
  ⟨fun t => diffusiveWalk R t X, continuous_diffusiveWalk R X⟩

/-- The diffusively rescaled walk is measurable as a continuous-path-valued
random variable. -/
theorem measurable_diffusiveWalkPath {d : ℕ} (R : ℝ) :
    Measurable (diffusiveWalkPath (d := d) R) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact measurable_linearWalk R _

end Sandpile.External.Stopping
