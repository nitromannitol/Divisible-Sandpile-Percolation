import Sandpile.External.Stopping.CenteredWalkInterpolation

/-!
# Recovering a lattice walk from its centered interpolation

At positive scale, the lattice positions are recovered by evaluating the
centered interpolated path at its lattice times. The reconstruction map is
measurable on continuous-path space.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The centered, diffusively interpolated path. -/
noncomputable def centeredWalkPath {d : ℕ} (R : ℝ) (q : Site d) (X : ℕ → Site d) :
    C(ℝ≥0, Continuum.Space d) :=
  ⟨fun t => diffusiveWalk R t X - Lclt.scaledSite R q,
    (continuous_diffusiveWalk R X).sub continuous_const⟩

/-- The centered path is measurable as a function of the lattice walk. -/
theorem measurable_centeredWalkPath {d : ℕ} (R : ℝ) (q : Site d) :
    Measurable (centeredWalkPath R q) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (measurable_linearWalk R _).sub measurable_const

/-- Read the successive lattice sites from a centered continuous path. -/
noncomputable def decodeCenteredWalk {d : ℕ} (R : ℝ) (q : Site d)
    (f : C(ℝ≥0, Continuum.Space d)) : ℕ → Site d :=
  fun k i => ⌊R * f (LatticeProb.ConstantStepInterpolation.knot ⟨R ^ 2, sq_nonneg R⟩ k) i⌋ + q i

/-- Reading lattice sites from a centered continuous path is measurable. -/
theorem measurable_decodeCenteredWalk {d : ℕ} (R : ℝ) (q : Site d) :
    Measurable (decodeCenteredWalk R q) := by
  apply measurable_pi_iff.2
  intro k
  apply measurable_pi_iff.2
  intro i
  exact ((Int.measurable_floor.comp (measurable_const.mul
    ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable.comp
      (continuous_eval_const _).measurable))).add measurable_const)

/-- Decoding a centered interpolation recovers every site of the walk. -/
theorem decodeCenteredWalk_centeredWalkPath {d : ℕ} {R : ℝ} (hR : 0 < R)
    (q : Site d) (X : ℕ → Site d) : decodeCenteredWalk R q (centeredWalkPath R q X) = X := by
  ext k i
  have hm : (0 : ℝ≥0) < ⟨R ^ 2, sq_nonneg R⟩ := by
    change (0 : ℝ) < R ^ 2
    positivity
  have hp := LatticeProb.ConstantStepInterpolation.path_knot hm (centeredScaledSite R q ∘ X) k
  change LatticeProb.ConstantStepInterpolation.path (R ^ 2) (centeredScaledSite R q ∘ X)
      (LatticeProb.ConstantStepInterpolation.knot ⟨R ^ 2, sq_nonneg R⟩ k) =
      centeredScaledSite R q (X k) at hp
  rw [centered_constantStep_path_eq_diffusiveWalk] at hp
  change ⌊R * ((diffusiveWalk R _ X - Lclt.scaledSite R q) i)⌋ + q i = X k i
  rw [hp]
  change ⌊R * (((X k i - q i : ℤ) : ℝ) / R)⌋ + q i = X k i
  have heq : R * (((X k i - q i : ℤ) : ℝ) / R) = ((X k i - q i : ℤ) : ℝ) := by
    field_simp
  rw [heq, Int.floor_intCast]
  exact sub_add_cancel _ _

end Sandpile.External.Stopping
