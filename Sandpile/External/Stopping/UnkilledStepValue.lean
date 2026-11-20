import Sandpile.External.Stopping.KilledStepHorizon
import Sandpile.External.Stopping.StoppingValueLowerLimit

/-!
# Unkilled step-walk stopping values

Translation preserves the natural stopping class, and killing on the whole
space imposes no restriction on lattice or step-walk stopping times.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Translating every position by the same constant preserves natural stops. -/
theorem isBrownianStopping_sub_const_iff {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (c : Continuum.Space d) (τ : Ω → ℝ≥0) :
    Continuum.IsBrownianStopping (fun t ω => B t ω - c) τ ↔
      Continuum.IsBrownianStopping B τ := by
  have hleft (t : ℝ≥0) : Continuum.brownianFiltration (fun s ω => B s ω - c) t ≤
      Continuum.brownianFiltration B t := by
    apply Continuum.brownianFiltration_le
    intro s hs
    exact (Continuum.measurable_brownianFiltration B s t hs).sub_const c
  have hright (t : ℝ≥0) : Continuum.brownianFiltration B t ≤
      Continuum.brownianFiltration (fun s ω => B s ω - c) t := by
    apply Continuum.brownianFiltration_le
    intro s hs
    have h := (Continuum.measurable_brownianFiltration (fun u ω => B u ω - c) s t hs).add_const c
    simpa using h
  constructor
  · intro h t
    exact hleft t _ (h t)
  · intro h t
    exact hright t _ (h t)

/-- The whole-space killed lattice value is the ordinary lattice value. -/
theorem killedStoppingSup_univ {d : ℕ} (N : ℕ) (x : Site d)
    (F : ℕ → (ℕ → Site d) → ℝ) :
    killedStoppingSup Set.univ N x F = stoppingSup N x F := by
  unfold killedStoppingSup stoppingSup
  congr 1
  ext a
  simp only [killedSet, Set.mem_ofPred_eq, Set.mem_univ, implies_true, true_and]

/-- The centered step-walk stopping values agree with the whole-space
step-walk values after translating the reward. -/
theorem naturalStoppingPayoffs_centered_eq_univ {d : ℕ} (R : ℝ) (x : Site d)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ) :
    naturalStoppingPayoffs (walkLaw d x)
      (fun t X => diffusiveStepWalk R t X - Lclt.scaledSite R x) T
      (fun t z => G ((T : ℝ) - t) (z + Lclt.scaledSite R x)) =
      killedStepTimePayoffs R Set.univ x T G := by
  ext a
  simp only [naturalStoppingPayoffs, killedStepTimePayoffs, Set.mem_ofPred_eq,
    isBrownianStopping_sub_const_iff, NNReal.coe_le_coe, Set.mem_univ, implies_true,
    eventually_true, true_and, sub_add_cancel]

end Sandpile.External.Stopping
