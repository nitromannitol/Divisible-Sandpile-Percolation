import Sandpile.External.Stopping.StepRewardIntegrable

/-!
# Joint measurability of the diffusive step walk

The floor-time index and countable coordinate evaluation give joint
measurability in physical time and the lattice trajectory.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The diffusively rescaled step walk is jointly measurable in time and path. -/
theorem measurable_diffusiveStepWalk_uncurry {d : ℕ} (R : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → Site d) => diffusiveStepWalk R p.1 p.2) := by
  have hi : Measurable (fun p : ℝ≥0 × (ℕ → Site d) => diffusiveTimeIndex R p.1) :=
    Nat.measurable_floor.comp (measurable_const.mul (measurable_coe_nnreal_real.comp measurable_fst))
  have heval : Measurable (fun p : (ℕ → Site d) × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  have hpos : Measurable (fun p : ℝ≥0 × (ℕ → Site d) =>
      Lclt.scaledSite R (p.2 (diffusiveTimeIndex R p.1))) :=
    (measurable_of_countable (Lclt.scaledSite (d := d) R)).comp
      (heval.comp (measurable_snd.prodMk hi))
  convert hpos using 1
  funext p
  exact diffusiveStepWalk_eq_at_index R p.1 p.2

end Sandpile.External.Stopping
