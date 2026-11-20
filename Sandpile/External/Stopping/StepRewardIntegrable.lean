import Sandpile.External.Stopping.RoundedRewardIntegral
import LatticeProb.Prob.BrownianDriftExitMoment

/-!
# Integrability of stopped step-walk rewards

Bounded measurable rewards at natural-filtration step-walk stopping times and
at their rounded lattice times are integrable under the walk law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A natural-filtration stopping time is measurable when each process
observation is measurable in the ambient space. -/
theorem measurable_of_isBrownianStopping {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : ∀ t, Measurable (B t))
    (θ : Ω → ℝ≥0) (hθ : Continuum.IsBrownianStopping B θ) : Measurable θ := by
  have hs : IsStoppingTime (Filtration.const ℝ≥0 (inferInstance : MeasurableSpace Ω) le_rfl)
      (fun ω => (θ ω : ℝ≥0∞)) := by
    intro t
    exact (Continuum.brownianFiltration_le B t inferInstance (fun s _ => hB s)) _ (hθ t)
  exact measurable_coe_nnreal_ennreal_iff.mp (LatticeProb.measurable_of_isStoppingTime_enn hs)

/-- A fixed-time observation of the diffusive step walk is measurable. -/
theorem measurable_diffusiveStepWalk {d : ℕ} (R : ℝ) (t : ℝ≥0) :
    Measurable (diffusiveStepWalk (d := d) R t) := by
  have heq : diffusiveStepWalk (d := d) R t =
      fun X => Lclt.scaledSite R (X (diffusiveTimeIndex R t)) := by
    funext X
    exact diffusiveStepWalk_eq_at_index R t X
  rw [heq]
  exact (measurable_of_countable (Lclt.scaledSite (d := d) R)).comp (measurable_pi_apply _)

/-- A natural-filtration stopping time of the diffusive step walk is measurable
in the ambient lattice path space. -/
theorem measurable_of_diffusiveStepWalk_stopping {d : ℕ} (R : ℝ)
    (θ : (ℕ → Site d) → ℝ≥0) (hθ : Continuum.IsBrownianStopping (diffusiveStepWalk R) θ) :
    Measurable θ :=
  measurable_of_isBrownianStopping (diffusiveStepWalk R) (measurable_diffusiveStepWalk R) θ hθ

/-- The rounded lattice index and its site are measurable for a step-walk
stopping time. -/
theorem measurable_diffusiveTimeIndex_and_site {d : ℕ} (R : ℝ)
    (θ : (ℕ → Site d) → ℝ≥0) (hθ : Continuum.IsBrownianStopping (diffusiveStepWalk R) θ) :
    Measurable (fun X => diffusiveTimeIndex R (θ X)) ∧
      Measurable (fun X : ℕ → Site d => X (diffusiveTimeIndex R (θ X))) := by
  have hθm := measurable_of_diffusiveStepWalk_stopping R θ hθ
  have hi : Measurable (fun X => diffusiveTimeIndex R (θ X)) := by
    exact Nat.measurable_floor.comp (measurable_const.mul (measurable_coe_nnreal_real.comp hθm))
  refine ⟨hi, ?_⟩
  have heval : Measurable (fun p : (ℕ → Site d) × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  exact heval.comp (measurable_id.prodMk hi)

/-- A bounded measurable reward at a diffusive step-walk stopping time is
integrable. -/
theorem integrable_diffusiveStepWalk_stopped_reward {d : ℕ} [NeZero d] (R : ℝ) (x : Site d)
    (T M : ℝ) (G : ℝ → Continuum.Space d → ℝ)
    (hG : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hM : ∀ s z, |G s z| ≤ M) (θ : (ℕ → Site d) → ℝ≥0)
    (hθ : Continuum.IsBrownianStopping (diffusiveStepWalk R) θ) :
    Integrable (fun X => G (T - θ X) (diffusiveStepWalk R (θ X) X)) (walkLaw d x) := by
  let : IsProbabilityMeasure (walkLaw d x) := by
    change IsProbabilityMeasure (LatticeProb.siteWalkLaw d x)
    infer_instance
  have hθm := measurable_of_diffusiveStepWalk_stopping R θ hθ
  have hs := (measurable_diffusiveTimeIndex_and_site R θ hθ).2
  have hpos : Measurable (fun X => diffusiveStepWalk R (θ X) X) := by
    have heq : (fun X : ℕ → Site d => diffusiveStepWalk R (θ X) X) =
        fun X => Lclt.scaledSite R (X (diffusiveTimeIndex R (θ X))) := by
      funext X
      exact diffusiveStepWalk_eq_at_index R (θ X) X
    rw [heq]
    exact (measurable_of_countable (Lclt.scaledSite (d := d) R)).comp hs
  have hreward : Measurable (fun X => G (T - θ X) (diffusiveStepWalk R (θ X) X)) :=
    hG.comp ((measurable_const.sub (measurable_coe_nnreal_real.comp hθm)).prodMk hpos)
  apply (integrable_const M).mono' hreward.aestronglyMeasurable
  filter_upwards with X
  simpa only [Real.norm_eq_abs] using hM (T - θ X) (diffusiveStepWalk R (θ X) X)

/-- A bounded measurable reward at the rounded lattice time and site is
integrable. -/
theorem integrable_diffusiveStepWalk_rounded_reward {d : ℕ} [NeZero d] {R : ℝ} (hR : 0 < R)
    (x : Site d) (T M : ℝ) (G : ℝ → Continuum.Space d → ℝ)
    (hG : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hM : ∀ s z, |G s z| ≤ M) (θ : (ℕ → Site d) → ℝ≥0)
    (hθ : Continuum.IsBrownianStopping (diffusiveStepWalk R) θ) :
    Integrable (fun X => G (T - roundDiffusiveTime R hR (θ X))
      (Lclt.scaledSite R (X (diffusiveTimeIndex R (θ X))))) (walkLaw d x) := by
  let : IsProbabilityMeasure (walkLaw d x) := by
    change IsProbabilityMeasure (LatticeProb.siteWalkLaw d x)
    infer_instance
  obtain ⟨hi, hs⟩ := measurable_diffusiveTimeIndex_and_site R θ hθ
  have ht : Measurable (fun X => roundDiffusiveTime R hR (θ X)) := by
    exact (measurable_of_countable (fun n : ℕ =>
      (n : ℝ≥0) / ⟨R ^ 2, sq_nonneg R⟩)).comp hi
  have hz : Measurable (fun X : ℕ → Site d => Lclt.scaledSite R (X (diffusiveTimeIndex R (θ X)))) :=
    (measurable_of_countable (Lclt.scaledSite (d := d) R)).comp hs
  have hreward : Measurable (fun X => G (T - roundDiffusiveTime R hR (θ X))
      (Lclt.scaledSite R (X (diffusiveTimeIndex R (θ X))))) :=
    hG.comp ((measurable_const.sub (measurable_coe_nnreal_real.comp ht)).prodMk hz)
  apply (integrable_const M).mono' hreward.aestronglyMeasurable
  filter_upwards with X
  simpa only [Real.norm_eq_abs] using hM (T - roundDiffusiveTime R hR (θ X))
    (Lclt.scaledSite R (X (diffusiveTimeIndex R (θ X))))

end Sandpile.External.Stopping
