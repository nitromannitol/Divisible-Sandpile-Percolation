/-
Measurability of the per-site visit-weighted covariance sum on the walk-pair space.

`eq:dgt4-early-derivative-variance` (`sandpile.tex:5731-5753`): the per-site integrand
of the expansion is measurable in the pair of paths, so the covariance hypothesis of
the paper applies to it.
-/
import Sandpile.Support.LinEarlyVarDefs
import Sandpile.Support.LinEarlyVarSite
import Sandpile.Support.LinEarlyVarNorm

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

theorem measurable_covSurvival_pair (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (t : Finset ℕ) (z : Site d) :
    Measurable (fun p : (ℕ → Site d) × (ℕ → Site d) =>
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = z then (1 : ℝ) else 0) *
        (if p.2 j = z then (1 : ℝ) else 0) *
        covSurvival μ n i j p.1 p.2) := by
  classical
  refine Finset.measurable_sum t fun i hi => ?_
  refine Finset.measurable_sum t fun j hj => ?_
  refine Measurable.mul ?_ ?_
  · refine Measurable.mul ?_ ?_
    · exact Measurable.ite (measurableSet_eq.preimage ((measurable_pi_apply i).comp measurable_fst))
        measurable_const measurable_const
    · exact Measurable.ite (measurableSet_eq.preimage ((measurable_pi_apply j).comp measurable_snd))
        measurable_const measurable_const
  · show Measurable (fun p : (ℕ → Site d) × (ℕ → Site d) =>
        ∫ σ : Site d → ℝ, (survivalInd σ n i p.1 - ∫ σ', survivalInd σ' n i p.1 ∂μ) *
          (survivalInd σ n j p.2 - ∫ σ', survivalInd σ' n j p.2 ∂μ) ∂μ)
    have hswap : Measurable fun q : ((ℕ → Site d) × (ℕ → Site d)) × (Site d → ℝ) =>
        (survivalInd q.2 n i q.1.1 - ∫ σ', survivalInd σ' n i q.1.1 ∂μ) *
          (survivalInd q.2 n j q.1.2 - ∫ σ', survivalInd σ' n j q.1.2 ∂μ) := by
      refine Measurable.mul ?_ ?_
      · refine Measurable.sub ?_ ?_
        · exact (measurable_uncurry_survival n i).comp
            ((measurable_snd).prodMk (measurable_fst.comp measurable_fst))
        · exact (measurable_integral_survivalInd μ n i).comp (measurable_fst.comp measurable_fst)
      · refine Measurable.sub ?_ ?_
        · exact (measurable_uncurry_survival n j).comp
            ((measurable_snd).prodMk (measurable_snd.comp measurable_fst))
        · exact (measurable_integral_survivalInd μ n j).comp (measurable_snd.comp measurable_fst)
    exact (hswap.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

end Sandpile
