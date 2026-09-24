/-
Theorem 1.3(ii)(a) of sandpile.tex, frozen.  `sandpile.tex:241-244`
(label `thm:main-explosion`, part (ii)(a)):

  "(ii)(a) [$d=4$] The mean odometer is of logarithmic order at each site:
   $\E u_t(0)\asymp\log t$."

This is the clause the parking paper quotes.  The two comparison constants are
bound after the law, so they do not depend on `t`.
-/
import Sandpile.Support.D4Applications

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.mean_growth_four
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℕ, 2 ≤ t →
      c * Real.log t ≤ Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t ∧
        Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t ≤ C * Real.log t
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  exact Sandpile.exists_log_mean_bounds_fixed_four ν hmean hvar hvar' θ₀ hθ₀ hexp
