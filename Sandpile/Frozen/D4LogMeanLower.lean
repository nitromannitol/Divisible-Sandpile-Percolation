import Sandpile.Law
import Sandpile.Support.D4IntegrableMean

/-!
# Logarithmic mean lower bound in dimension four, frozen

Corollary of Section 5 of `sandpile.tex`, frozen (`sandpile.tex:2998-3005`, label
`cor:d4-logarithmic-mean-lower`): for i.i.d., mean-zero, integrable, nondegenerate scenery, there
are `c > 0` and `t₀ < ∞`, depending on the one-site law `ν`, such that `E u_t(0) ≥ c log t` for
`t ≥ t₀`. The constants may depend on `ν`, so `c` and `t₀` are bound after `ν`, unlike in
`thm:critical-toppling-d4`. Only integrability is assumed, with no exponential moment or
finite-variance hypothesis, so `evariance id ν` may be `⊤`; "nondegenerate" is `0 < evariance id ν`,
which for an integrable mean-zero law says exactly that `ν` is not the Dirac mass at zero.
-/

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_log_mean_lower
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hint : Integrable id ν)
    (hmean : ∫ z, z ∂ν = 0) (hnondeg : 0 < evariance id ν) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      c * Real.log t ≤ Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  exact Sandpile.exists_log_mean_lower_integrable_four ν hint hmean hnondeg
