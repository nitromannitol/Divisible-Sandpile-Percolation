/-
Corollary of Section 5 of sandpile.tex, frozen.  `sandpile.tex:2998-3005`
(label `cor:d4-logarithmic-mean-lower`):

  "Let $(\zeta(x))_{x\in\Z^4}$ be i.i.d., mean zero, integrable, and
   nondegenerate.  There are $c>0$ and $t_0<\infty$, depending on the one-site
   law, such that for every $t\geq t_0$, $\E u_t(0)\geq c\log t$."

The constants are allowed to depend on the one-site law, so `c` and `t₀` are
bound after `ν`, unlike in `thm:critical-toppling-d4`.  Only integrability is
assumed: there is no exponential moment and no finite-variance hypothesis, so
`evariance id ν` may be `⊤` here.  Integrability of the identity is stated
separately from the mean-zero hypothesis, since `∫ z, z ∂ν = 0` alone is also
satisfied by the junk value of a divergent integral.  "Nondegenerate" is
written as `0 < evariance id ν`, which for an integrable mean-zero law says
exactly that `ν` is not the Dirac mass at zero, the paper's meaning.
-/
import Sandpile.Law
import Sandpile.Support.D4IntegrableMean

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
