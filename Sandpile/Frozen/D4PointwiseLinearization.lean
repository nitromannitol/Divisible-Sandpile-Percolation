/-
Proposition of Section 5 of sandpile.tex, frozen.  `sandpile.tex:3060-3075`
(label `prop:d4-pointwise-linearization`):

  "There are constants $c,C\in(0,\infty)$ such that, for all integers $t\geq3$
   and all $\lambda\geq0$,
   $\sup_{x\in\Z^4}\P(|u_t(x)-\E u_t(0)-V_t(x)|>\lambda)
    \leq C\exp\{-c\min(\lambda^2/(1+\log\log t),\lambda)\}$."

The standing hypotheses of `sec:dim4-regime` are in force in
`ssec:d4-linearization` (`sandpile.tex:2676-2679`): mean-zero i.i.d.\ scenery
with `0 < Var(ζ(0)) < ∞` and an exponential moment.  The field is
`LatticeProb.iidLaw 4 ν`, so `u_t` is `odometerOf ζ t`, `V_t` is
`membrane ζ t`, and `E u_t(0)` is the integral of `odometerOf ζ t 0` against
that same law.  The constants come after the law.  The supremum over `x` is
written as a universally quantified `x` inside the bound, which is the same
statement and avoids an `sSup` junk value.  The bound is on the measure of the
deviation event in `ℝ≥0∞`, against `ENNReal.ofReal` of the paper's right-hand
side.  The threshold `t ≥ 3` is the paper's; it keeps `1 + log log t`
positive, so the ratio `λ²/(1 + log log t)` has no division by zero.
-/
import Sandpile.Walk
import Sandpile.External.VarianceScale
import Sandpile.Support.D4PointwiseTail

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_pointwise_linearization
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ t : ℕ, 3 ≤ t → ∀ lam : ℝ, 0 ≤ lam → ∀ x : Sandpile.Site 4,
        LatticeProb.iidLaw 4 ν
            {ζ | lam < |Sandpile.odometerOf ζ t x -
              (∫ η, Sandpile.odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) -
              Sandpile.membrane ζ t x|} ≤
          ENNReal.ofReal (C * Real.exp
            (-(c * min (lam ^ 2 / (1 + Real.log (Real.log t))) lam)))
-- FROZEN-STATEMENT-END
:= by
  have hVarScale : Sandpile.External.VarianceScale := Sandpile.External.varianceScale
  have _ := hvar
  have _ := hvar'
  haveI := hprob
  exact Sandpile.exists_pointwise_linearization_four hVarScale ν hmean θ hθ hexp
