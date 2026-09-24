/-
Lemma of Section 5 of sandpile.tex, frozen.  `sandpile.tex:3002-3015`
(label `lem:d4-difference-tail`):

  "There are constants $A_0,c,C\in(0,\infty)$ such that, for all $t\geq2$ and
   all $x\in\Z^4$,
   $\E[\exp\{c(u_t(x)-V_t(x)-A_0\log(t+2))_+\}-1]\leq C(t+2)^{-2}$."

The standing hypotheses of `sec:dim4-regime` are in force in
`ssec:d4-linearization` (`sandpile.tex:2676-2679`): the scenery is mean-zero
i.i.d.\ with `0 < Var(ζ(0)) < ∞` and `E e^{θ|ζ(0)|} < ∞` for some `θ > 0`.
They are transcribed as hypotheses on the one-site law `ν`, and the field is
the i.i.d.\ field `LatticeProb.iidLaw 4 ν` on `ℤ⁴`, so that the odometer
`u_t` is `odometerOf ζ t` and the membrane field `V_t` of
`eq:membrane-recursion` is `membrane ζ t` in the same variable `ζ`.  The
constants come after the law, since the paper fixes the field first.  The
positive part is `max 0`, so the integrand is nonnegative; it is integrated as
a lower Lebesgue integral in `ℝ≥0∞`, which makes the bound FALSE rather than
vacuously true when the exponential moment fails to exist.
-/
import Sandpile.Walk
import Sandpile.External.VarianceScale
import Sandpile.Support.D4Difference

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_difference_tail
    (hVarScale : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    ∃ A₀ c C : ℝ, 0 < A₀ ∧ 0 < c ∧ 0 < C ∧
      ∀ t : ℕ, 2 ≤ t → ∀ x : Sandpile.Site 4,
        ∫⁻ ζ, ENNReal.ofReal (Real.exp (c * max 0 (Sandpile.odometerOf ζ t x -
            Sandpile.membrane ζ t x - A₀ * Real.log ((t : ℝ) + 2))) - 1)
            ∂(LatticeProb.iidLaw 4 ν) ≤
          ENNReal.ofReal (C / ((t : ℝ) + 2) ^ 2)
-- FROZEN-STATEMENT-END
:= by
  have _ := hvar
  have _ := hvar'
  obtain ⟨A₀, c, C, hA₀, hc, hC, h⟩ :=
    Sandpile.exists_difference_exp_moment_four hVarScale θ (∫ z, Real.exp (θ * |z|) ∂ν) hθ
  exact ⟨A₀, c, C, hA₀, hc, hC, fun t ht x => h ν hprob hmean hexp le_rfl t ht x⟩
