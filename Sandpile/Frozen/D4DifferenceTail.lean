import Sandpile.Walk
import Sandpile.External.VarianceScale
import Sandpile.Support.D4Difference

/-!
# Exponential concentration of the odometer-membrane difference in dimension four

`Sandpile.Frozen.d4_difference_tail` is `lem:d4-difference-tail`: for a mean-zero i.i.d. scenery
on `ℤ⁴` with a finite exponential moment, there are constants `A₀, c, C > 0` such that the
exponential moment of the positive part of `u_t(x) - V_t(x) - A₀\log(t+2)` is at most
`C(t+2)^{-2}`, uniformly over `t ≥ 2` and `x`, where `u_t` is the odometer and `V_t` is the
membrane field of `eq:membrane-recursion`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_difference_tail
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
  have hVarScale : Sandpile.External.VarianceScale := Sandpile.External.varianceScale
  have _ := hvar
  have _ := hvar'
  obtain ⟨A₀, c, C, hA₀, hc, hC, h⟩ :=
    Sandpile.exists_difference_exp_moment_four hVarScale θ (∫ z, Real.exp (θ * |z|) ∂ν) hθ
  exact ⟨A₀, c, C, hA₀, hc, hC, fun t ht x => h ν hprob hmean hexp le_rfl t ht x⟩
