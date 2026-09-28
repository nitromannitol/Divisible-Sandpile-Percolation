import Sandpile.Law
import Sandpile.Frozen.D4OnePointGaussian
import Sandpile.External.VarianceScaleProved

/-!
# Theorem 1.3(ii)(b): Gaussian fluctuations in dimension four

This file proves the frozen statement of Theorem 1.3(ii)(b) (`sandpile.tex:247-253`,
`thm:main-explosion`): in dimension `d = 4`, the centered odometer
`(u_t(0) - E u_t(0)) / √(log t)` converges in distribution, `TendstoInDistribution`, to the
Gaussian law `N(0, 4 Var(ζ(0)) / π²)`, and `Var(u_t(0)) / log t` converges to the same constant.
The statement is the theorem-level instance of `prop:d4-one-point-gaussian`, and inherits its
explicit cited input, the paired local central limit theorem of `sandpile.tex:3250-3256`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.four_gaussian
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    TendstoInDistribution
      (fun (t : ℕ) (σ : Sandpile.Site 4 → ℝ) =>
        (Sandpile.odometer σ t 0 - Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t) /
          Real.sqrt (Real.log t))
      atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal (4 * variance id ν / Real.pi ^ 2))) ∧
    Tendsto (fun t : ℕ =>
      variance (fun σ => Sandpile.odometer σ t 0) (Sandpile.centeredMassLaw 4 ν) / Real.log t)
      atTop (𝓝 (4 * variance id ν / Real.pi ^ 2))
-- FROZEN-STATEMENT-END
:= by
  exact Sandpile.Frozen.d4_one_point_gaussian
    ν hmean hvar hvar' θ₀ hθ₀ hexp
