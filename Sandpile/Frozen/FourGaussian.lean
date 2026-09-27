/-
Theorem 1.3(ii)(b) of sandpile.tex, frozen.  `sandpile.tex:247-253`
(label `thm:main-explosion`, part (ii)(b)):

  "[$d=4$] The centered odometer $u_t(0)-\E u_t(0)$ has Gaussian fluctuations:
   $(u_t(0)-\E u_t(0))/\sqrt{\log t}\Rightarrow N(0, 4\Var(\zeta(0))/\pi^2)$,
   and $\Var(u_t(0))/\log t\to4\Var(\zeta(0))/\pi^2$."

Convergence in distribution is Mathlib's `TendstoInDistribution`, with the
limit the identity variable under the Gaussian law of the stated variance.
The paired local central limit theorem is the explicit cited input used by
Proposition `prop:d4-one-point-gaussian` at `sandpile.tex:3250-3256`.
-/
import Sandpile.Law
import Sandpile.Frozen.D4OnePointGaussian
import Sandpile.External.VarianceScaleProved

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.four_gaussian
    (hPaired : Sandpile.External.PairedLocalCLTFour)
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
  exact Sandpile.Frozen.d4_one_point_gaussian hPaired
    ν hmean hvar hvar' θ₀ hθ₀ hexp
