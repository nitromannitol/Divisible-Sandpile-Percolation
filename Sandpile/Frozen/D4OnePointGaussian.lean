/-
Proposition of Section 5 of sandpile.tex, frozen.  `sandpile.tex:3270-3283`
(label `prop:d4-one-point-gaussian`):

  "As $t\to\infty$,
   $\frac{u_t(0)-\E u_t(0)}{\sqrt{\log t}}\Longrightarrow
    N\left(0,\frac{4\Var(\zeta(0))}{\pi^2}\right)$, and
   $\frac{\Var(u_t(0))}{\log t}\longrightarrow\frac{4\Var(\zeta(0))}{\pi^2}$."

This is the section-level version of Theorem 1.3(ii)(b).  The hypotheses are
the standing ones of `sec:dim4-regime` (`sandpile.tex:2676-2679`): the scenery
is mean-zero i.i.d.\ with `0 < Var(ζ(0)) < ∞` and `E e^{θ|ζ(0)|} < ∞` for some
`θ > 0`; on this law they coincide with the hypotheses of Theorem 1.3, and the
exponential-moment constant is named `θ` after the paper's standing sentence
rather than `θ₀`.  Convergence in distribution and the variance limit are
written exactly as in the frozen Theorem 1.3(ii)(b): `TendstoInDistribution`
with the identity variable under `gaussianReal`, whose variance argument is
`Real.toNNReal` of the paper's `4 Var(ζ(0))/π²`, and `variance` of the
odometer against `centeredMassLaw 4 ν`.

The paired local central limit theorem used at `sandpile.tex:3250-3256`
is an explicit cited input. The weighted independent-row central limit theorem
and the second-moment transfer from the membrane are proved locally.
-/
import Sandpile.Law
import Sandpile.External.VarianceScale
import Sandpile.External.PairedLocalCLTFourProved
import Sandpile.Support.D4Gaussian

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_one_point_gaussian
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
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
  have hVarScale : Sandpile.External.VarianceScale := Sandpile.External.varianceScale
  have _hPositive := hvar
  have hsq : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  exact Sandpile.odometer_gaussian_four_mass hVarScale Sandpile.External.pairedLocalCLTFour ν
    hsq hmean θ hθ hexp
