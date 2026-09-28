import Sandpile.Law
import Sandpile.External.VarianceScale
import Sandpile.External.PairedLocalCLTFourProved
import Sandpile.Support.D4Gaussian

/-!
# The one-point Gaussian limit in dimension four

This file proves the frozen section-level statement of `prop:d4-one-point-gaussian`
(`sandpile.tex:3270-3283`), the mass-normalized form of Theorem 1.3(ii)(b). Under the standing
hypotheses of `sec:dim4-regime` (`sandpile.tex:2676-2679`), namely mean-zero i.i.d. scenery with
`0 < Var(ζ(0)) < ∞` and a finite exponential moment `E e^{θ|ζ(0)|}` for some `θ > 0`, the
centered odometer `(u_t(0) - E u_t(0)) / √(log t)` converges in distribution to
`N(0, 4 Var(ζ(0)) / π²)`, and `Var(u_t(0)) / log t` converges to the same constant. The paired
local central limit theorem of `sandpile.tex:3250-3256` is taken as an explicit cited input,
while the weighted independent-row central limit theorem and the second-moment transfer from the
membrane that the proof also needs are proved locally.
-/

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
