import Sandpile.Law
import Sandpile.Continuum.Membrane
import Sandpile.External.HeatKernelBounds
import Sandpile.External.MembraneScalingFour
import Sandpile.External.VarianceScale
import Sandpile.Support.D4STightness

/-!
# The superdiffusive membrane limit in dimension four, frozen

Proposition of Section 5 of `sandpile.tex`, frozen (`sandpile.tex:3356-3364`, label
`prop:d4-superdiffusive-limit`): fixing a bounded smooth domain `D ⊂ ℝ⁴`, an averaging density
`ω`, and `α > 2`, the recentred, rescaled, `ω`-paired odometer field converges as `R → ∞` to the
four-dimensional continuum membrane model `𝒢_4^ω` in `H^{-s}(D)`, for every `s > 0`. The scenery
`ζ` is carried by `centeredMassLaw 4 ν`, `u_t` is `Sandpile.odometer σ t`, `E u_t(0)` is
`Sandpile.meanOdometer`, the domain and density hypotheses are `IsDomain D` and
`IsAveragingDensity D w`, and both sides carry the `ω`-representative `omegaRep D w` of
`eq:d4-omega-representative`, with limit covariance `omegaMembraneCov4 D w (variance id ν)`.
Convergence is stated for the fixed domain `D` alone, as two clauses inline rather than through
`Sandpile.Continuum.TendstoInNegSobolev`'s `H^{-s}_loc(ℝ^4)` quantification. The cited input is
`Sandpile.External.MembraneScalingLimitFour`, the convergence of the discrete membrane field to
the continuum one for the four-dimensional potential kernel; the paper's own new point, that time
truncation washes out at superdiffusive times, is proved rather than assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_superdiffusive_limit
    (hMembrane : Sandpile.External.MembraneScalingLimitFour)
    (D : Set (Sandpile.Continuum.Space 4)) (hD : Sandpile.Continuum.IsDomain D)
    (w : Sandpile.Continuum.Space 4 → ℝ)
    (hw : Sandpile.Continuum.IsAveragingDensity D w)
    (α : ℝ) (hα : 2 < α)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (s : ℝ) (hs : 0 < s) :
    (∀ φ : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsTestFn D φ →
        TendstoInDistribution
          (fun (R : ℝ) (ω : Sandpile.Site 4 → ℝ) =>
            Sandpile.Continuum.omegaRep D w
              (Sandpile.Continuum.latticePairing R
                (fun x => Sandpile.odometer ω ⌊R ^ α⌋₊ x -
                  Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)) φ)
          atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw 4 ν)
          (gaussianReal 0 (Real.toNNReal
            (Sandpile.omegaMembraneCov4 D w (variance id ν) φ φ)))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
        Sandpile.centeredMassLaw 4 ν
            {ω | M < Sandpile.Continuum.negSobolevNorm 4 s D
              (Sandpile.Continuum.omegaRep D w
                (Sandpile.Continuum.latticePairing R
                  (fun x => Sandpile.odometer ω ⌊R ^ α⌋₊ x -
                    Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))} ≤
          ENNReal.ofReal ε)
-- FROZEN-STATEMENT-END
:= by
  have hHeatKernel : Sandpile.External.HeatKernelBounds := Sandpile.External.heatKernelBounds
  have hVarScale : Sandpile.External.VarianceScale := Sandpile.External.varianceScale
  haveI := hprob
  -- the moment hypotheses the two clauses consume, from the finite variance
  have hsqm : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hsq2 : Integrable (fun z : ℝ => z ^ 2) ν := by simpa using hsqm.integrable_sq
  have hint : Integrable (id : ℝ → ℝ) ν := hsqm.integrable (by norm_num)
  have hpos : Integrable (fun z : ℝ => max z 0) ν := by
    refine hint.abs.mono' (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    rcases le_or_gt 0 z with hz | hz
    · rw [max_eq_left hz]
      simp
    · rw [max_eq_right (le_of_lt hz), abs_zero]
      simp
  refine ⟨fun φ hφ => ?_, fun ε hε => ?_⟩
  · exact Sandpile.d4_superdiffusive_first_clause hHeatKernel hVarScale hMembrane ν hprob
      hmean hvar hvar' θ₀ hθ₀ hexp hint hpos hD hw hα hs hφ
  · exact Sandpile.Support.d4_superdiffusive_tightness hHeatKernel hVarScale hMembrane ν hprob
      hmean hvar hvar' θ₀ hθ₀ hexp hint hpos hsq2 hD hw hα hs hε
