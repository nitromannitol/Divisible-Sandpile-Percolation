import Sandpile.Support.D4DefectBound

/-!
# Step 1 of the superdiffusive limit: the membrane part

Step 1 of `prop:d4-superdiffusive-limit` (`sandpile.tex:3341-3366`): the membrane part
`V_{t_R}` converges to `𝒢_4^ω` at the superdiffusive times `t_R = ⌊R^α⌋`.

The cited convergence of the discrete membrane field to the continuum membrane field is
`Sandpile.External.MembraneScalingLimitFour`, which carries an `ℓ²` hypothesis on the
truncation. That hypothesis is the paper's own new point, "the time truncation in `V_{t_R}`
washes out at superdiffusive times", and it is proved here, not assumed:
`Sandpile.tendsto_tsum_sq_membraneDefect`. What is left, done by `d4_superdiffusive_step1`,
is to put the two together.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

open Sandpile.Continuum

/-- **Step 1.**  At the superdiffusive times `⌊R^α⌋` with `α > 2` the
`ω`-representative of the rescaled membrane field converges in distribution to
`𝒢_4^ω`, and its `H^{-s}(D)` norms are tight. -/
theorem d4_superdiffusive_step1 (hHK : Sandpile.External.HeatKernelBounds)
    (hMembrane : Sandpile.External.MembraneScalingLimitFour)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (D : Set (Space 4)) (hD : IsDomain D) (w : Space 4 → ℝ) (hw : IsAveragingDensity D w)
    (s : ℝ) (hs : 0 < s) {α : ℝ} (hα : 2 < α) :
    (∀ φ : Space 4 → ℝ, IsTestFn D φ →
        TendstoInDistribution
          (fun (R : ℝ) (σ : Site 4 → ℝ) =>
            omegaRep D w (latticePairing R (Sandpile.membrane (Sandpile.scenery 4 σ)
              ⌊R ^ α⌋₊)) φ)
          atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw 4 ν)
          (gaussianReal 0 (Real.toNNReal
            (Sandpile.omegaMembraneCov4 D w (variance id ν) φ φ)))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
        Sandpile.centeredMassLaw 4 ν
            {σ | M < negSobolevNorm 4 s D
              (omegaRep D w (latticePairing R (Sandpile.membrane (Sandpile.scenery 4 σ)
                ⌊R ^ α⌋₊)))} ≤
          ENNReal.ofReal ε) :=
  hMembrane ν hprob hmean hvar hvar' D hD w hw s hs (fun R => ⌊R ^ α⌋₊)
    (fun _ hφ => tendsto_tsum_sq_membraneDefect hHK hw hφ hα)

end Sandpile
