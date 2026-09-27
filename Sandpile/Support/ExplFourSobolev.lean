/-
Theorem 1.3(ii)(c) of `sandpile.tex` (`sandpile.tex:255-260`) assembled from the
two propositions its proof names.  At `sandpile.tex:302-304` the proof of
`thm:main-explosion` reads "part (ii)(c) combines
Propositions~\ref{prop:d4-diffusive-tightness} and~\ref{prop:d4-superdiffusive-limit}",
and that is the whole content of the part: the first conjunct is the tightness
of `prop:d4-diffusive-tightness` at the diffusive times `⌊TR²⌋`, and the second
is the superdiffusive limit of `prop:d4-superdiffusive-limit`, one domain and
one averaging density at a time.

`prop:d4-diffusive-tightness` is sealed, so it is applied here.
`prop:d4-superdiffusive-limit` is not, so its conclusion is the hypothesis
`hSuper`, quantified over the domain, the density and the exponent exactly as
the frozen theorem quantifies them.  The two covariances agree by definition:
`Sandpile.omegaMembraneCov4 D w ν2 φ ψ` is
`omegaRep D w (fun χ => omegaRep D w (membraneCov4 ν2 χ) ψ) φ`.
-/
import Sandpile.Frozen.D4DiffusiveTightness
import Sandpile.Frozen.D4SuperdiffusiveLimit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support

/-- **Theorem 1.3(ii)(c) from the superdiffusive limit.**  The diffusive
tightness is `prop:d4-diffusive-tightness`, which is sealed; the superdiffusive
convergence is the hypothesis `hSuper`, which is the conclusion of
`prop:d4-superdiffusive-limit` at every domain, averaging density and exponent
`α > 2`. -/
theorem four_sobolev_of_superdiffusive
    (_hHeatKernel : Sandpile.External.HeatKernelBounds)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site 4 → ℝ))
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : 0 < s)
    (hSuper : ∀ D : Set (Sandpile.Continuum.Space 4), Sandpile.Continuum.IsDomain D →
      ∀ w : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsAveragingDensity D w →
      ∀ α : ℝ, 2 < α →
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
              ENNReal.ofReal ε)) :
    Sandpile.Continuum.TightInNegSobolev 4 s (Sandpile.centeredMassLaw 4 ν)
        (fun (R : ℝ) (σ : Sandpile.Site 4 → ℝ) =>
          Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊)) ∧
      ∀ D : Set (Sandpile.Continuum.Space 4), Sandpile.Continuum.IsDomain D →
        ∀ w : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsAveragingDensity D w →
          ∀ α : ℝ, 2 < α →
            (∀ φ : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsTestFn D φ →
                TendstoInDistribution
                  (fun (R : ℝ) (σ : Sandpile.Site 4 → ℝ) =>
                    Sandpile.Continuum.omegaRep D w
                      (Sandpile.Continuum.latticePairing R
                        (fun x => Sandpile.odometer σ ⌊R ^ α⌋₊ x -
                          Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)) φ)
                  atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw 4 ν)
                  (gaussianReal 0 (Real.toNNReal
                    (Sandpile.Continuum.omegaRep D w
                      (fun φ' => Sandpile.Continuum.omegaRep D w
                        (Sandpile.Continuum.membraneCov4 (variance id ν) φ') φ) φ)))) ∧
              ∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
                Sandpile.centeredMassLaw 4 ν
                    {σ | M < Sandpile.Continuum.negSobolevNorm 4 s D
                      (Sandpile.Continuum.omegaRep D w
                        (Sandpile.Continuum.latticePairing R
                          (fun x => Sandpile.odometer σ ⌊R ^ α⌋₊ x -
                            Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))} ≤
                  ENNReal.ofReal ε := by
  refine ⟨Sandpile.Frozen.d4_diffusive_tightness hBesov ν hprob hmean hvar hvar'
    T hT s hs, ?_⟩
  intro D hD w hw α hα
  exact hSuper D hD w hw α hα

end Sandpile.Support
