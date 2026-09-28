import Sandpile.Law
import Sandpile.Continuum.Membrane
import Sandpile.External.ContinuumBesovTightness
import Sandpile.External.LocalCLT
import Sandpile.External.HeatKernelBoundsProved
import Sandpile.External.GreenBoundsHighProved
import Sandpile.Support.ExplHighSobolev

/-!
# Theorem 1.3(iii)(c): the high-Sobolev scaling limit above dimension four

This file proves the frozen statement of Theorem 1.3(iii)(c) (`sandpile.tex:274-285`,
`thm:main-explosion`), for `d ≥ 5` scenery with mean zero and finite positive variance. For
Gaussian scenery, the rescaled centered odometer `R^{(d-4)/2} (u_{⌊TR²⌋} - E u_{⌊TR²⌋}(0))^{(R)}`
converges in `H^{-s}_{loc}(ℝ^d)` (`TendstoInNegSobolev`) to the centered Gaussian field of
covariance `weightedMembraneCov d (Var ζ(0)) 1 T`, for every `T > 0` and `s > (d-4)/2`. If instead
the scenery is atomless, bounded above, with a regularly varying lower tail of index `-α`,
`α > 2`, the same rescaled odometer converges to the field of covariance
`weightedMembraneCov d (Var ζ(0)) (1 - 1/α) T`. The proof inherits the cited inputs of
`thm:dgt4-diffusive-membrane`: Gaussian concentration, the normal comparison, the intersection
second moment, the local central limit theorem, and the Besov tightness criterion, while the
heat-kernel bounds and the `d ≥ 5` Green estimates are already discharged unconditionally.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.high_sobolev_limit
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hNormal : Sandpile.External.NormalComparison)
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤) :
    (∀ v : ℝ≥0, ν = gaussianReal 0 v →
        ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
          Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
            (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
              R ^ (((d : ℝ) - 4) / 2) *
                Sandpile.Continuum.latticePairing R
                  (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
                    Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ)
            (Sandpile.Continuum.weightedMembraneCov d (variance id ν) 1 T)) ∧
      ((∀ z : ℝ, ν {z} = 0) → (∃ b : ℝ, ν (Set.Ioi b) = 0) →
        ∀ α : ℝ, 2 < α →
          (∀ lam : ℝ, 0 < lam →
              Tendsto (fun r : ℝ =>
                  (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
                atTop (𝓝 (lam ^ (-α)))) →
          ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
            Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
              (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
                R ^ (((d : ℝ) - 4) / 2) *
                  Sandpile.Continuum.latticePairing R
                    (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
                      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ)
              (Sandpile.Continuum.weightedMembraneCov d (variance id ν) (1 - 1 / α) T))
-- FROZEN-STATEMENT-END
:=
  Sandpile.Support.high_sobolev_limit_of_membrane hd ν hmean hvar hvar'
    (fun κ hatom hcase =>
      (Sandpile.Frozen.dgt4_diffusive_membrane
        hGaussConc hNormal
        d hd hBesov ν hatom hmean hvar hvar' κ hcase).1)
