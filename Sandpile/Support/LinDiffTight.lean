import Sandpile.Support.TightWeightedMembrane

/-!
# Tightness of the odometer/weighted-linear-field difference

The difference of the rescaled centred odometer and the weighted linear field is
tight in `H^{-s}_loc(ℝ^d)`: both families are tight, so their difference is, by
`tight_sub`.  This is the tightness half of the second conjunct of
`lem:dgt4-linearization-from-survival` (`sandpile.tex:5841-5849`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

variable {d : ℕ}

/-- The difference of the rescaled centred odometer and the weighted linear field
is tight in `H^{-s}_loc(ℝ^d)`. -/
theorem dgt4_difference_tight (hGH : Sandpile.External.GreenBoundsHigh)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (hpos : Integrable (fun z => max z 0) ν)
    (hmean : ∫ z, z ∂ν = 0)
    (T : ℝ) (hT : 0 < T) (q : ℝ → ℝ) (Q : ℝ) (hQ0 : 0 ≤ Q)
    (hQ : ∀ r ∈ Set.Icc (0 : ℝ) T, |q r| ≤ Q) (s : ℝ) (hs : ((d : ℝ) - 4) / 2 < s) :
    Sandpile.Continuum.TightInNegSobolev d s (Sandpile.centeredMassLaw d ν)
      (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
        R ^ (((d : ℝ) - 4) / 2) *
            Sandpile.Continuum.latticePairing R
              (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
                Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) φ
          - R ^ (((d : ℝ) - 4) / 2) *
            Sandpile.Continuum.latticePairing R
              (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
                q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) := by
  exact Sandpile.Support.tight_sub s (Sandpile.centeredMassLaw d ν) _ _
    (Sandpile.Support.dgt4_odometer_tight hGH hBesov hd ν hsq hpos T hT s hs)
    (Sandpile.Support.weighted_membrane_tight hGH hBesov hd ν
      ((MeasureTheory.memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq) hmean T hT q Q
      hQ0 hQ s hs)

end Sandpile.Support
