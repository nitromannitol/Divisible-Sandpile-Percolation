import Sandpile.Support.D4RieszTightness

/-!
# Membrane norm control from a localized covariance estimate

The centered finite-time membrane satisfies the measurability and moment
conditions of the Riesz covariance criterion.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- A local Riesz estimate for the centered membrane covariance implies the
bounded-in-probability clause of its scaling limit. -/
theorem membrane_omegaRep_bounded_in_probability_of_riesz_covariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (s β K : ℝ)
    (hβ : 0 < β) (hβd : β < 4) (hs : β / 2 < s) (hK : 0 ≤ K)
    (D : Set (Space 4)) (w χ : Space 4 → ℝ) (hw : IsTestFn D w)
    (hχ : IsTestFn Set.univ χ) (hχD : ∀ z ∈ D, χ z = 1) (T : ℝ → ℕ)
    (hcov : ∀ R, 1 ≤ R → ∀ᵐ p : Space 4 × Space 4 ∂(volume.prod volume),
      χ p.1 ≠ 0 → χ p.2 ≠ 0 →
      |covariance (fun σ => omegaEmbed R w (membrane (scenery 4 σ) (T R)) p.1)
        (fun σ => omegaEmbed R w (membrane (scenery 4 σ) (T R)) p.2)
        (centeredMassLaw 4 ν)| ≤ K * ‖p.1 - p.2‖ ^ (-β)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
      centeredMassLaw 4 ν {σ | M < negSobolevNorm 4 s D
        (omegaRep D w (latticePairing R (membrane (scenery 4 σ) (T R))))} ≤
          ENNReal.ofReal ε := by
  apply omegaRep_bounded_in_probability_of_riesz_covariance (centeredMassLaw 4 ν)
    4 s β K hβ hβd hs hK D w χ hw hχ hχD
    (fun R x σ => membrane (scenery 4 σ) (T R) x)
  · intro R _ x
    have h := (measurable_weightedField (d := 4) (fun _ => 1) (T R) x).comp
      (measurable_scenery 4)
    simpa only [weightedField_one_eq_membrane, Function.comp_def] using h
  · intro R _ x
    simpa only [weightedField_one_eq_membrane] using
      memLp_two_weightedField_mass ν hsq (d := 4) (by norm_num) (fun _ => 1) (T R) x
  · intro R _ x
    simpa only [weightedField_one_eq_membrane] using
      integral_weightedField_mass ν hsq hmean (d := 4) (by norm_num) (fun _ => 1) (T R) x
  · exact hcov

end Sandpile.Support
