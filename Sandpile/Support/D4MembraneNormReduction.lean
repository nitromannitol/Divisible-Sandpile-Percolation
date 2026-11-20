import Sandpile.Support.D4MembraneRieszTightness
import Sandpile.Support.D4Cutoff

/-!
# Reduction of membrane norm bounds to local covariance estimates

A localized power bound for every sufficiently small positive exponent implies
the norm bound for every positive Sobolev order.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- Local Riesz bounds of arbitrarily small positive order imply the membrane
norm probability bound for every positive Sobolev order. -/
theorem membrane_omegaRep_bounded_of_local_covariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvariance : evariance id ν < ⊤) (s : ℝ) (hs : 0 < s)
    (D : Set (Space 4)) (hD : IsDomain D) (w : Space 4 → ℝ)
    (hw : IsTestFn D w) (T : ℝ → ℕ)
    (hcov : ∀ (χ : Space 4 → ℝ), IsTestFn Set.univ χ →
      ∀ β : ℝ, 0 < β → β < 4 → ∃ K : ℝ, 0 ≤ K ∧
        ∀ R, 1 ≤ R → ∀ᵐ p : Space 4 × Space 4 ∂(volume.prod volume),
          χ p.1 ≠ 0 → χ p.2 ≠ 0 →
          |covariance (fun σ => omegaEmbed R w (membrane (scenery 4 σ) (T R)) p.1)
            (fun σ => omegaEmbed R w (membrane (scenery 4 σ) (T R)) p.2)
            (centeredMassLaw 4 ν)| ≤ K * ‖p.1 - p.2‖ ^ (-β)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
      centeredMassLaw 4 ν {σ | M < negSobolevNorm 4 s D
        (omegaRep D w (latticePairing R (membrane (scenery 4 σ) (T R))))} ≤
          ENNReal.ofReal ε := by
  obtain ⟨χ, hχ, hχD⟩ := exists_testFn_eq_one_on_domain hD
  let β := min 1 s
  have hβ : 0 < β := lt_min zero_lt_one hs
  have hβd : β < 4 := lt_of_le_of_lt (min_le_left 1 s) (by norm_num)
  have hβs : β / 2 < s := by have := min_le_right (1 : ℝ) s; linarith
  obtain ⟨K, hK, hcov⟩ := hcov χ hχ β hβ hβd
  have hsq : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvariance
  exact membrane_omegaRep_bounded_in_probability_of_riesz_covariance ν hmean hsq
    s β K hβ hβd hβs hK D w χ hw hχ hχD T hcov

end Sandpile.Support
