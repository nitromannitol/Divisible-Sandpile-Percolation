import Sandpile.Support.D4RieszEnergy
import Sandpile.Support.D4OmegaField
import Sandpile.Support.D4EnergyTightness

/-!
# Tightness from the centered embedding covariance

A local Riesz covariance bound on the support of a cutoff implies boundedness
in probability of the negative Sobolev norm of the centered lattice pairing.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum LatticeProb.Sobolev

/-- A local Riesz bound on the covariance of centered embeddings implies
boundedness in probability of their negative Sobolev norms. -/
theorem omegaRep_bounded_in_probability_of_riesz_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) (s β K : ℝ) (hβ : 0 < β) (hβd : β < d) (hs : β / 2 < s) (hK : 0 ≤ K)
    (D : Set (Space d)) (w χ : Space d → ℝ) (hw : IsTestFn D w)
    (hχ : IsTestFn Set.univ χ) (hχD : ∀ z ∈ D, χ z = 1)
    (X : ℝ → Site d → Ω → ℝ)
    (hXm : ∀ R, 1 ≤ R → ∀ x, Measurable (X R x))
    (hX2 : ∀ R, 1 ≤ R → ∀ x, MemLp (X R x) 2 P)
    (hX0 : ∀ R, 1 ≤ R → ∀ x, ∫ ω, X R x ω ∂P = 0)
    (hcov : ∀ R, 1 ≤ R → ∀ᵐ p : Space d × Space d ∂(volume.prod volume),
      χ p.1 ≠ 0 → χ p.2 ≠ 0 →
      |covariance (fun ω => omegaEmbed R w (fun x => X R x ω) p.1)
        (fun ω => omegaEmbed R w (fun x => X R x ω) p.2) P| ≤
          K * ‖p.1 - p.2‖ ^ (-β)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
      P {ω | M < negSobolevNorm d s D
        (omegaRep D w (latticePairing R (fun x => X R x ω)))} ≤ ENNReal.ofReal ε := by
  have hw' : IsTestFn Set.univ w := ⟨hw.1, hw.2.1, Set.subset_univ _⟩
  obtain ⟨_, L, _, _, _, hL, hwint⟩ := exists_bound_of_isTestFn hw'
  obtain ⟨_, H, _, _, _, hH, _⟩ := exists_bound_of_isTestFn hχ
  let T : {R : ℝ // 1 ≤ R} → Ω → Space d → ℝ :=
    fun R ω z => omegaEmbed R.1 w (fun x => X R.1 x ω) z
  have hTm (R : {R : ℝ // 1 ≤ R}) : Measurable (fun p : Ω × Space d => T R p.1 p.2) :=
    measurable_omegaEmbed_field R.1 L w hwint hL (X R.1) (hXm R.1 R.2)
  have hT2 (R : {R : ℝ // 1 ≤ R}) (z : Space d) : MemLp (fun ω => T R ω z) 2 P :=
    memLp_two_omegaEmbed_field P R.1 L w hwint hL (X R.1) (hX2 R.1 R.2) z
  have hT0 (R : {R : ℝ // 1 ≤ R}) (z : Space d) : ∫ ω, T R ω z ∂P = 0 :=
    integral_omegaEmbed_field P R.1 L w hwint hL (X R.1) (hX2 R.1 R.2) (hX0 R.1 R.2) z
  have hfield (R : {R : ℝ // 1 ≤ R}) : ∀ᵐ ω ∂P, Integrable (fun z => χ z * T R ω z) := by
    filter_upwards with ω
    exact (integrable_omegaEmbed_mul R.1 w (fun x => X R.1 x ω) χ hχ).congr
      (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have hB (R : {R : ℝ // 1 ≤ R}) : ∃ B : ℝ, ∀ z, χ z ≠ 0 →
      ∫ ω, T R ω z ^ 2 ∂P ≤ B :=
    exists_second_moment_bound_omegaEmbed P R.1 L H w χ hwint hL hH (X R.1)
  have hsq (R : {R : ℝ // 1 ≤ R}) (z : Space d) (_ : χ z ≠ 0) :
      Integrable (fun ω => T R ω z ^ 2) P := by
    have h := (hT2 R z).integrable_mul (hT2 R z)
    change Integrable (fun ω => T R ω z * T R ω z) P at h
    simpa only [pow_two] using h
  obtain ⟨C, hC, henergy⟩ := uniform_fourierNegEnergy_of_riesz_covariance P d β s K
    hβ hβd hs hK χ hχ T hTm hsq hB hT0 hfield (fun R => hcov R.1 R.2)
  let E : ℝ → Ω → ℝ≥0∞ := fun R ω => fourierNegEnergy d s
    (fun z => χ z * omegaEmbed R w (fun x => X R x ω) z)
  apply negSobolevNorm_bounded_in_probability_of_energy P d s D
    (fun R ω => omegaRep D w (latticePairing R (fun x => X R x ω))) E C hC
  · intro R hR
    exact aemeasurable_fourierNegEnergy_field d s P (hTm ⟨R, hR⟩).aestronglyMeasurable
      hχ.1.continuous.measurable
  · intro R hR
    exact henergy ⟨R, hR⟩
  · intro R hR ω
    exact negSobolevNorm_omegaRep_le_fourierNegEnergy s D w χ R (fun x => X R x ω) hw hχ hχD

end Sandpile.Support
