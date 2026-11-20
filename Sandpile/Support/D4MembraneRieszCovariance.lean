import Sandpile.Support.D4MembraneLogCovariance
import Sandpile.Support.D4DefectOmega

/-!
# Local Riesz covariance bound for the centered membrane

A logarithmic singularity on a bounded set is dominated by any negative
power of the distance. This gives the local covariance estimate for the
four-dimensional membrane embedding.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- On a bounded interval, a constant plus a logarithmic singularity is
bounded by any strictly negative power. -/
theorem exists_const_add_log_le_rpow (A B H β : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hβ : 0 < β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 0 < r → r ≤ H →
      A + B * max 0 (Real.log r⁻¹) ≤ K * r ^ (-β) := by
  let C : ℝ := max 1 H
  let c : ℝ := C ^ (-β)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc : 0 < c := Real.rpow_pos_of_pos hC _
  refine ⟨A / c + B * β⁻¹, by positivity, ?_⟩
  intro r hr hrH
  have hrC : r ≤ C := hrH.trans (le_max_right _ _)
  have hpow : c ≤ r ^ (-β) := Real.rpow_le_rpow_of_nonpos hr hrC (by linarith)
  have hratio : 1 ≤ r ^ (-β) / c := (one_le_div hc).2 hpow
  have hlog := log_inv_pos_part_le_rpow hr hβ
  have h1 := mul_le_mul_of_nonneg_left hratio hA
  have h2 := mul_le_mul_of_nonneg_left hlog hB
  have heq : A * (r ^ (-β) / c) + B * (β⁻¹ * r ^ (-β)) =
      (A / c + B * β⁻¹) * r ^ (-β) := by ring
  linarith

/-- The centered membrane covariance satisfies the local Riesz estimate needed
for the negative Sobolev norm bound. -/
theorem exists_membrane_omegaEmbed_riesz_covariance_bound
    (hPaired : External.PairedLocalCLTFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (D : Set (Space 4)) (w : Space 4 → ℝ) (hw : IsAveragingDensity D w)
    (χ : Space 4 → ℝ) (hχ : IsTestFn Set.univ χ) (β : ℝ) (hβ : 0 < β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∀ᵐ p : Space 4 × Space 4 ∂(volume.prod volume),
        χ p.1 ≠ 0 → χ p.2 ≠ 0 →
        |covariance (fun σ => omegaEmbed R w (membrane (scenery 4 σ) t) p.1)
          (fun σ => omegaEmbed R w (membrane (scenery 4 σ) t) p.2)
          (centeredMassLaw 4 ν)| ≤ K * ‖p.1 - p.2‖ ^ (-β) := by
  have hwt : IsTestFn Set.univ w := ⟨hw.1.1, hw.1.2.1, Set.subset_univ _⟩
  obtain ⟨W, Lw, hW, _, hwB, hwL, hwi⟩ := exists_bound_of_isTestFn hwt
  obtain ⟨_, Lχ, _, _, _, hχL, _⟩ := exists_bound_of_isTestFn hχ
  let L := max Lw Lχ
  have hwL' : ∀ z, w z ≠ 0 → ‖z‖ ≤ L := fun z hz =>
    (hwL z hz).trans (le_max_left _ _)
  have hχL' : ∀ z, χ z ≠ 0 → ‖z‖ ≤ L := fun z hz =>
    (hχL z hz).trans (le_max_right _ _)
  have hw1 : ∫ z, w z = 1 := by
    rw [← setIntegral_eq_integral_of_isTestFn hw.1]
    exact hw.2.2
  obtain ⟨A, B, hA, hB, hlog⟩ :=
    exists_membrane_omegaEmbed_log_covariance_bound hPaired ν hsq w hwi hw.2.1
      hw1 W L hW hwB hwL'
  obtain ⟨K, hK, hpower⟩ := exists_const_add_log_le_rpow A B (2 * L) β hA hB hβ
  refine ⟨K, hK, ?_⟩
  intro t R hR
  filter_upwards [LatticeProb.Sobolev.ae_ne_diagonal 4 (by norm_num)] with p hp hχ1 hχ2
  have hdist : ‖p.1 - p.2‖ ≤ 2 * L := by
    have := norm_sub_le p.1 p.2
    linarith [hχL' p.1 hχ1, hχL' p.2 hχ2]
  have hr : 0 < ‖p.1 - p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  exact (hlog t R hR p.1 p.2 (hχL' p.1 hχ1) (hχL' p.2 hχ2) hp).trans
    (hpower ‖p.1 - p.2‖ hr hdist)

end Sandpile.Support
