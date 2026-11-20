import LatticeProb.Prob.NegSobolevTightness

/-!
# Negative Sobolev energy from a Riesz covariance bound

A local covariance singularity of order less than the dimension controls the
expected negative Sobolev energy. The heat-kernel argument adapts the
covariance estimate in `LatticeProb/Prob/NegSobolevTightness.lean` to a
Riesz bound that need only hold almost everywhere.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal FourierTransform

namespace Sandpile.Support

open LatticeProb.Sobolev

/-- A Riesz bound on a covariance kernel controls its heat-kernel integral. -/
theorem heat_covariance_integral_bound_of_riesz (d : ℕ) (β : ℝ)
    (hβ : 0 < β) (hβd : β < d) {f : Space d → ℝ} {B K : ℝ}
    (hfm : StronglyMeasurable f) (hfi : Integrable f)
    (hfB : ∀ x, |f x| ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ c : Space d × Space d → ℝ,
      Integrable (fun p => (f p.1 * f p.2 * heatKernel d t (p.1 - p.2)) * c p)
        (volume.prod volume) →
      (∀ᵐ p ∂(volume.prod volume), f p.1 ≠ 0 → f p.2 ≠ 0 →
        |c p| ≤ K * ‖p.1 - p.2‖ ^ (-β)) →
      (∫ p : Space d × Space d,
        (f p.1 * f p.2 * heatKernel d t (p.1 - p.2)) * c p ∂(volume.prod volume)) ≤
          K * (B * (C * t ^ (-β / 2)) * ∫ y, |f y|) := by
  obtain ⟨C, hC, hconv⟩ := rieszHeat_convolution_bound d β hβ hβd hfm hfi hfB
  obtain ⟨D, _, hD⟩ := rieszHeat_bound d β hβ hβd
  refine ⟨C, hC, ?_⟩
  intro t ht c hcint hcov
  let k : Space d → ℝ := fun z => ‖z‖ ^ (-β) * heatKernel d t z
  have hkint : Integrable k := (hD t ht).1
  have hmajor := integrable_abs_mul_kernel d hfi hfB hkint
  have hpoint : ∀ᵐ p : Space d × Space d ∂(volume.prod volume),
      ((f p.1 * f p.2 * heatKernel d t (p.1 - p.2)) * c p) ≤
        K * (|f p.1| * |f p.2| * k (p.1 - p.2)) := by
    filter_upwards [hcov] with p hp
    have hheat := heatKernel_nonneg d ht (p.1 - p.2)
    by_cases hp1 : f p.1 = 0
    · simp [hp1]
    by_cases hp2 : f p.2 = 0
    · simp [hp2]
    have hp := hp hp1 hp2
    calc
      _ ≤ |(f p.1 * f p.2 * heatKernel d t (p.1 - p.2)) * c p| := le_abs_self _
      _ = |f p.1| * |f p.2| * heatKernel d t (p.1 - p.2) * |c p| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hheat]
      _ ≤ |f p.1| * |f p.2| * heatKernel d t (p.1 - p.2) *
          (K * ‖p.1 - p.2‖ ^ (-β)) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = K * (|f p.1| * |f p.2| * k (p.1 - p.2)) := by dsimp [k]; ring
  have hmono := integral_mono_ae hcint (hmajor.const_mul K) hpoint
  rw [integral_const_mul] at hmono
  have heq : (∫ p : Space d × Space d, |f p.1| * |f p.2| * k (p.1 - p.2)
      ∂(volume.prod volume)) = ∫ y, |f y| * (∫ x, |f x| * k (y - x)) := by
    rw [integral_prod _ hmajor]
    apply integral_congr_ae
    filter_upwards with y
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [heq] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left (hconv t ht) hK)

/-- A uniform Riesz covariance bound implies a uniform expected cutoff Fourier
energy, even if the diagonal second moments are not uniformly bounded. -/
theorem uniform_fourierNegEnergy_of_riesz_covariance {Ω ι : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] (d : ℕ) (β s K : ℝ)
    (hβ : 0 < β) (hβd : β < d) (hs : β / 2 < s) (hK : 0 ≤ K)
    (χ : Space d → ℝ) (hχ : IsTestFn Set.univ χ) (T : ι → Ω → Space d → ℝ)
    (hT : ∀ i, Measurable fun q : Ω × Space d => T i q.1 q.2)
    (hsq : ∀ i z, χ z ≠ 0 → Integrable (fun ω => T i ω z ^ 2) P)
    (hB : ∀ i, ∃ B : ℝ, ∀ z, χ z ≠ 0 → ∫ ω, T i ω z ^ 2 ∂P ≤ B)
    (hmean : ∀ i z, ∫ ω, T i ω z ∂P = 0)
    (hfield : ∀ i, ∀ᵐ ω ∂P, Integrable (fun z => χ z * T i ω z))
    (hcov : ∀ i, ∀ᵐ p : Space d × Space d ∂(volume.prod volume),
      χ p.1 ≠ 0 → χ p.2 ≠ 0 → |covariance (fun ω => T i ω p.1) (fun ω => T i ω p.2) P| ≤
        K * ‖p.1 - p.2‖ ^ (-β)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i,
      (∫⁻ ω, fourierNegEnergy d s (fun z => χ z * T i ω z) ∂P) ≤ ENNReal.ofReal M := by
  have hgm : StronglyMeasurable χ := hχ.1.continuous.stronglyMeasurable
  have hg : Integrable χ := hχ.integrable
  obtain ⟨B, hBχ⟩ := hχ.2.1.exists_bound_of_continuous hχ.1.continuous
  have hgB (x : Space d) : |χ x| ≤ B := by simpa only [Real.norm_eq_abs] using hBχ x
  have hB0 : 0 ≤ B := (abs_nonneg (χ 0)).trans (hgB 0)
  have hg0 : 0 ≤ ∫ y, |χ y| := integral_nonneg fun y => abs_nonneg _
  have hs0 : 0 < s := by linarith
  have hsa : 0 < s - β / 2 := by linarith
  obtain ⟨C, hC, hheat⟩ := heat_covariance_integral_bound_of_riesz d β hβ hβd hgm hg hgB hK
  let M : ℝ := K * (B * C * ∫ y, |χ y|)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hΓ : 0 ≤ M * Real.Gamma (s - β / 2) / Real.Gamma s := by
    positivity
  refine ⟨M * Real.Gamma (s - β / 2) / Real.Gamma s, hΓ, ?_⟩
  intro i
  obtain ⟨Bi, hBi⟩ := hB i
  have hheat' (t : ℝ) (ht : 0 < t) : (1 : ℝ) * (∫ ω,
      (∫ ξ : Space d, Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ‖ ^ 2)) *
        ‖𝓕 (fun z => ((χ z * T i ω z : ℝ) : ℂ)) ξ‖ ^ 2) ∂P) ≤ M * t ^ (-(β / 2)) := by
    let k : Space d × Space d → ℝ := fun p => heatKernel d t (p.1 - p.2)
    have hkm : Measurable k := ((continuous_heatKernel d t).comp
      (continuous_fst.sub continuous_snd)).measurable
    have hkbound (p : Space d × Space d) : ‖k p‖ ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg d ht _)]
      exact heatKernel_le d ht _
    have hi := integrable_pair_kernel_covariance (hT i) hgm.measurable hg
      (hsq i) hBi (hmean i) hkm hkbound
    have h := hheat t ht _ hi (hcov i)
    rw [integral_heatEnergy_eq_covariance d (hT i) hgm.measurable hg
      (hsq i) hBi (hmean i) (hfield i) ht]
    have heq : K * (B * (C * t ^ (-β / 2)) * ∫ y, |χ y|) = M * t ^ (-(β / 2)) := by
      have hexp : -β / 2 = -(β / 2) := by ring
      rw [hexp]
      dsimp [M]
      ring
    simpa only [one_mul, heq] using h
  have hspec := lintegral_fourier_energy_le_of_heat d (hT i) hgm.measurable hg
    (B := Bi) (A := 1) (M := M) (s := s) (a := β / 2)
    (by norm_num) hM hs0 hsa (hsq i) hBi (hfield i) hheat'
  have hweight (ξ : Space d) : 1 + (2 * Real.pi * ‖ξ‖) ^ 2 =
      1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by ring
  simp_rw [fourierNegEnergy, hweight]
  simpa only [one_mul] using hspec

end Sandpile.Support
