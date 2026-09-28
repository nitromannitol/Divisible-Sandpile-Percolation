import Sandpile.Support.ExplBallBound
import Sandpile.Support.ExplBallMoment

/-!
# Uniform boundedness of the far values, from a uniform path-radius moment

The boundedness of the far values of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`)
with no separate moment hypothesis.

The polynomial moment of the compact-time Brownian maximum is uniform over the starting point
and the motion (`exists_uniform_pathRadius_moment`), so the boundedness of the far values
follows from the samplewise polynomial growth of the field alone.
`bddAbove_farValues_of_growth_uniform` draws this conclusion at a single sample point directly,
`bddAbove_farValues_of_growth_pointwise` supplies the underlying quantitative bound, and
`bddAbove_farValues_of_samplewise_growth_uniform` upgrades to an almost-sure statement when the
growth amplitude and degree are only chosen after the sample.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum
open Sandpile.Support

variable {ΩW : Type*} [MeasurableSpace ΩW] {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- The far values are bounded above at a sample point where the field is continuous on the
strip and grows polynomially, with NO separate moment hypothesis: the uniform moment bound of
`exists_uniform_pathRadius_moment` supplies it. -/
theorem bddAbove_farValues_of_growth_uniform {PW : Measure ΩW} [IsProbabilityMeasure PW]
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBrown : ∀ y : Space d, IsBrownian d y (B y) PB)
    (hcont : ∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hmeas : ∀ (y : Space d) (t : ℝ≥0), Measurable (B y t))
    (Z : ℝ → Space d → ΩW → ℝ) (T A : ℝ) (hT : 0 ≤ T) (K : Set (Space d)) (hK : IsCompact K)
    (p : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ᵐ ω ∂PW, ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d,
      ‖Z v y ω‖ ≤ C * (1 + ‖y‖) ^ p)
    (hcontZ : ∀ᵐ ω ∂PW,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) :
    ∀ᵐ ω ∂PW, BddAbove (farValues B PB (fun t z => Z t z ω) T A K) := by
  obtain ⟨M, hM⟩ := exists_uniform_pathRadius_moment d T.toNNReal p
  exact bddAbove_farValues_of_growth hBrown hcont hmeas Z T A hT K hK p C hC hgrowth hcontZ M
    (fun z => hM ΩB PB inferInstance z (B z) (hBrown z) (hmeas z) (hcont z))

/-- The far values are bounded above at ONE sample point where the field is continuous on the
strip and grows polynomially with a fixed amplitude and degree. -/
theorem bddAbove_farValues_of_growth_pointwise {PW : Measure ΩW} [IsProbabilityMeasure PW]
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBrown : ∀ y : Space d, IsBrownian d y (B y) PB)
    (hcont : ∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hmeas : ∀ (y : Space d) (t : ℝ≥0), Measurable (B y t))
    (Z : ℝ → Space d → ΩW → ℝ) (T A : ℝ) (hT : 0 ≤ T) (K : Set (Space d)) (hK : IsCompact K)
    (p : ℕ) (C : ℝ) (hC : 0 ≤ C) (ω : ΩW)
    (hgrowth : ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d,
      ‖Z v y ω‖ ≤ C * (1 + ‖y‖) ^ p)
    (hcontZ : ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) :
    BddAbove (farValues B PB (fun t z => Z t z ω) T A K) := by
  obtain ⟨M, hM⟩ := exists_uniform_pathRadius_moment d T.toNNReal p
  have hMmom : ∀ z : Space d,
      ∫ ω, (1 + brownianPathRadius (B z) z T.toNNReal ω) ^ p ∂PB ≤ M :=
    fun z => hM ΩB PB inferInstance z (B z) (hBrown z) (hmeas z) (hcont z)
  obtain ⟨M', hM'⟩ := exists_bound_on_neighbourhood (fun t z => Z t z ω) T A hT K hK hcontZ
  obtain ⟨R, hR⟩ := exists_bound_on_neighbourhood (fun _ z => (1 + ‖z‖) ^ p) T A hT K hK
    (Continuous.continuousOn (by fun_prop))
  refine ⟨2 * C * M * R + C * R, ?_⟩
  rintro v ⟨z, hz, rfl⟩
  have hRz : (1 + ‖z‖) ^ p ≤ R := hR z hz
  have hpoly : ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d,
      ‖Z v y ω‖ ≤ C * (1 + ‖z‖) ^ p * (1 + ‖y - z‖) ^ p := by
    intro v hv y
    refine le_trans (hgrowth v hv y) ?_
    have h1 : (1 + ‖y‖) ≤ (1 + ‖z‖) * (1 + ‖y - z‖) := by
      have h2 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
        simpa only [sub_add_cancel] using norm_le_norm_sub_add y z
      nlinarith [norm_nonneg (y - z), norm_nonneg z]
    calc C * (1 + ‖y‖) ^ p ≤ C * ((1 + ‖z‖) * (1 + ‖y - z‖)) ^ p :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 p) hC
      _ = C * (1 + ‖z‖) ^ p * (1 + ‖y - z‖) ^ p := by rw [mul_pow]; ring
  have hb := brownianValue_le_of_pointwise_bound (hBrown z) (hmeas z) (hcont z)
    (fun t z => Z t z ω) T hT hcontZ (C * (1 + ‖z‖) ^ p) M (by positivity) p hpoly (hMmom z)
  have hb' : Z T z ω + sSup (stoppingPayoffs (B z) PB (fun t z => Z t z ω) T) ≤
      2 * (C * (1 + ‖z‖) ^ p) * M := by
    simpa only [Sandpile.Continuum.brownianValue, Sandpile.Continuum.brownianDiscount_eq_sSup]
      using hb
  have hz'' : -(C * (1 + ‖z‖) ^ p) ≤ Z T z ω := by
    have h1 := hpoly T.toNNReal (by rw [Real.coe_toNNReal T hT]) z
    rw [Real.coe_toNNReal T hT, sub_self, norm_zero, add_zero, one_pow, mul_one] at h1
    exact neg_le_of_abs_le h1
  have hCnn : 0 ≤ C * (1 + ‖z‖) ^ p :=
    mul_nonneg hC (pow_nonneg (add_nonneg zero_le_one (norm_nonneg z)) p)
  have hRnn : 0 ≤ R := le_trans (pow_nonneg (add_nonneg zero_le_one (norm_nonneg z)) p) hRz
  have hMnn : 0 ≤ M := by
    have h1 : (0 : ℝ) ≤ ∫ ω, (1 + brownianPathRadius (B z) z T.toNNReal ω) ^ p ∂PB :=
      integral_nonneg fun ω => pow_nonneg (add_nonneg zero_le_one
        (le_trans (norm_nonneg _) (norm_le_pathRadius (B z) (hcont z) z T.toNNReal ω le_rfl))) p
    linarith [hMmom z]
  have hstep : sSup (stoppingPayoffs (B z) PB (fun t z => Z t z ω) T) ≤
      C * (1 + ‖z‖) ^ p * (2 * M + 1) := by nlinarith [hb', hz'']
  have hfin : C * (1 + ‖z‖) ^ p * (2 * M + 1) ≤ C * R * (2 * M + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRz hC) (by linarith)
  linarith [hstep, hfin]

/-- The far values are bounded above at almost every sample point where the field is continuous
on the strip and grows polynomially with an amplitude chosen after the sample. -/
theorem bddAbove_farValues_of_samplewise_growth_uniform {PW : Measure ΩW}
    [IsProbabilityMeasure PW] {PB : Measure ΩB} [IsProbabilityMeasure PB]
    {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBrown : ∀ y : Space d, IsBrownian d y (B y) PB)
    (hcont : ∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hmeas : ∀ (y : Space d) (t : ℝ≥0), Measurable (B y t))
    (Z : ℝ → Space d → ΩW → ℝ) (T A : ℝ) (hT : 0 ≤ T) (K : Set (Space d)) (hK : IsCompact K)
    (hgrowth : ∀ᵐ ω ∂PW, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
      ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d, ‖Z v y ω‖ ≤ C * (1 + ‖y‖) ^ p)
    (hcontZ : ∀ᵐ ω ∂PW,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) :
    ∀ᵐ ω ∂PW, BddAbove (farValues B PB (fun t z => Z t z ω) T A K) := by
  filter_upwards [hgrowth, hcontZ] with ω hg hc
  obtain ⟨C, hC, p, hp⟩ := hg
  exact bddAbove_farValues_of_growth_pointwise (PW := PW) (PB := PB) hBrown hcont hmeas Z T A hT
    K hK p C hC ω hp hc

end Sandpile.Continuum
