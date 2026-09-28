import Sandpile.Support.Dgt4ABandLaw
import Sandpile.Support.Dgt4ABandWeights
import LatticeProb.Prob.Karamata

/-!
# The Integrated Band Profile

The integrated band profile `eq:dgt4-band-integrated-profile` of Step 2 of
`thm:dgt4-many-limits` (`sandpile.tex:6145-6161`).

Integrating the band profile `eq:dgt4-band-profile` over the band and adding the
upper isolation `eq:dgt4-band-upper-isolation` turns the tail profile
`P(-ζ(0) > a_k - (1-ℓ_1)a_k r) = ω_k r^{ϑ_k}(1+o(1))` into the overshoot profile
`E(-ζ(0) - a_k + (1-ℓ_1)a_k z)_+ = ω_k(1-ℓ_1)a_k z^{ϑ_k+1}/(ϑ_k+1)(1+o(1))`.

The estimate proved here is the additive one, uniform over the whole range
`0 ≤ z ≤ 1`. The paper's ratio form follows from it wherever `z^{ϑ_k+1}` is
bounded below, which is what the index range `eq:dgt4-band-index-range` and the
choice of `L_k` secure; the additive form does not mention `L_k`, which the
paper chooses only afterwards.

The layer-cake identity `E(-ζ(0) - t)_+ = ∫_t^∞ P(-ζ(0) > r) dr` and the
integrability that goes with it come from the shared probability library
(`LatticeProb.integral_posPart_eq`).
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal Interval

noncomputable section

namespace Sandpile.Support

open LatticeProb

/-- The set the band profile is stated on is the lower tail of the law. -/
theorem setOf_neg_gt_eq_Iio (c : ℝ) : {z : ℝ | -(z) > c} = Iio (-c) := by
  ext z
  simp only [mem_setOf_eq, mem_Iio, gt_iff_lt]
  constructor <;> intro h <;> linarith

/-- The band profile reads the lower tail of the law. -/
theorem lowerTail_eq_toReal (ν : Measure ℝ) (c : ℝ) :
    lowerTail ν c = (ν {z : ℝ | -(z) > c}).toReal := by
  rw [lowerTail, setOf_neg_gt_eq_Iio]

/-- The lower tail is integrable past `t` as soon as the mean overshoot above
`t` is finite; this is the converse of `LatticeProb.integrable_posPart`. -/
theorem integrableOn_lowerTail_of_integrable {ν : Measure ℝ} [IsFiniteMeasure ν] {t : ℝ}
    (h : Integrable (fun z : ℝ => max (-z - t) 0) ν) :
    IntegrableOn (lowerTail ν) (Ioi t) := by
  have hmeas : Measurable (lowerTail ν) := (antitone_lowerTail ν).measurable
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi t)] lowerTail ν :=
    Filter.Eventually.of_forall fun r => lowerTail_nonneg ν r
  refine ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).mpr ?_⟩
  rw [← lintegral_posPart_eq ν t]
  have hnn' : 0 ≤ᵐ[ν] fun z : ℝ => max (-z - t) 0 :=
    Filter.Eventually.of_forall fun z => le_max_right _ _
  exact (hasFiniteIntegral_iff_ofReal hnn').mp h.2

/-- **The integrated profile at one band.**  If the tail profile holds on the
`k`th band up to `η`, then the mean overshoot above the level `a - Wz`, divided
by `ωW`, is `z^{θ+1}/(θ+1)` up to `η` plus the relative mean overshoot above the
top of the band. -/
theorem abs_integrated_profile_le (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hint : ∀ t : ℝ, IntegrableOn (lowerTail ν) (Ioi t))
    {a W ω θ η : ℝ} (hW : 0 < W) (hω : 0 < ω) (hθ : 0 ≤ θ)
    (hprof : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → |lowerTail ν (a - W * r) / ω - r ^ θ| ≤ η)
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    |(∫ x, max (-x - (a - W * z)) 0 ∂ν) / (ω * W) - z ^ (θ + 1) / (θ + 1)|
      ≤ η + (∫ x, max (-x - a) 0 ∂ν) / (ω * W) := by
  have hz0 : 0 ≤ z := hz.1
  have hz1 : z ≤ 1 := hz.2
  have hθ1 : (0 : ℝ) < θ + 1 := by linarith
  set c : ℝ := a - W * z with hc
  have hca : c ≤ a := by
    have : 0 ≤ W * z := mul_nonneg hW.le hz0
    simp only [hc]; linarith
  -- the layer-cake representation of the two overshoots
  have hI : ∫ x, max (-x - c) 0 ∂ν = ∫ r in Ioi c, lowerTail ν r :=
    integral_posPart_eq (hint c)
  have hIa : ∫ x, max (-x - a) 0 ∂ν = ∫ r in Ioi a, lowerTail ν r :=
    integral_posPart_eq (hint a)
  -- split the tail integral at the top of the band
  have hsplit : ∫ r in Ioi c, lowerTail ν r
      = (∫ r in Ioc c a, lowerTail ν r) + ∫ r in Ioi a, lowerTail ν r := by
    have hdisj : Disjoint (Ioc c a) (Ioi a) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_le.mpr hx')
    have hunion : Ioc c a ∪ Ioi a = Ioi c := Ioc_union_Ioi_eq_Ioi hca
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioi
      ((hint c).mono_set Ioc_subset_Ioi_self) (hint a)]
  -- rescale the band to `[0,z]`
  have hband : ∫ r in Ioc c a, lowerTail ν r
      = W * ∫ s in (0 : ℝ)..z, lowerTail ν (a - W * s) := by
    have hsub := intervalIntegral.integral_comp_sub_mul (a := (0 : ℝ)) (b := z)
      (lowerTail ν) (ne_of_gt hW) a
    rw [mul_zero, sub_zero, smul_eq_mul, ← hc] at hsub
    rw [← intervalIntegral.integral_of_le hca, hsub, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hW), one_mul]
  -- the profile controls the rescaled integrand
  have hmono : Monotone fun s : ℝ => lowerTail ν (a - W * s) := by
    intro s₁ s₂ hs
    refine (antitone_lowerTail ν) ?_
    have := mul_le_mul_of_nonneg_left hs hW.le
    linarith
  have hii1 : IntervalIntegrable (fun s : ℝ => lowerTail ν (a - W * s)) volume 0 z :=
    hmono.intervalIntegrable
  have hii2 : IntervalIntegrable (fun s : ℝ => ω * s ^ θ) volume 0 z :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < θ)).const_mul ω
  have hrpow : ∫ s in (0 : ℝ)..z, s ^ θ = z ^ (θ + 1) / (θ + 1) := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < θ)), Real.zero_rpow (ne_of_gt hθ1)]
    ring
  have hdiff : (∫ s in (0 : ℝ)..z, lowerTail ν (a - W * s)) - ω * (z ^ (θ + 1) / (θ + 1))
      = ∫ s in (0 : ℝ)..z, (lowerTail ν (a - W * s) - ω * s ^ θ) := by
    rw [intervalIntegral.integral_sub hii1 hii2, intervalIntegral.integral_const_mul, hrpow]
  have hbound : |(∫ s in (0 : ℝ)..z, lowerTail ν (a - W * s)) - ω * (z ^ (θ + 1) / (θ + 1))|
      ≤ η * ω * z := by
    rw [hdiff]
    have hptw : ∀ s ∈ Ι (0 : ℝ) z, ‖lowerTail ν (a - W * s) - ω * s ^ θ‖ ≤ η * ω := by
      intro s hs
      rw [Set.uIoc_of_le hz0] at hs
      have hs0 : (0 : ℝ) ≤ s := hs.1.le
      have hs1 : s ≤ 1 := le_trans hs.2 hz1
      have hp := hprof s ⟨hs0, hs1⟩
      have hkey : |lowerTail ν (a - W * s) - ω * s ^ θ| ≤ η * ω := by
        have hrw : lowerTail ν (a - W * s) - ω * s ^ θ
            = ω * (lowerTail ν (a - W * s) / ω - s ^ θ) := by
          field_simp
        rw [hrw, abs_mul, abs_of_pos hω, mul_comm (η : ℝ) ω]
        exact mul_le_mul_of_nonneg_left hp hω.le
      rwa [Real.norm_eq_abs]
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hptw
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hz0] at hle
    exact hle
  -- assemble
  have hIeq : ∫ x, max (-x - c) 0 ∂ν
      = W * (∫ s in (0 : ℝ)..z, lowerTail ν (a - W * s)) + ∫ x, max (-x - a) 0 ∂ν := by
    rw [hI, hsplit, hband, hIa]
  rw [hIeq]
  set G : ℝ := ∫ s in (0 : ℝ)..z, lowerTail ν (a - W * s) with hG
  set Ia : ℝ := ∫ x, max (-x - a) 0 ∂ν with hIadef
  have hIann : 0 ≤ Ia := by
    rw [hIadef]
    exact integral_nonneg fun x => le_max_right _ _
  have hform : (W * G + Ia) / (ω * W) - z ^ (θ + 1) / (θ + 1)
      = (G - ω * (z ^ (θ + 1) / (θ + 1))) / ω + Ia / (ω * W) := by
    field_simp
    ring
  rw [hform]
  have h1 : |(G - ω * (z ^ (θ + 1) / (θ + 1))) / ω| ≤ η := by
    rw [abs_div, abs_of_pos hω, div_le_iff₀ hω]
    refine hbound.trans ?_
    calc η * ω * z ≤ η * ω * 1 := by
          have hηnn : 0 ≤ η := le_trans (abs_nonneg _) (hprof 0 ⟨le_rfl, zero_le_one⟩)
          have : 0 ≤ η * ω := mul_nonneg hηnn hω.le
          nlinarith
      _ = η * ω := by ring
  have h2 : |Ia / (ω * W)| = Ia / (ω * W) :=
    abs_of_nonneg (div_nonneg hIann (mul_pos hω hW).le)
  calc |(G - ω * (z ^ (θ + 1) / (θ + 1))) / ω + Ia / (ω * W)|
      ≤ |(G - ω * (z ^ (θ + 1) / (θ + 1))) / ω| + |Ia / (ω * W)| := abs_add_le _ _
    _ ≤ η + Ia / (ω * W) := by rw [h2]; linarith

/-- `eq:dgt4-band-integrated-profile` (`sandpile.tex:6140-6156`), in additive
form: uniformly over `0 ≤ z ≤ 1`, the mean overshoot of `-ζ(0)` above the level
`a_k - (1-ℓ_1)a_k z`, divided by `ω_k(1-ℓ_1)a_k`, is `z^{ϑ_k+1}/(ϑ_k+1)`. -/
def BandIntegratedProfile (P : BandParameters) (ν : Measure ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ z : ℝ, z ∈ Icc (0 : ℝ) 1 →
    |(∫ x, max (-x - (P.level k - (1 - P.l1) * P.level k * z)) 0 ∂ν) /
        (P.weight k * (1 - P.l1) * P.level k)
      - z ^ (P.theta k + 1) / (P.theta k + 1)| ≤ η

/-- **The integrated band profile from the tail profile and the upper
isolation** (`sandpile.tex:6140-6156`). -/
theorem bandIntegratedProfile_of_profile (P : BandParameters) (ν : Measure ℝ)
    [IsFiniteMeasure ν] (hint : ∀ t : ℝ, IntegrableOn (lowerTail ν) (Ioi t))
    (hprof : BandProfile P ν) (hupper : BandUpperIsolation P ν) :
    BandIntegratedProfile P ν := by
  intro η hη
  have hhalf : (0 : ℝ) < η / 2 := by linarith
  have h2 : ∀ᶠ k : ℕ in atTop,
      (∫ x, max (-x - P.level k) 0 ∂ν) / (P.weight k * (1 - P.l1) * P.level k) < η / 2 :=
    hupper.2.eventually_lt_const hhalf
  filter_upwards [hprof (η / 2) hhalf, h2] with k hk1 hk2 z hz
  have hl1 : P.l1 < 1 := P.hl1.2
  have hak : 0 < P.level k := P.level_pos k
  have hW : 0 < (1 - P.l1) * P.level k := mul_pos (by linarith) hak
  have hω : 0 < P.weight k := P.weight_pos k
  have hθ : 0 ≤ P.theta k := le_trans zero_le_one (P.htheta k).1
  have hprofk : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
      |lowerTail ν (P.level k - (1 - P.l1) * P.level k * r) / P.weight k
        - r ^ P.theta k| ≤ η / 2 := by
    intro r hr
    rw [lowerTail_eq_toReal]
    exact hk1 r hr
  have hcore := abs_integrated_profile_le ν hint (a := P.level k)
    (W := (1 - P.l1) * P.level k) (ω := P.weight k) (θ := P.theta k) (η := η / 2)
    hW hω hθ hprofk hz
  have hassoc : P.weight k * (1 - P.l1) * P.level k
      = P.weight k * ((1 - P.l1) * P.level k) := by ring
  rw [hassoc]
  rw [hassoc] at hk2
  linarith

end Sandpile.Support
