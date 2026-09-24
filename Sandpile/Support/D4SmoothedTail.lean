/-
Step 2 of `prop:d4-pointwise-linearization` (`sandpile.tex:3100-3125`): the tail
of the smoothed difference,

    P(|P^n(u_{t-n} - E u_{t-n}(0) - V_{t-n})(x)| > u)
      ≤ C exp{-c min(u²/(1 + log((t+2)/(n+2))), u n)} ,

uniformly in `x`.  The coordinate Lipschitz coefficient of the smoothed
difference is twice the window `∑_{k=n}^{t-1} p_k(x,z)`
(`Sandpile.abs_diffSmoothed_update_le`), whose two norms are
`eq:d4-window-l2` and `eq:d4-window-linfty`, and the mean of the smoothed
difference is `E u_{t-n}(0)` (`Sandpile.integral_diffSmoothed`).
`lem:weighted-exp-conc` clause (b) then gives the bound.
-/
import Sandpile.Support.D4Smoothed
import Sandpile.Support.D4Difference
import Sandpile.External.VarianceScale
import Sandpile.Frozen.WeightedExpConcentration

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

/-- **The tail of the smoothed difference in dimension four.** -/
theorem exists_smoothed_difference_tail_four (hVS : Sandpile.External.VarianceScale)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ w, w ∂ν = 0 →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ n t : ℕ, 1 ≤ n → n < t → ∀ (x : Site 4) (u : ℝ), 0 ≤ u →
          LatticeProb.iidLaw 4 ν
              {ζ : Site 4 → ℝ | u < |(avg^[n] (diffField ζ (t - n))) x -
                ∫ η, odometerOf η (t - n) 0 ∂(LatticeProb.iidLaw 4 ν)|} ≤
            ENNReal.ofReal (C * Real.exp (-(c * min (u ^ 2 /
              (1 + Real.log (((t : ℝ) + 2) / ((n : ℝ) + 2)))) (u * (n : ℝ))))) := by
  classical
  obtain ⟨Cw, hCw, hwin, -⟩ := hVS.2.2
  obtain ⟨c₀, C₀, hc₀, hC₀, hconc⟩ := Sandpile.Frozen.weighted_exp_concentration.2.1 θ₀ K₀ hθ₀
  refine ⟨c₀ / (4 * Cw), C₀, div_pos hc₀ (by linarith), hC₀, ?_⟩
  intro ν hprob hmean hexpint hexp n t hn hnt x u hu
  haveI := hprob
  have hint : Integrable id ν := LatticeProb.integrable_id_of_exp_moment ν θ₀ hθ₀ hexpint
  have hpos : Integrable (fun z : ℝ => max z 0) ν := by
    refine Integrable.mono' (hexpint.const_mul (1 / θ₀))
      (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have hle := LatticeProb.le_exp_self (θ₀ * |z|)
    have habs : |z| ≤ Real.exp (θ₀ * |z|) / θ₀ := by
      rw [le_div_iff₀ hθ₀]; nlinarith [hle]
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
    have h1 : max z 0 ≤ |z| := max_le (le_abs_self z) (abs_nonneg z)
    have h2 : Real.exp (θ₀ * |z|) / θ₀ = 1 / θ₀ * Real.exp (θ₀ * |z|) := by ring
    linarith [habs, h1, h2.le, h2.ge]
  -- the two window bounds at the pair `(n, t)`
  obtain ⟨hwl2, hwinf⟩ := hwin n t hn hnt x
  set m := t - n with hm
  have hm1 : 1 ≤ m := by omega
  set s : Finset (Site 4) := boxFinset x (n + m) with hs
  set N := s.card with hN
  set ℓ : Fin N → ℝ := fun i => 2 * smoothedCoeff 4 n m x (siteEnum s i) with hℓ
  have hℓnn : ∀ i, 0 ≤ ℓ i := fun i => by
    have := smoothedCoeff_nonneg (d := 4) n m x (siteEnum s i); simp [hℓ]; linarith
  obtain ⟨i₀, hi₀⟩ := exists_smoothedCoeff_ne_zero' (d := 4) (by norm_num) n m hm1 x
  have hi₀pos : 0 < smoothedCoeff 4 n m x (siteEnum s i₀) :=
    lt_of_le_of_ne (smoothedCoeff_nonneg n m x _) (Ne.symm hi₀)
  have hne : ∃ i, ℓ i ≠ 0 := ⟨i₀, by simp [hℓ]; linarith⟩
  haveI : Nonempty (Fin N) := ⟨i₀⟩
  set L : ℝ := 1 + Real.log (((t : ℝ) + 2) / ((n : ℝ) + 2)) with hL
  have hLpos : 0 < L := by
    have h1 : (1 : ℝ) ≤ ((t : ℝ) + 2) / ((n : ℝ) + 2) := by
      rw [le_div_iff₀ (by positivity)]
      have : (n : ℝ) ≤ (t : ℝ) := by exact_mod_cast hnt.le
      linarith
    have := Real.log_nonneg h1
    linarith
  -- the ℓ² norm
  have hTwo : lTwoNorm ℓ ^ 2 = ∑ i, ℓ i ^ 2 := lTwoNorm_sq ℓ
  have hTwoLe : lTwoNorm ℓ ^ 2 ≤ 4 * Cw * L := by
    rw [hTwo]
    have hexpand : ∀ i : Fin N, ℓ i ^ 2 = 4 * smoothedCoeff 4 n m x (siteEnum s i) ^ 2 :=
      fun i => by simp [hℓ]; ring
    rw [Finset.sum_congr rfl fun i _ => hexpand i, ← Finset.mul_sum,
      sum_siteEnum s fun z => smoothedCoeff 4 n m x z ^ 2,
      ← tsum_smoothedCoeff_sq_eq_sum n m x]
    have heq : ∀ z : Site 4, smoothedCoeff 4 n m x z ^ 2
        = Sandpile.External.Variance.windowKernel n t x z ^ 2 := fun z => by
      rw [hm, smoothedCoeff_eq_windowKernel n t x z]
    rw [tsum_congr heq]
    nlinarith [hwl2]
  have hTwoPos : 0 < lTwoNorm ℓ ^ 2 := by
    rw [hTwo]
    refine lt_of_lt_of_le (pow_pos (show (0:ℝ) < ℓ i₀ by simp [hℓ]; linarith) 2) ?_
    exact Finset.single_le_sum (f := fun i : Fin N => ℓ i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
  -- the ℓ^∞ norm
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hInfLe : lInfNorm ℓ ≤ 2 * Cw / (n : ℝ) := by
    refine ciSup_le fun i => ?_
    have h := hwinf (siteEnum s i)
    rw [hℓ]
    simp only
    rw [hm, smoothedCoeff_eq_windowKernel n t x (siteEnum s i)]
    rw [show 2 * Cw / (n : ℝ) = 2 * (Cw / (n : ℝ)) by ring]
    linarith
  have hInfPos : 0 < lInfNorm ℓ :=
    lt_of_lt_of_le (show (0:ℝ) < ℓ i₀ by simp [hℓ]; linarith) (le_lInfNorm ℓ i₀)
  -- the concentration bound in the box coordinates
  have hkey := hconc N ν hprob hexpint hexp (diffSmoothed s n m x)
    (measurable_diffSmoothed s n m x) ℓ hℓnn hne
    (fun ξ i y => abs_diffSmoothed_update_le s n m x ξ i y) u hu
  have hmean' : (∫ ξ, diffSmoothed s n m x ξ ∂(Measure.pi fun _ : Fin N => ν))
      = ∫ η, odometerOf η m 0 ∂(LatticeProb.iidLaw 4 ν) :=
    integral_diffSmoothed (by norm_num) ν hint hmean hpos n m x
  rw [hmean'] at hkey
  have hmp := LatticeProb.measurePreserving_pick _ ν (siteEnum s) (siteEnum_injective s)
  have hmeasset : MeasurableSet {ξ : Fin N → ℝ | u ≤ |diffSmoothed s n m x ξ -
      ∫ η, odometerOf η m 0 ∂(LatticeProb.iidLaw 4 ν)|} :=
    measurableSet_le measurable_const
      (((measurable_diffSmoothed s n m x).sub measurable_const).abs)
  have hsubset : {ζ : Site 4 → ℝ | u < |(avg^[n] (diffField ζ m)) x -
        ∫ η, odometerOf η m 0 ∂(LatticeProb.iidLaw 4 ν)|}
      ⊆ (fun ζ : Site 4 → ℝ => fun i => ζ (siteEnum s i)) ⁻¹'
        {ξ | u ≤ |diffSmoothed s n m x ξ -
          ∫ η, odometerOf η m 0 ∂(LatticeProb.iidLaw 4 ν)|} := by
    intro ζ hζ
    simp only [Set.mem_setOf_eq] at hζ
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [diffSmoothed_pick (subset_refl s) ζ]
    exact hζ.le
  have hmin : (c₀ / (4 * Cw)) * min (u ^ 2 / L) (u * (n : ℝ))
      ≤ c₀ * min (u ^ 2 / lTwoNorm ℓ ^ 2) (u / lInfNorm ℓ) := by
    rw [mul_min_of_nonneg _ _ (div_pos hc₀ (by linarith)).le,
      mul_min_of_nonneg _ _ hc₀.le]
    refine min_le_min ?_ ?_
    · rw [show (c₀ / (4 * Cw)) * (u ^ 2 / L) = c₀ * (u ^ 2 / (4 * Cw * L)) by
        field_simp]
      refine mul_le_mul_of_nonneg_left ?_ hc₀.le
      exact div_le_div_of_nonneg_left (sq_nonneg u) hTwoPos hTwoLe
    · rw [show (c₀ / (4 * Cw)) * (u * (n : ℝ)) = c₀ * (u / (4 * Cw / (n : ℝ))) by
        field_simp]
      refine mul_le_mul_of_nonneg_left ?_ hc₀.le
      refine div_le_div_of_nonneg_left hu hInfPos (le_trans hInfLe ?_)
      rw [div_le_div_iff_of_pos_right hn0]
      linarith
  calc LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | u < |(avg^[n] (diffField ζ m)) x -
        ∫ η, odometerOf η m 0 ∂(LatticeProb.iidLaw 4 ν)|}
      ≤ LatticeProb.iidLaw 4 ν ((fun ζ : Site 4 → ℝ => fun i => ζ (siteEnum s i)) ⁻¹'
          {ξ | u ≤ |diffSmoothed s n m x ξ -
            ∫ η, odometerOf η m 0 ∂(LatticeProb.iidLaw 4 ν)|}) := measure_mono hsubset
    _ = (Measure.pi fun _ : Fin N => ν)
          {ξ | u ≤ |diffSmoothed s n m x ξ -
            ∫ η, odometerOf η m 0 ∂(LatticeProb.iidLaw 4 ν)|} :=
        hmp.measure_preimage hmeasset.nullMeasurableSet
    _ ≤ ENNReal.ofReal (C₀ * Real.exp (-(c₀ *
          min (u ^ 2 / lTwoNorm ℓ ^ 2) (u / lInfNorm ℓ)))) := hkey
    _ ≤ ENNReal.ofReal (C₀ * Real.exp (-(c₀ / (4 * Cw) *
          min (u ^ 2 / L) (u * (n : ℝ))))) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC₀.le)
        exact Real.exp_le_exp.mpr (by linarith)

end Sandpile
