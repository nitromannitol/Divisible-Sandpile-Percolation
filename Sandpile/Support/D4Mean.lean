import Sandpile.Support.D4SmoothedTail
import Sandpile.Support.CrudeIncrement
import LatticeProb.Prob.Coordinate

/-!
# The logarithmic upper bound on the mean odometer in dimension four

This file proves `E u_t(0) ≤ C log(t+2)`, Step 1 of `thm:critical-toppling-d4`
(`sandpile.tex:2760-2825`). The smoothed centred odometer `P(u_t - E u_t(0))(0)` is a
Lipschitz function of the scenery with coefficients at most `g_{t+1}(0,·)`, whose square sum
is at most `C log(t+3)` and whose supremum is at most `C`; the weighted exponential
concentration lemma gives its lower tail on those two scales, and the split of
`sandpile.tex:2770-2776` carries that to the lower tail of `ζ(0) + P u_t(0)`. Integrating the
tail bounds the mean increment by `C ℓ exp{-c min(m_t²/ℓ, m_t)}` with `ℓ = log(t+3)`, and the
stopping argument of `sandpile.tex:2798-2825` turns that into the logarithmic bound.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- The window coefficient is below the Green kernel of the whole window. -/
theorem smoothedCoeff_le_greenTime (m n : ℕ) (x y : Site d) :
    smoothedCoeff d m n x y ≤ greenTime d (m + n) x y := by
  have hIco : ∑ j ∈ Finset.range n, heatKernel d (m + j) x y
      = ∑ k ∈ Finset.Ico m (m + n), heatKernel d k x y := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  rw [smoothedCoeff, greenTime, hIco]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => heatKernel_nonneg k x y
  intro k hk
  exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2

/-- **The lower tail of the smoothed centred odometer in dimension four.**  The
coefficients `∑_{j<t} p_{1+j}(0,y)` are at most `g_{t+1}(0,y)`, whose square sum
is at most `M log(t+3)` and whose supremum is at most `M`. -/
theorem exists_smoothed_odometer_tail_four_uniform (hVS : Sandpile.External.VarianceScale)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        (∫ z, Real.exp (θ₀ * |z|) ∂ν) ≤ K₀ →
        Integrable (fun z : ℝ => max z 0) ν →
        ∀ (t : ℕ) (s : ℝ), 0 ≤ s →
      LatticeProb.iidLaw 4 ν
          {ζ : Site 4 → ℝ | (avg^[1] fun x => odometerOf ζ t x -
            ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) 0 ≤ -s} ≤
        ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2 / Real.log ((t : ℝ) + 3)) s))) := by
  classical
  obtain ⟨M, hM, hM2, hMinf⟩ := exists_greenTime_norm_bounds_four hVS
  obtain ⟨c₀, C₀, hc₀, hC₀, hconc⟩ := Sandpile.Frozen.weighted_exp_concentration.2.1 θ₀ K₀ hθ₀
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  refine ⟨c₀ / M, max C₀ 1, div_pos hc₀ hM0, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro ν hprob hexpint hexp hpos t s hs
  haveI := hprob
  set P : Measure (Site 4 → ℝ) := LatticeProb.iidLaw 4 ν with hP
  set mean : ℝ := ∫ η, odometerOf η t 0 ∂P with hmeandef
  set L : ℝ := Real.log ((t : ℝ) + 3) with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    refine le_trans one_le_log_three (Real.log_le_log (by norm_num) ?_)
    have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  rcases hs.eq_or_lt with hs0 | hspos
  · subst hs0
    refine le_trans prob_le_one ?_
    have h1 : ((0:ℝ) ^ 2 / L) = 0 := by simp
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (max C₀ 1 * Real.exp (-(c₀ / M * min ((0:ℝ) ^ 2 / L) 0))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [h1]
          simp
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hI : (∫ η, odometerOf η 0 0 ∂P) = 0 := by simp [odometerOf]
    have hempty : {ζ : Site 4 → ℝ | (avg^[1] fun x => odometerOf ζ 0 x -
        ∫ η, odometerOf η 0 0 ∂P) 0 ≤ -s} = ∅ := by
      ext ζ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      rw [avg_iterate_sub_const (by norm_num) 1 (odometerOf ζ 0) _ 0, hI, sub_zero]
      have hfun : odometerOf ζ 0 = fun _ : Site 4 => (0 : ℝ) := rfl
      rw [hfun, avg_iterate_zero]
      linarith
    rw [hempty]
    simp
  · set s0 : Finset (Site 4) := boxFinset (0 : Site 4) (1 + t) with hs0def
    set N := s0.card with hN
    set ℓ : Fin N → ℝ := fun i => smoothedCoeff 4 1 t 0 (siteEnum s0 i) with hℓ
    have hℓnn : ∀ i, 0 ≤ ℓ i := fun i => smoothedCoeff_nonneg _ _ _ _
    obtain ⟨i₀, hi₀⟩ := exists_smoothedCoeff_ne_zero (d := 4) (by norm_num) 1 t ht
    have hne : ∃ i, ℓ i ≠ 0 := ⟨i₀, hi₀⟩
    haveI : Nonempty (Fin N) := ⟨i₀⟩
    have hi₀pos : 0 < ℓ i₀ := lt_of_le_of_ne (hℓnn i₀) (Ne.symm hi₀)
    have hTwo : lTwoNorm ℓ ^ 2 = ∑ i, ℓ i ^ 2 := lTwoNorm_sq ℓ
    have hTwoLe : lTwoNorm ℓ ^ 2 ≤ M * L := by
      rw [hTwo, hℓ, sum_siteEnum s0 fun y => smoothedCoeff 4 1 t 0 y ^ 2]
      have hle : ∀ y ∈ s0, smoothedCoeff 4 1 t 0 y ^ 2 ≤ greenTime 4 (1 + t) 0 y ^ 2 :=
        fun y _ => pow_le_pow_left₀ (smoothedCoeff_nonneg _ _ _ _)
          (smoothedCoeff_le_greenTime 1 t 0 y) 2
      refine le_trans (Finset.sum_le_sum hle) ?_
      rw [← tsum_greenTime_sq_eq_sum (1 + t) (0 : Site 4)]
      refine le_trans (hM2 (1 + t) 0) ?_
      refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hM0.le
      rw [hLdef]
      congr 1
      push_cast
      ring
    have hTwoPos : 0 < lTwoNorm ℓ ^ 2 := by
      rw [hTwo]
      refine lt_of_lt_of_le (pow_pos hi₀pos 2) ?_
      exact Finset.single_le_sum (f := fun i : Fin N => ℓ i ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
    have hInfLe : lInfNorm ℓ ≤ M :=
      ciSup_le fun i => le_trans (smoothedCoeff_le_greenTime 1 t 0 _) (hMinf _ _ _)
    have hInfPos : 0 < lInfNorm ℓ := lt_of_lt_of_le hi₀pos (le_lInfNorm ℓ i₀)
    have hkey := hconc N ν hprob hexpint hexp (scenerySmoothed s0 1 t 0)
      (measurable_scenerySmoothed s0 1 t 0) ℓ hℓnn hne
      (fun ξ i y => abs_scenerySmoothed_update_le s0 1 t 0 ξ i y) s hs
    have hmp := LatticeProb.measurePreserving_pick _ ν (siteEnum s0) (siteEnum_injective s0)
    have hmean' : (∫ η, scenerySmoothed s0 1 t 0 η ∂(Measure.pi fun _ : Fin N => ν)) = mean := by
      rw [← integral_pick ν _ (siteEnum_injective s0) _
        (measurable_scenerySmoothed s0 1 t 0).aestronglyMeasurable,
        integral_congr_ae (Filter.Eventually.of_forall fun ζ =>
          scenerySmoothed_pick (subset_refl s0) ζ)]
      exact integral_avg_odometerOf (by norm_num) ν hpos 1 t 0
    rw [hmean'] at hkey
    have hmeasset : MeasurableSet {ξ : Fin N → ℝ | s ≤ |scenerySmoothed s0 1 t 0 ξ - mean|} :=
      measurableSet_le measurable_const
        (((measurable_scenerySmoothed s0 1 t 0).sub measurable_const).abs)
    have hsubset : {ζ : Site 4 → ℝ | (avg^[1] fun x => odometerOf ζ t x -
          ∫ η, odometerOf η t 0 ∂P) 0 ≤ -s}
        ⊆ (fun ζ : Site 4 → ℝ => fun i => ζ (siteEnum s0 i)) ⁻¹'
          {ξ | s ≤ |scenerySmoothed s0 1 t 0 ξ - mean|} := by
      intro ζ hζ
      simp only [Set.mem_setOf_eq] at hζ
      rw [avg_iterate_sub_const (by norm_num) 1 (odometerOf ζ t) _ 0] at hζ
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [scenerySmoothed_pick (subset_refl s0) ζ]
      refine le_trans ?_ (neg_le_abs _)
      rw [← hmeandef] at hζ
      linarith
    have hmin : (c₀ / M) * min (s ^ 2 / L) s
        ≤ c₀ * min (s ^ 2 / lTwoNorm ℓ ^ 2) (s / lInfNorm ℓ) := by
      rw [mul_min_of_nonneg _ _ (div_pos hc₀ hM0).le, mul_min_of_nonneg _ _ hc₀.le]
      refine min_le_min ?_ ?_
      · rw [show (c₀ / M) * (s ^ 2 / L) = c₀ * (s ^ 2 / (M * L)) by field_simp]
        refine mul_le_mul_of_nonneg_left ?_ hc₀.le
        exact div_le_div_of_nonneg_left (sq_nonneg s) hTwoPos hTwoLe
      · rw [show (c₀ / M) * s = c₀ * (s / M) by ring]
        refine mul_le_mul_of_nonneg_left ?_ hc₀.le
        exact div_le_div_of_nonneg_left hs hInfPos hInfLe
    calc P {ζ : Site 4 → ℝ | (avg^[1] fun x => odometerOf ζ t x -
          ∫ η, odometerOf η t 0 ∂P) 0 ≤ -s}
        ≤ P ((fun ζ : Site 4 → ℝ => fun i => ζ (siteEnum s0 i)) ⁻¹'
            {ξ | s ≤ |scenerySmoothed s0 1 t 0 ξ - mean|}) := measure_mono hsubset
      _ = (Measure.pi fun _ : Fin N => ν)
            {ξ | s ≤ |scenerySmoothed s0 1 t 0 ξ - mean|} :=
          hmp.measure_preimage hmeasset.nullMeasurableSet
      _ ≤ ENNReal.ofReal (C₀ * Real.exp (-(c₀ *
            min (s ^ 2 / lTwoNorm ℓ ^ 2) (s / lInfNorm ℓ)))) := hkey
      _ ≤ ENNReal.ofReal (max C₀ 1 * Real.exp (-(c₀ / M * min (s ^ 2 / L) s))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr (by linarith))
            (Real.exp_nonneg _) (le_trans hC₀.le (le_max_left _ _))

/-- **The lower tail of the smoothed centred odometer, at a fixed `ν`.** This specializes
`exists_smoothed_odometer_tail_four_uniform` to one probability measure `ν` already known to
satisfy its hypotheses. -/
theorem exists_smoothed_odometer_tail_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (t : ℕ) (s : ℝ), 0 ≤ s →
      LatticeProb.iidLaw 4 ν
          {ζ : Site 4 → ℝ | (avg^[1] fun x => odometerOf ζ t x -
            ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) 0 ≤ -s} ≤
        ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2 / Real.log ((t : ℝ) + 3)) s))) := by
  obtain ⟨c, C, hc, hC, h⟩ := exists_smoothed_odometer_tail_four_uniform hVS θ₀ K₀ hθ₀
  exact ⟨c, C, hc, hC, h ν hprob hexpint hexp hpos⟩

/-- **The lower tail of `ζ(0) + P u_t(0)` in dimension four.** -/
theorem exists_reflected_tail_four_uniform (hVS : Sandpile.External.VarianceScale)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        (∫ z, Real.exp (θ₀ * |z|) ∂ν) ≤ K₀ →
        Integrable (fun z : ℝ => max z 0) ν →
        ∀ (t : ℕ) (h : ℝ), 0 ≤ h →
      (LatticeProb.iidLaw 4 ν).real
          {ζ : Site 4 → ℝ | h ≤ -(ζ 0) - avg (odometerOf ζ t) 0} ≤
        C * Real.exp (-(c * min (((h + ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) / 2) ^ 2 /
            Real.log ((t : ℝ) + 3))
          ((h + ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) / 2))) := by
  classical
  obtain ⟨c₀, C₀, hc₀, hC₀, hsm⟩ :=
    exists_smoothed_odometer_tail_four_uniform hVS θ₀ K₀ hθ₀
  have hK₀ : 0 < max K₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨min θ₀ c₀, max K₀ 1 + C₀, lt_min hθ₀ hc₀, by positivity, ?_⟩
  intro ν hprob hexpint hexp hpos t h hh
  haveI := hprob
  have hsm := hsm ν hprob hexpint hexp hpos
  set P : Measure (Site 4 → ℝ) := LatticeProb.iidLaw 4 ν with hP
  set mean : ℝ := ∫ η, odometerOf η t 0 ∂P with hmeandef
  have hmeannn : 0 ≤ mean := integral_nonneg fun ζ => odometerOf_nonneg ζ t 0
  set s : ℝ := (h + mean) / 2 with hsdef
  have hs0 : (0 : ℝ) ≤ s := by rw [hsdef]; linarith
  set L : ℝ := Real.log ((t : ℝ) + 3) with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    refine le_trans one_le_log_three (Real.log_le_log (by norm_num) ?_)
    have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  set A : Set (Site 4 → ℝ) := {ζ : Site 4 → ℝ | h ≤ -(ζ 0) - avg (odometerOf ζ t) 0} with hA
  set A₁ : Set (Site 4 → ℝ) := {ζ : Site 4 → ℝ | ζ 0 ≤ -s} with hA₁
  set A₂ : Set (Site 4 → ℝ) :=
    {ζ : Site 4 → ℝ | (avg^[1] fun x => odometerOf ζ t x - mean) 0 ≤ -s} with hA₂
  have hsub : A ⊆ A₁ ∪ A₂ := by
    intro ζ hζ
    rcases reflected_subset (d := 4) (by norm_num) ζ t mean h hζ with h1 | h2
    · exact Or.inl h1
    · exact Or.inr h2
  have hb₁ : P.real A₁ ≤ max K₀ 1 * Real.exp (-(θ₀ * s)) := by
    rw [hA₁, measureReal_coord_le ν 0 (-s)]
    exact measureReal_Iic_le_of_exp_moment ν hθ₀ hexpint
      (le_trans hexp (le_max_left K₀ 1)) s
  have hb₂ : P.real A₂ ≤ C₀ * Real.exp (-(c₀ * min (s ^ 2 / L) s)) := by
    have hmm := hsm t s hs0
    have hnn : (0 : ℝ) ≤ C₀ * Real.exp (-(c₀ * min (s ^ 2 / L) s)) := by positivity
    rw [hA₂, Measure.real, ← ENNReal.toReal_ofReal hnn]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hmm
  have hminle : min (s ^ 2 / L) s ≤ s := min_le_right _ _
  have hminnn : 0 ≤ min (s ^ 2 / L) s :=
    le_min (by positivity) hs0
  have hc1 : Real.exp (-(θ₀ * s)) ≤ Real.exp (-(min θ₀ c₀ * min (s ^ 2 / L) s)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left θ₀ c₀, hminnn, hminle, hθ₀.le])
  have hc2 : Real.exp (-(c₀ * min (s ^ 2 / L) s))
      ≤ Real.exp (-(min θ₀ c₀ * min (s ^ 2 / L) s)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right θ₀ c₀, hminnn])
  have hunion : P.real A ≤ P.real A₁ + P.real A₂ :=
    le_trans (measureReal_mono hsub) (measureReal_union_le _ _)
  calc P.real A ≤ P.real A₁ + P.real A₂ := hunion
    _ ≤ max K₀ 1 * Real.exp (-(min θ₀ c₀ * min (s ^ 2 / L) s))
        + C₀ * Real.exp (-(min θ₀ c₀ * min (s ^ 2 / L) s)) := by
        have h1 := mul_le_mul_of_nonneg_left hc1 hK₀.le
        have h2 := mul_le_mul_of_nonneg_left hc2 hC₀.le
        linarith [hb₁, hb₂]
    _ = (max K₀ 1 + C₀) * Real.exp (-(min θ₀ c₀ * min (s ^ 2 / L) s)) := by ring

/-- **The lower tail of `ζ(0) + P u_t(0)`, at a fixed `ν`.** This specializes
`exists_reflected_tail_four_uniform` to one probability measure `ν` already known to satisfy
its hypotheses. -/
theorem exists_reflected_tail_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (t : ℕ) (h : ℝ), 0 ≤ h →
      (LatticeProb.iidLaw 4 ν).real
          {ζ : Site 4 → ℝ | h ≤ -(ζ 0) - avg (odometerOf ζ t) 0} ≤
        C * Real.exp (-(c * min (((h + ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) / 2) ^ 2 /
            Real.log ((t : ℝ) + 3))
          ((h + ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) / 2))) := by
  obtain ⟨c, C, hc, hC, h⟩ := exists_reflected_tail_four_uniform hVS θ₀ K₀ hθ₀
  exact ⟨c, C, hc, hC, h ν hprob hexpint hexp hpos⟩

/-- **The crude increment bound in dimension four.**  Integrating the reflected
tail over the level `h` gives
`E u_{t+1}(0) - E u_t(0) ≤ C e^{a ℓ} exp{-c min(m_t²/ℓ, m_t)}` with
`ℓ = log(t+3)`. -/
theorem exists_crude_increment_four_uniform (hVS : Sandpile.External.VarianceScale)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ a c C : ℝ, 0 < a ∧ 0 < c ∧ 0 < C ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        (∫ z, z ∂ν = 0) →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        (∫ z, Real.exp (θ₀ * |z|) ∂ν) ≤ K₀ →
        Integrable id ν →
        Integrable (fun z : ℝ => max z 0) ν →
        ∀ t : ℕ,
      (∫ ζ, odometerOf ζ (t + 1) 0 ∂(LatticeProb.iidLaw 4 ν))
          - ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν)
        ≤ C * Real.exp (a * Real.log ((t : ℝ) + 3)) *
            Real.exp (-(c * min ((∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν)) ^ 2 /
                Real.log ((t : ℝ) + 3))
              (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν)))) := by
  classical
  obtain ⟨c₁, C₁, hc₁, hC₁, htail⟩ :=
    exists_reflected_tail_four_uniform hVS θ₀ K₀ hθ₀
  refine ⟨c₁, c₁ / 4, 2 * C₁ / c₁, hc₁, by positivity, by positivity, ?_⟩
  intro ν hprob hmean hexpint hexp hint hpos t
  haveI := hprob
  have htail := htail ν hprob hexpint hexp hpos
  set P : Measure (Site 4 → ℝ) := LatticeProb.iidLaw 4 ν with hP
  set mean : ℝ := ∫ η, odometerOf η t 0 ∂P with hmeandef
  have hmeannn : 0 ≤ mean := integral_nonneg fun ζ => odometerOf_nonneg ζ t 0
  set L : ℝ := Real.log ((t : ℝ) + 3) with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    refine le_trans one_le_log_three (Real.log_le_log (by norm_num) ?_)
    have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  set E : ℝ := Real.exp (-(c₁ / 4 * min (mean ^ 2 / L) mean)) with hEdef
  set B : ℝ := C₁ * Real.exp (c₁ * L) * E with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set f : (Site 4 → ℝ) → ℝ := fun ζ => max 0 (-(ζ 0) - avg (odometerOf ζ t) 0) with hf
  have hfint : Integrable f P := integrable_reflected ν hint hpos t
  have hfnn : 0 ≤ᵐ[P] f := Filter.Eventually.of_forall fun ζ => le_max_left _ _
  have hlayer : ∫ ζ, f ζ ∂P = ∫ h in Set.Ioi (0 : ℝ), P.real {ζ | h ≤ f ζ} :=
    hfint.integral_eq_integral_meas_le hfnn
  have hbint : IntegrableOn (fun h : ℝ => B * Real.exp (-(c₁ / 2) * h)) (Set.Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 (by positivity)).const_mul B
  have hdom : ∫ h in Set.Ioi (0 : ℝ), P.real {ζ | h ≤ f ζ}
      ≤ ∫ h in Set.Ioi (0 : ℝ), B * Real.exp (-(c₁ / 2) * h) := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun h => ENNReal.toReal_nonneg) hbint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hh0 : 0 < h := hh
    have hset : {ζ : Site 4 → ℝ | h ≤ f ζ}
        = {ζ : Site 4 → ℝ | h ≤ -(ζ 0) - avg (odometerOf ζ t) 0} := by
      ext ζ
      simp only [Set.mem_setOf_eq, hf, le_max_iff]
      constructor
      · rintro (hc | hc)
        · linarith
        · exact hc
      · intro hc; exact Or.inr hc
    rw [hset]
    refine le_trans (htail t h hh0.le) ?_
    -- the exponent comparison
    set s : ℝ := (h + mean) / 2 with hsdef
    have hs0 : (0 : ℝ) ≤ s := by rw [hsdef]; linarith
    have hsplit : min ((h / 2) ^ 2 / L) (h / 2) + min ((mean / 2) ^ 2 / L) (mean / 2)
        ≤ min (s ^ 2 / L) s := by
      refine le_min (le_trans (add_le_add (min_le_left _ _) (min_le_left _ _)) ?_)
        (le_trans (add_le_add (min_le_right _ _) (min_le_right _ _)) (le_of_eq (by
          rw [hsdef]; ring)))
      rw [← add_div, hsdef]
      refine div_le_div_of_nonneg_right ?_ hL0.le
      nlinarith [hh0.le, hmeannn]
    have hhalf : h / 2 - L ≤ min ((h / 2) ^ 2 / L) (h / 2) := by
      rcases le_total L (h / 2) with hcase | hcase
      · have : h / 2 ≤ (h / 2) ^ 2 / L := by
          rw [le_div_iff₀ hL0]
          nlinarith [hh0.le]
        rw [min_eq_right this]
        linarith
      · have hnn1 : (0 : ℝ) ≤ (h / 2) ^ 2 / L := by positivity
        have hnn2 : (0 : ℝ) ≤ h / 2 := by linarith
        have : (0 : ℝ) ≤ min ((h / 2) ^ 2 / L) (h / 2) := le_min hnn1 hnn2
        linarith
    have hquarter : (1 / 4 : ℝ) * min (mean ^ 2 / L) mean
        ≤ min ((mean / 2) ^ 2 / L) (mean / 2) := by
      refine le_min ?_ ?_
      · have h1 : (mean / 2) ^ 2 / L = (1 / 4 : ℝ) * (mean ^ 2 / L) := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
      · have h2 : (1 / 4 : ℝ) * min (mean ^ 2 / L) mean ≤ (1 / 4 : ℝ) * mean :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        linarith
    have hexpcmp : C₁ * Real.exp (-(c₁ * min (s ^ 2 / L) s))
        ≤ B * Real.exp (-(c₁ / 2) * h) := by
      rw [hBdef, hEdef]
      rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₁.le
      have hkey : h / 2 - L + (1 / 4 : ℝ) * min (mean ^ 2 / L) mean ≤ min (s ^ 2 / L) s := by
        linarith [hsplit, hhalf, hquarter]
      nlinarith [hkey, hc₁.le]
    exact hexpcmp
  have hval : ∫ h in Set.Ioi (0 : ℝ), B * Real.exp (-(c₁ / 2) * h) = B * (2 / c₁) := by
    rw [integral_const_mul, integral_exp_neg_mul_Ioi_zero (by positivity)]
    field_simp
  rw [meanOdometerOf_succ_sub (by norm_num) ν hint hmean hpos t, ← hf, hlayer]
  refine le_trans hdom ?_
  rw [hval, hBdef, hEdef]
  ring_nf
  exact le_rfl

/-- **The crude increment bound, at a fixed `ν`.** This specializes
`exists_crude_increment_four_uniform` to one probability measure `ν` already known to satisfy
its hypotheses. -/
theorem exists_crude_increment_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (hint : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν) :
    ∃ a c C : ℝ, 0 < a ∧ 0 < c ∧ 0 < C ∧ ∀ t : ℕ,
      (∫ ζ, odometerOf ζ (t + 1) 0 ∂(LatticeProb.iidLaw 4 ν))
          - ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν)
        ≤ C * Real.exp (a * Real.log ((t : ℝ) + 3)) *
            Real.exp (-(c * min ((∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν)) ^ 2 /
                Real.log ((t : ℝ) + 3))
              (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν)))) := by
  obtain ⟨a, c, C, ha, hc, hC, h⟩ := exists_crude_increment_four_uniform hVS θ₀ K₀ hθ₀
  exact ⟨a, c, C, ha, hc, hC, h ν hprob hmean hexpint hexp hint hpos⟩

/-- `log(t+3) ≤ 2 log(t+2)`, since `t + 3 ≤ (t+2)²`. -/
theorem log_add_three_le (t : ℕ) :
    Real.log ((t : ℝ) + 3) ≤ 2 * Real.log ((t : ℝ) + 2) := by
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hsq : ((t : ℝ) + 3) ≤ ((t : ℝ) + 2) ^ 2 := by nlinarith
  have h := Real.log_le_log (by linarith) hsq
  rwa [Real.log_pow] at h

/-- **The crude logarithmic upper bound in dimension four**, the first half of
`eq:d4-logarithmic-mean-bounds`. -/
theorem exists_crude_log_upper_four_uniform (hVS : Sandpile.External.VarianceScale)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        (∫ z, z ∂ν = 0) →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        (∫ z, Real.exp (θ₀ * |z|) ∂ν) ≤ K₀ →
        Integrable id ν →
        Integrable (fun z : ℝ => max z 0) ν →
        ∀ t : ℕ,
      (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν)) ≤ C * Real.log ((t : ℝ) + 2) := by
  classical
  obtain ⟨a, c, C₂, ha, hc, hC₂, hstep⟩ :=
    exists_crude_increment_four_uniform hVS θ₀ K₀ hθ₀
  set A : ℝ := max 1 ((a + 1) / c) with hA
  have hA1 : (1 : ℝ) ≤ A := le_max_left _ _
  have hAc : a + 1 ≤ c * A := by
    have h1 : (a + 1) / c ≤ A := le_max_right _ _
    rw [div_le_iff₀ hc] at h1
    linarith
  set D := max K₀ 1 / θ₀
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨2 * (A + D + C₂), by positivity, ?_⟩
  intro ν hprob hmean hexpint hexp hint hpos t
  haveI := hprob
  have hstep := hstep ν hprob hmean hexpint hexp hint hpos
  set P : Measure (Site 4 → ℝ) := LatticeProb.iidLaw 4 ν with hP
  set m : ℕ → ℝ := fun n => ∫ ζ, odometerOf ζ n 0 ∂P with hmdef
  have hmnn : ∀ n, 0 ≤ m n := fun n => integral_nonneg fun ζ => odometerOf_nonneg ζ n 0
  have hmmono : Monotone m := meanOdometerOf_mono (d := 4) ν hpos
  have hD : (∫ ζ : Site 4 → ℝ, max 0 (-(ζ 0)) ∂P) ≤ D := by
    change (∫ ζ : Site 4 → ℝ, max 0 (-(ζ 0)) ∂(LatticeProb.iidLaw 4 ν)) ≤ D
    rw [LatticeProb.iidLaw,
      LatticeProb.integral_eval (fun _ : Site 4 => ν) 0 (fun z : ℝ => max 0 (-z)) (by fun_prop)]
    have hneg : Integrable (fun z : ℝ => max 0 (-z)) ν :=
      hint.abs.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left 0 (-z))]
        exact max_le (abs_nonneg z) (neg_le_abs z))
    have hbd := integral_mono hneg (hexpint.div_const θ₀) (fun z => ?_)
    · rw [integral_div] at hbd
      exact hbd.trans (div_le_div_of_nonneg_right (hexp.trans (le_max_left _ _)) hθ₀.le)
    · rw [le_div_iff₀ hθ₀]
      have h1 : max 0 (-z) ≤ |z| := max_le (abs_nonneg z) (neg_le_abs z)
      have h2 := Real.add_one_le_exp (θ₀ * |z|)
      nlinarith
  have huniform : ∀ n : ℕ, m (n + 1) - m n ≤ D := fun n =>
    (meanOdometerOf_succ_sub_le (by norm_num) ν hint hmean hpos n).trans hD

  set ell : ℝ := Real.log ((t : ℝ) + 3) with hell
  have hell1 : (1 : ℝ) ≤ ell := by
    rw [hell]
    refine le_trans one_le_log_three (Real.log_le_log (by norm_num) ?_)
    have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  have hell0 : (0 : ℝ) < ell := lt_of_lt_of_le one_pos hell1
  set K : ℝ := C₂ * Real.exp (-ell) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  -- the small increment above the level `A ell`
  have hstep_large : ∀ n : ℕ, n ≤ t → A * ell ≤ m n → m (n + 1) - m n ≤ K := by
    intro n hnt hlarge
    have hLn : Real.log ((n : ℝ) + 3) ≤ ell := by
      rw [hell]
      refine Real.log_le_log (by positivity) ?_
      have : (n : ℝ) ≤ (t : ℝ) := by exact_mod_cast hnt
      linarith
    have hLn1 : (1 : ℝ) ≤ Real.log ((n : ℝ) + 3) := by
      refine le_trans one_le_log_three (Real.log_le_log (by norm_num) ?_)
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hLn0 : (0 : ℝ) < Real.log ((n : ℝ) + 3) := lt_of_lt_of_le one_pos hLn1
    have hAell : 0 ≤ A * ell := by positivity
    have hmin : A * ell ≤ min (m n ^ 2 / Real.log ((n : ℝ) + 3)) (m n) := by
      refine le_min ?_ hlarge
      rw [le_div_iff₀ hLn0]
      have h1 : A * ell * Real.log ((n : ℝ) + 3) ≤ A * ell * ell :=
        mul_le_mul_of_nonneg_left hLn hAell
      have h2 : A * ell * ell ≤ (A * ell) ^ 2 := by nlinarith [hA1, hell0.le]
      have h3 : (A * ell) ^ 2 ≤ m n ^ 2 := by nlinarith [hlarge, hAell]
      linarith
    have hexpcmp : Real.exp (a * Real.log ((n : ℝ) + 3)) *
        Real.exp (-(c * min (m n ^ 2 / Real.log ((n : ℝ) + 3)) (m n)))
          ≤ Real.exp (-ell) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 : a * Real.log ((n : ℝ) + 3) ≤ a * ell := mul_le_mul_of_nonneg_left hLn ha.le
      have h2 : c * (A * ell) ≤ c * min (m n ^ 2 / Real.log ((n : ℝ) + 3)) (m n) :=
        mul_le_mul_of_nonneg_left hmin hc.le
      have h3 : (1 : ℝ) * ell ≤ (c * A - a) * ell :=
        mul_le_mul_of_nonneg_right (by linarith) hell0.le
      nlinarith [h1, h2, h3]
    calc m (n + 1) - m n
        ≤ C₂ * Real.exp (a * Real.log ((n : ℝ) + 3)) *
            Real.exp (-(c * min (m n ^ 2 / Real.log ((n : ℝ) + 3)) (m n))) := hstep n
      _ = C₂ * (Real.exp (a * Real.log ((n : ℝ) + 3)) *
            Real.exp (-(c * min (m n ^ 2 / Real.log ((n : ℝ) + 3)) (m n)))) := by ring
      _ ≤ C₂ * Real.exp (-ell) := mul_le_mul_of_nonneg_left hexpcmp hC₂.le
      _ = K := by rw [hK]
  -- the running bound
  have hkey : ∀ n : ℕ, n ≤ t → m n ≤ A * ell + D + (n : ℝ) * K := by
    intro n
    induction n with
    | zero =>
        intro _
        have h0 : m 0 = 0 := by simp [hmdef, odometerOf]
        have : (0 : ℝ) ≤ A * ell := by positivity
        rw [h0]; push_cast; linarith
    | succ n ih =>
        intro hn1
        have hnt : n ≤ t := by omega
        have hIH := ih hnt
        rcases lt_or_ge (m n) (A * ell) with hsmall | hbig
        · have := huniform n
          push_cast
          nlinarith [hK0, Nat.cast_nonneg (α := ℝ) n]
        · have := hstep_large n hnt hbig
          push_cast
          linarith
  have hfinal := hkey t le_rfl
  have hexpell : Real.exp (-ell) = 1 / ((t : ℝ) + 3) := by
    rw [hell, Real.exp_neg, Real.exp_log (by positivity), one_div]
  have htK : (t : ℝ) * K ≤ C₂ := by
    rw [hK, hexpell]
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    have h1 : (t : ℝ) * (C₂ * (1 / ((t : ℝ) + 3))) = C₂ * ((t : ℝ) / ((t : ℝ) + 3)) := by
      field_simp
    rw [h1]
    have h2 : (t : ℝ) / ((t : ℝ) + 3) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    nlinarith [hC₂.le]
  have hmt : m t ≤ (A + D + C₂) * ell := by
    have : m t ≤ A * ell + D + C₂ := by linarith [hfinal, htK]
    nlinarith [hell1, hD0, hC₂.le]
  calc m t ≤ (A + D + C₂) * ell := hmt
    _ ≤ (A + D + C₂) * (2 * Real.log ((t : ℝ) + 2)) := by
        refine mul_le_mul_of_nonneg_left (log_add_three_le t) (by positivity)
    _ = 2 * (A + D + C₂) * Real.log ((t : ℝ) + 2) := by ring

/-- **The crude logarithmic upper bound, at a fixed `ν`.** This specializes
`exists_crude_log_upper_four_uniform` to one probability measure `ν` already known to satisfy
its hypotheses. -/
theorem exists_crude_log_upper_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (hint : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν)) ≤ C * Real.log ((t : ℝ) + 2) := by
  obtain ⟨C, hC, h⟩ := exists_crude_log_upper_four_uniform hVS θ₀ K₀ hθ₀
  exact ⟨C, hC, h ν hprob hmean hexpint hexp hint hpos⟩

end Sandpile
