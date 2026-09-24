/-
The pointwise concentration of the odometer in dimension five and above,
`eq:dgt4-pointwise-concentration` of `sandpile.tex:4138-4141`, together with the
two uniform bounds on the Green coefficients that it needs.

The odometer at a site is a functional of finitely many sites of the scenery,
Lipschitz in each with the Green kernel as the constant, so the general
concentration lemma applies to it.  What dimension five and above supplies is
that both the square sum and the supremum of those constants are bounded
uniformly in the time and in the base point, which turns the lemma's
`min(s^2/|l|_2^2, s/|l|_inf)` into the paper's `min(s^2, s)`.
-/
import Sandpile.Frozen.WeightedExpConcentration
import Sandpile.Support.GreenHigh
import Sandpile.Support.FiniteCoord
import Sandpile.Support.Stationary

open LatticeProb

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

theorem exists_siteEnum_eq (s : Finset (Site d)) {z : Site d} (hz : z ∈ s) :
    ∃ i : Fin s.card, siteEnum s i = z := by
  refine ⟨s.equivFin ⟨z, hz⟩, ?_⟩
  show ((s.equivFin.symm (s.equivFin ⟨z, hz⟩) : ↥s) : Site d) = z
  rw [Equiv.symm_apply_apply]

theorem one_le_greenTime_self (t : ℕ) (ht : 1 ≤ t) (x : Site d) : 1 ≤ greenTime d t x x := by
  have h0 : (0 : ℕ) ∈ Finset.range t := Finset.mem_range.mpr ht
  have := Finset.single_le_sum (f := fun k => heatKernel d k x x)
    (fun k _ => heatKernel_nonneg k x x) h0
  simpa [greenTime, LatticeProb.greenTime, heatKernel, LatticeProb.LocalCLT.heatKernel] using this

theorem exists_greenTime_norm_bounds (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) :
    ∃ M : ℝ, 1 ≤ M ∧
      (∀ (t : ℕ) (x : Site d), (∑' z : Site d, greenTime d t x z ^ 2) ≤ M) ∧
      (∀ (t : ℕ) (x y : Site d), greenTime d t x y ≤ M) := by
  obtain ⟨-, hl2, -, -, -⟩ := hGH d hd
  obtain ⟨CG, hCG, hpt⟩ := exists_green_pointwise hGH hd
  have hd2 : (2 : ℝ) - (d : ℝ) ≤ 0 := by
    have : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hgle : ∀ y : Site d, green d 0 y ≤ CG := by
    intro y
    refine le_trans (hpt y) ?_
    have h1 : (1 : ℝ) ≤ 1 + Sandpile.External.latticeNorm y := by
      have : 0 ≤ Sandpile.External.latticeNorm y := Real.sqrt_nonneg _
      linarith
    have := Real.rpow_le_one_of_one_le_of_nonpos h1 hd2
    nlinarith
  refine ⟨max (∑' z : Site d, green d 0 z ^ 2) CG + 1, ?_, ?_, ?_⟩
  · have h2 : CG ≤ max (∑' z : Site d, green d 0 z ^ 2) CG := le_max_right _ _
    linarith
  · intro t x
    rw [tsum_greenTime_sq_eq]
    have hsum : Summable fun z : Site d => greenTime d t 0 z ^ 2 := by
      refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_) hl2
      have h1 := greenTime_le_green hGH hd t z
      have h2 := greenTime_nonneg t (0 : Site d) z
      nlinarith
    have hle : ∑' z : Site d, greenTime d t 0 z ^ 2 ≤ ∑' z : Site d, green d 0 z ^ 2 := by
      refine hsum.tsum_le_tsum (fun z => ?_) hl2
      have h1 := greenTime_le_green hGH hd t z
      have h2 := greenTime_nonneg t (0 : Site d) z
      nlinarith
    have := le_max_left (∑' z : Site d, green d 0 z ^ 2) CG
    linarith
  · intro t x y
    have hshift : greenTime d t x y = greenTime d t 0 (y - x) := by
      have := greenTime_add_right t (0 : Site d) (y - x) x
      simpa using this
    rw [hshift]
    have h1 := greenTime_le_green hGH hd t (y - x)
    have h2 := hgle (y - x)
    have := le_max_right (∑' z : Site d, green d 0 z ^ 2) CG
    linarith

/-- **The pointwise concentration of the odometer**, `eq:dgt4-pointwise-concentration`
of `sandpile.tex:4133-4136`.  The odometer at any site is a coordinate-Lipschitz
functional of the scenery with Green constants, and in dimension five and above
both the square sum and the supremum of those constants are bounded uniformly in
the time and the base point. -/
theorem exists_odometerOf_conc (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ (x : Site d) (t : ℕ) (s : ℝ), 0 ≤ s →
          LatticeProb.iidLaw d ν
              {ζ | s ≤ |odometerOf ζ t x -
                ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)|} ≤
            ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2) s))) := by
  classical
  obtain ⟨M, hM, hM2, hMinf⟩ := exists_greenTime_norm_bounds hGH hd
  obtain ⟨c₀, C₀, hc₀, hC₀, hconc⟩ := Sandpile.Frozen.weighted_exp_concentration.2.1 θ₀ K₀ hθ₀
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  refine ⟨c₀ / M, max C₀ 1, div_pos hc₀ hM0, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro ν hprob hexpint hexp x t s hs
  haveI := hprob
  rcases hs.eq_or_lt with hs0 | hspos
  · -- `s = 0`: the bound is at least one and a probability is at most one
    subst hs0
    refine le_trans prob_le_one ?_
    have : (0 : ℝ) ≤ 1 := zero_le_one
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (max C₀ 1 * Real.exp (-(c₀ / M * min ((0:ℝ) ^ 2) 0))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          simp
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · -- with no toppling the odometer and its mean are zero
    have hI : (∫ η, odometerOf η 0 (0 : Site d) ∂(LatticeProb.iidLaw d ν)) = 0 := by
      simp [odometerOf]
    have hempty : {ζ : Site d → ℝ | s ≤ |odometerOf ζ 0 x -
        ∫ η, odometerOf η 0 (0 : Site d) ∂(LatticeProb.iidLaw d ν)|} = ∅ := by
      ext ζ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le, hI]
      show |(0 : ℝ) - 0| < s
      simpa using hspos
    rw [hempty]
    simp
  · set N := (boxFinset x t).card with hN
    set ℓ : Fin N → ℝ := fun i => greenTime d t x (boxEnum x t i) with hℓ
    have hℓnn : ∀ i, 0 ≤ ℓ i := fun i => greenTime_nonneg _ _ _
    obtain ⟨i₀, hi₀⟩ := exists_siteEnum_eq (boxFinset x t)
      (mem_boxFinset (x := x) (y := x) (r := t) (by rw [boxDist_self]; exact Nat.zero_le t))
    have hℓi₀ : (1 : ℝ) ≤ ℓ i₀ := by
      have hval : ℓ i₀ = greenTime d t x x := congrArg (greenTime d t x) hi₀
      rw [hval]
      exact one_le_greenTime_self t ht x
    have hne : ∃ i, ℓ i ≠ 0 := ⟨i₀, by intro h; rw [h] at hℓi₀; linarith⟩
    -- the two norms of the coefficient vector
    have hTwo : lTwoNorm ℓ ^ 2 = ∑ i, ℓ i ^ 2 := lTwoNorm_sq ℓ
    have hTwoLe : lTwoNorm ℓ ^ 2 ≤ M := by
      rw [hTwo, hℓ]
      have hsum : ∑ i : Fin N, greenTime d t x (boxEnum x t i) ^ 2
          = ∑' z : Site d, greenTime d t x z ^ 2 := by
        rw [tsum_greenTime_sq_eq_sum]
        exact sum_boxEnum x t fun z => greenTime d t x z ^ 2
      rw [hsum]
      exact hM2 t x
    have hTwoPos : 0 < lTwoNorm ℓ ^ 2 := by
      rw [hTwo]
      refine lt_of_lt_of_le (pow_pos (by linarith : (0:ℝ) < ℓ i₀) 2) ?_
      exact Finset.single_le_sum (f := fun i : Fin N => ℓ i ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
    haveI : Nonempty (Fin N) := ⟨i₀⟩
    have hInfLe : lInfNorm ℓ ≤ M := ciSup_le fun i => hMinf t x _
    have hInfPos : 0 < lInfNorm ℓ := lt_of_lt_of_le (by linarith) (le_lInfNorm ℓ i₀)
    -- the concentration bound in the box coordinates
    have hkey := hconc N ν hprob hexpint hexp (boxOdometer t x)
      (measurable_boxOdometer t x) ℓ hℓnn hne
      (fun ξ i y => abs_boxOdometer_update_le t x ξ i y) s hs
    have hmp := LatticeProb.measurePreserving_pick _ ν (boxEnum x t) (boxEnum_injective x t)
    have hmean : (∫ ξ, boxOdometer t x ξ ∂(Measure.pi fun _ : Fin N => ν))
        = ∫ η, odometerOf η t (0 : Site d) ∂(LatticeProb.iidLaw d ν) := by
      rw [← integral_pick ν (boxEnum x t) (boxEnum_injective x t) (boxOdometer t x)
        (measurable_boxOdometer t x).aestronglyMeasurable,
        integral_congr_ae (Filter.Eventually.of_forall fun ζ => boxOdometer_pick t x ζ)]
      exact integral_odometerOf_eq d ν t x
    have hmeasset : MeasurableSet {ξ : Fin N → ℝ | s ≤ |boxOdometer t x ξ -
        ∫ η, boxOdometer t x η ∂(Measure.pi fun _ : Fin N => ν)|} :=
      measurableSet_le measurable_const
        (((measurable_boxOdometer t x).sub measurable_const).abs)
    have hpre : {ζ : Site d → ℝ | s ≤ |odometerOf ζ t x -
          ∫ η, odometerOf η t (0 : Site d) ∂(LatticeProb.iidLaw d ν)|}
        = (fun ζ : Site d → ℝ => fun i => ζ (boxEnum x t i)) ⁻¹'
          {ξ | s ≤ |boxOdometer t x ξ -
            ∫ η, boxOdometer t x η ∂(Measure.pi fun _ : Fin N => ν)|} := by
      ext ζ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hmean, boxOdometer_pick t x ζ]
    -- the exponent comparison
    have hmin : (c₀ / M) * min (s ^ 2) s
        ≤ c₀ * min (s ^ 2 / lTwoNorm ℓ ^ 2) (s / lInfNorm ℓ) := by
      rw [mul_min_of_nonneg _ _ (div_pos hc₀ hM0).le, mul_min_of_nonneg _ _ hc₀.le]
      refine min_le_min ?_ ?_
      · rw [show (c₀ / M) * s ^ 2 = c₀ * (s ^ 2 / M) by ring]
        refine mul_le_mul_of_nonneg_left ?_ hc₀.le
        exact div_le_div_of_nonneg_left (sq_nonneg s) hTwoPos hTwoLe
      · rw [show (c₀ / M) * s = c₀ * (s / M) by ring]
        refine mul_le_mul_of_nonneg_left ?_ hc₀.le
        exact div_le_div_of_nonneg_left hs hInfPos hInfLe
    calc LatticeProb.iidLaw d ν {ζ : Site d → ℝ | s ≤ |odometerOf ζ t x -
            ∫ η, odometerOf η t (0 : Site d) ∂(LatticeProb.iidLaw d ν)|}
        = (Measure.pi fun _ : Fin N => ν)
            {ξ | s ≤ |boxOdometer t x ξ -
              ∫ η, boxOdometer t x η ∂(Measure.pi fun _ : Fin N => ν)|} := by
          rw [hpre]; exact hmp.measure_preimage hmeasset.nullMeasurableSet
      _ ≤ ENNReal.ofReal (C₀ * Real.exp (-(c₀ *
            min (s ^ 2 / lTwoNorm ℓ ^ 2) (s / lInfNorm ℓ)))) := hkey
      _ ≤ ENNReal.ofReal (max C₀ 1 * Real.exp (-(c₀ / M * min (s ^ 2) s))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr (by linarith))
            (Real.exp_nonneg _) (le_trans hC₀.le (le_max_left _ _))

end Sandpile
