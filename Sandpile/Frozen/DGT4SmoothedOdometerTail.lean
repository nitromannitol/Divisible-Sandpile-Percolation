/-
Lemma (lower tail of the smoothed centred odometer) of sandpile.tex, frozen.
`sandpile.tex:4461-4472` (label `lem:dgt4-smoothed-odometer-tail`):

  "Suppose $\E e^{\theta_0|\zeta(0)|}\leq K_0$ for some $\theta_0>0$ and
   $K_0<\infty$.  There are constants $c,C>0$ such that, for all $m\geq1$,
   $n\geq0$, and $s\geq1$,
     $\P\left(P^m(u_n-\E u_n(0))(0)\leq -s\right)
      \leq C\exp\left\{-c\min\left(s^2m^{(d-4)/2},sm^{(d-2)/2}\right)\right\}$."

The statement is about the scenery alone, so the field is `ζ` with i.i.d. law
`LatticeProb.iidLaw d ν` and the odometer is `Sandpile.odometerOf ζ`.  `P` is
the averaging operator `Sandpile.avg`, so `P^m` is `Sandpile.avg^[m]`, applied
to the function `fun x => odometerOf ζ n x - E u_n(0)` and then evaluated at
the origin, exactly as the paper writes it.  `E u_n(0)` is the integral of
`odometerOf ζ' n 0` against the same i.i.d. law.  The exponential moment is
transcribed as integrability of `exp (θ₀ |z|)` together with the bound `≤ K₀`,
so a non-integrable law cannot satisfy it through the junk value `∫ = 0`; the
standing hypotheses `E ζ(0) = 0` and `0 < Var(ζ(0)) < ∞` are listed too.  The
constants may depend on the law, as the section's convention allows, so they
are bound after `ν`.  The probability is compared in `ℝ≥0∞` against
`ENNReal.ofReal` of the right side, so no `toReal` junk enters, and the powers
`m^{(d-4)/2}` and `m^{(d-2)/2}` are real powers of the natural number `m`,
which is at least one.
-/
import Sandpile.Support.Smoothed
import Sandpile.Frozen.WeightedExpConcentration
import Sandpile.External.GreenBoundsHigh
import Sandpile.External.GreenBoundsHighProved

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_smoothed_odometer_tail
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, ∀ s : ℝ, 1 ≤ s →
      LatticeProb.iidLaw d ν
          {ζ : Sandpile.Site d → ℝ |
            (Sandpile.avg^[m] fun x => Sandpile.odometerOf ζ n x -
              ∫ ζ', Sandpile.odometerOf ζ' n 0 ∂(LatticeProb.iidLaw d ν)) 0 ≤ -s} ≤
        ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2 * (m : ℝ) ^ (((d : ℝ) - 4) / 2))
          (s * (m : ℝ) ^ (((d : ℝ) - 2) / 2)))))
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI := hprob
  -- The mean-zero and variance hypotheses are the standing ones of the section
  -- and are not used: the concentration lemma centres by the actual mean, and
  -- the bound does not see the variance.
  have _hmean := hmean
  have _hvar := hvar
  have _hvar' := hvar'
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  -- the positive part of the one-site law is integrable
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
  obtain ⟨-, -, ⟨C₁, hC₁, htail⟩, -, -⟩ := Sandpile.External.greenBoundsHigh d hd
  obtain ⟨c₀, C₀, hc₀, hC₀, hconc⟩ := Sandpile.Frozen.weighted_exp_concentration.2.1 θ₀ K₀ hθ₀
  refine ⟨c₀ / C₁, C₀, div_pos hc₀ hC₁, hC₀, ?_⟩
  intro m hm n s hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- With no toppling the smoothed odometer is identically zero.
    have hI : (∫ ζ', Sandpile.odometerOf ζ' 0 0 ∂(LatticeProb.iidLaw d ν)) = 0 := by
      simp [Sandpile.odometerOf]
    have hzero : ∀ ζ : Sandpile.Site d → ℝ,
        (Sandpile.avg^[m] fun x => Sandpile.odometerOf ζ 0 x -
          ∫ ζ', Sandpile.odometerOf ζ' 0 0 ∂(LatticeProb.iidLaw d ν)) 0 = 0 := by
      intro ζ
      rw [Sandpile.avg_iterate_sub_const hd1 m _ _ 0, hI, sub_zero]
      have hfun : Sandpile.odometerOf ζ 0 = fun _ : Sandpile.Site d => (0 : ℝ) := rfl
      rw [hfun, Sandpile.avg_iterate_zero]
    have hempty : {ζ : Sandpile.Site d → ℝ |
        (Sandpile.avg^[m] fun x => Sandpile.odometerOf ζ 0 x -
          ∫ ζ', Sandpile.odometerOf ζ' 0 0 ∂(LatticeProb.iidLaw d ν)) 0 ≤ -s} = ∅ := by
      ext ζ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le, hzero ζ]
      linarith
    rw [hempty]
    simp
  · obtain ⟨htail1, htail2, htail3⟩ := htail m hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hsummable : ∀ y : Sandpile.Site d,
        Summable fun j : {j : ℕ // m ≤ j} => Sandpile.heatKernel d (j : ℕ) 0 y :=
      fun y => (htail1 y).1
    have hinf : ∀ y : Sandpile.Site d,
        Sandpile.smoothedCoeff d m n 0 y ≤ C₁ * (m : ℝ) ^ (((2 : ℝ) - d) / 2) :=
      fun y => le_trans (Sandpile.smoothedCoeff_le_tailKernel m n y (hsummable y)) (htail1 y).2
    have hl2 : ∑ i : Fin (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)).card,
        Sandpile.smoothedCoeff d m n 0
            (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i) ^ 2
          ≤ C₁ * (m : ℝ) ^ (((4 : ℝ) - d) / 2) :=
      le_trans (Sandpile.sum_smoothedCoeff_sq_le m n hsummable htail2) htail3
    obtain ⟨i₀, hi₀⟩ := Sandpile.exists_smoothedCoeff_ne_zero (d := d) hd1 m n hn
    haveI : Nonempty (Fin (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)).card) := ⟨i₀⟩
    have hi₀pos : 0 < Sandpile.smoothedCoeff d m n 0
        (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i₀) :=
      lt_of_le_of_ne (Sandpile.smoothedCoeff_nonneg m n 0 _) (Ne.symm hi₀)
    -- the two norms of the coefficient vector
    have hsumnn : (0 : ℝ) ≤ ∑ i : Fin (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)).card,
        Sandpile.smoothedCoeff d m n 0
          (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hTwo : Sandpile.lTwoNorm (fun i =>
        Sandpile.smoothedCoeff d m n 0
          (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i)) ^ 2
        = ∑ i, Sandpile.smoothedCoeff d m n 0
            (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i) ^ 2 := by
      rw [Sandpile.lTwoNorm, Real.sq_sqrt hsumnn]
    have hTwoPos : 0 < Sandpile.lTwoNorm (fun i =>
        Sandpile.smoothedCoeff d m n 0
          (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i)) ^ 2 := by
      rw [hTwo]
      refine lt_of_lt_of_le (pow_pos hi₀pos 2) ?_
      exact Finset.single_le_sum
        (f := fun i : Fin (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)).card =>
          Sandpile.smoothedCoeff d m n 0
            (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
    have hInfLe : Sandpile.lInfNorm (fun i =>
        Sandpile.smoothedCoeff d m n 0
          (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i))
        ≤ C₁ * (m : ℝ) ^ (((2 : ℝ) - d) / 2) :=
      ciSup_le fun i => hinf _
    have hInfPos : 0 < Sandpile.lInfNorm (fun i =>
        Sandpile.smoothedCoeff d m n 0
          (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i)) :=
      lt_of_lt_of_le hi₀pos
        (le_ciSup (f := fun i : Fin (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)).card =>
            Sandpile.smoothedCoeff d m n 0
              (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i))
          (Finite.bddAbove_range _) i₀)
    -- the concentration bound in the box coordinates
    have hkey := hconc (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)).card ν hprob
      hexpint hexp
      (Sandpile.scenerySmoothed (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) m n 0)
      (Sandpile.measurable_scenerySmoothed _ m n 0)
      (fun i => Sandpile.smoothedCoeff d m n 0
        (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i))
      (fun i => Sandpile.smoothedCoeff_nonneg m n 0 _) ⟨i₀, hi₀⟩
      (fun ξ i y => Sandpile.abs_scenerySmoothed_update_le _ m n 0 ξ i y) s (by linarith)
    -- transport the event to the box coordinates
    have hpickmp := LatticeProb.measurePreserving_pick _ ν
      (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)))
      (Sandpile.siteEnum_injective _)
    have hmean' : (∫ η, Sandpile.scenerySmoothed
          (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) m n 0 η
          ∂(Measure.pi fun _ : Fin (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)).card => ν))
        = ∫ ζ', Sandpile.odometerOf ζ' n 0 ∂(LatticeProb.iidLaw d ν) := by
      rw [← Sandpile.integral_pick ν _ (Sandpile.siteEnum_injective _) _
        (Sandpile.measurable_scenerySmoothed _ m n 0).aestronglyMeasurable,
        integral_congr_ae (Filter.Eventually.of_forall fun ζ =>
          Sandpile.scenerySmoothed_pick (subset_refl _) ζ)]
      exact Sandpile.integral_avg_odometerOf hd1 ν hpos m n 0
    have hmeasset : MeasurableSet {ξ : Fin (Sandpile.boxFinset
        (0 : Sandpile.Site d) (m + n)).card → ℝ | s ≤ |Sandpile.scenerySmoothed
          (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) m n 0 ξ -
        ∫ η, Sandpile.scenerySmoothed
          (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) m n 0 η
          ∂(Measure.pi fun _ => ν)|} :=
      measurableSet_le measurable_const
        (((Sandpile.measurable_scenerySmoothed _ m n 0).sub measurable_const).abs)
    have hsubset : {ζ : Sandpile.Site d → ℝ |
        (Sandpile.avg^[m] fun x => Sandpile.odometerOf ζ n x -
          ∫ ζ', Sandpile.odometerOf ζ' n 0 ∂(LatticeProb.iidLaw d ν)) 0 ≤ -s}
        ⊆ (fun ζ : Sandpile.Site d → ℝ => fun i =>
              ζ (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i)) ⁻¹'
          {ξ | s ≤ |Sandpile.scenerySmoothed
              (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) m n 0 ξ -
            ∫ η, Sandpile.scenerySmoothed
              (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) m n 0 η
              ∂(Measure.pi fun _ => ν)|} := by
      intro ζ hζ
      simp only [Set.mem_setOf_eq] at hζ
      rw [Sandpile.avg_iterate_sub_const hd1 m _ _ 0] at hζ
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [hmean', Sandpile.scenerySmoothed_pick (subset_refl _) ζ]
      refine le_trans ?_ (neg_le_abs _)
      linarith
    -- the exponent comparison
    have hpow4 : (m : ℝ) ^ (((d : ℝ) - 4) / 2) = ((m : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2))⁻¹ := by
      rw [show ((d : ℝ) - 4) / 2 = -(((4 : ℝ) - (d : ℝ)) / 2) by ring, Real.rpow_neg hm0.le]
    have hpow2 : (m : ℝ) ^ (((d : ℝ) - 2) / 2) = ((m : ℝ) ^ (((2 : ℝ) - (d : ℝ)) / 2))⁻¹ := by
      rw [show ((d : ℝ) - 2) / 2 = -(((2 : ℝ) - (d : ℝ)) / 2) by ring, Real.rpow_neg hm0.le]
    have hr4 : (0 : ℝ) < (m : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2) := Real.rpow_pos_of_pos hm0 _
    have hr2 : (0 : ℝ) < (m : ℝ) ^ (((2 : ℝ) - (d : ℝ)) / 2) := Real.rpow_pos_of_pos hm0 _
    have hmin : (c₀ / C₁) * min (s ^ 2 * (m : ℝ) ^ (((d : ℝ) - 4) / 2))
          (s * (m : ℝ) ^ (((d : ℝ) - 2) / 2))
        ≤ c₀ * min (s ^ 2 / Sandpile.lTwoNorm (fun i =>
              Sandpile.smoothedCoeff d m n 0
                (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i)) ^ 2)
            (s / Sandpile.lInfNorm (fun i =>
              Sandpile.smoothedCoeff d m n 0
                (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i))) := by
      rw [mul_min_of_nonneg _ _ (le_of_lt (div_pos hc₀ hC₁)),
        mul_min_of_nonneg _ _ hc₀.le]
      refine min_le_min ?_ ?_
      · have h1 : (c₀ / C₁) * (s ^ 2 * (m : ℝ) ^ (((d : ℝ) - 4) / 2))
            = c₀ * (s ^ 2 / (C₁ * (m : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2))) := by
          rw [hpow4]; field_simp
        rw [h1]
        refine mul_le_mul_of_nonneg_left ?_ hc₀.le
        gcongr
        rw [hTwo]; exact hl2
      · have h2 : (c₀ / C₁) * (s * (m : ℝ) ^ (((d : ℝ) - 2) / 2))
            = c₀ * (s / (C₁ * (m : ℝ) ^ (((2 : ℝ) - (d : ℝ)) / 2))) := by
          rw [hpow2]; field_simp
        rw [h2]
        refine mul_le_mul_of_nonneg_left ?_ hc₀.le
        gcongr
    calc LatticeProb.iidLaw d ν {ζ : Sandpile.Site d → ℝ |
          (Sandpile.avg^[m] fun x => Sandpile.odometerOf ζ n x -
            ∫ ζ', Sandpile.odometerOf ζ' n 0 ∂(LatticeProb.iidLaw d ν)) 0 ≤ -s}
        ≤ LatticeProb.iidLaw d ν ((fun ζ : Sandpile.Site d → ℝ => fun i =>
              ζ (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i)) ⁻¹'
            {ξ | s ≤ |Sandpile.scenerySmoothed
                (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) m n 0 ξ -
              ∫ η, Sandpile.scenerySmoothed
                (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) m n 0 η
                ∂(Measure.pi fun _ => ν)|}) := measure_mono hsubset
      _ = (Measure.pi fun _ : Fin (Sandpile.boxFinset
            (0 : Sandpile.Site d) (m + n)).card => ν)
            {ξ | s ≤ |Sandpile.scenerySmoothed
                (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) m n 0 ξ -
              ∫ η, Sandpile.scenerySmoothed
                (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) m n 0 η
                ∂(Measure.pi fun _ => ν)|} :=
          hpickmp.measure_preimage hmeasset.nullMeasurableSet
      _ ≤ ENNReal.ofReal (C₀ * Real.exp (-(c₀ * min (s ^ 2 /
            Sandpile.lTwoNorm (fun i => Sandpile.smoothedCoeff d m n 0
              (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i)) ^ 2)
            (s / Sandpile.lInfNorm (fun i => Sandpile.smoothedCoeff d m n 0
              (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (m + n)) i)))))) :=
          hkey
      _ ≤ ENNReal.ofReal (C₀ * Real.exp (-(c₀ / C₁ *
            min (s ^ 2 * (m : ℝ) ^ (((d : ℝ) - 4) / 2))
              (s * (m : ℝ) ^ (((d : ℝ) - 2) / 2))))) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC₀.le)
          exact Real.exp_le_exp.mpr (by linarith)
