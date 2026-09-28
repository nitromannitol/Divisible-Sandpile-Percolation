import LatticeProb.Prob.WeightedConc
import Sandpile.Support.Norms
import Sandpile.Support.ExitAverage

/-! # Exit-Averaged Concentration in Dimension Four

The concentration inequality for an exit-averaged localized odometer in
dimension four.  The influence square sum is uniformly bounded and its
largest coefficient is of order r⁻², giving Gaussian and exponential regimes.
-/

open LatticeProb

open MeasureTheory

namespace Sandpile

/-- A uniform square-sum bound and a small largest influence give the two
concentration regimes without any dependence on the number of coordinates. -/
theorem weighted_tail_of_norm_bounds (θ K B : ℝ) (hθ : 0 < θ) (hB : 0 < B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ * |z|)) ν → (∫ z, Real.exp (θ * |z|) ∂ν) ≤ K →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F → ∀ ℓ : Fin N → ℝ,
        (∀ i, 0 ≤ ℓ i) →
        (∀ ξ i v, |F ξ - F (Function.update ξ i v)| ≤ ℓ i * |ξ i - v|) →
        (∑ i, ℓ i ^ 2) ≤ B → ∀ H : ℝ, 0 < H → (∀ i, ℓ i ≤ B / H) →
        ∀ s : ℝ, 0 ≤ s →
          (Measure.pi fun _ : Fin N => ν)
              {ξ | s < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|} ≤
            ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2) (s * H)))) := by
  obtain ⟨c₀, C, hc₀, hC, htail⟩ := weighted_exp_conc_tail θ K hθ
  refine ⟨c₀ / B, C, div_pos hc₀ hB, hC, ?_⟩
  intro N ν hν hexp hK F hFm ℓ hℓ hLip hsum H hH hmax s hs
  haveI := hν
  classical
  by_cases hne : ∃ i, ℓ i ≠ 0
  · haveI : Nonempty (Fin N) := ⟨hne.choose⟩
    have hInf : lInfNorm ℓ ≤ B / H := ciSup_le fun i => hmax i
    have hInf0 : 0 < lInfNorm ℓ := lInfNorm_pos ℓ hℓ hne
    have hTwo0 : 0 < lTwoNorm ℓ ^ 2 := sq_pos_of_pos (lTwoNorm_pos ℓ hℓ hne)
    have hTwo : lTwoNorm ℓ ^ 2 ≤ B := by rwa [lTwoNorm_sq]
    have hmin : (c₀ / B) * min (s ^ 2) (s * H) ≤
        c₀ * min (s ^ 2 / lTwoNorm ℓ ^ 2) (s / lInfNorm ℓ) := by
      rw [mul_min_of_nonneg _ _ (div_pos hc₀ hB).le, mul_min_of_nonneg _ _ hc₀.le]
      refine min_le_min ?_ ?_
      · rw [show c₀ / B * s ^ 2 = c₀ * (s ^ 2 / B) by ring]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (sq_nonneg s) hTwo0 hTwo) hc₀.le
      · rw [show c₀ / B * (s * H) = c₀ * (s / (B / H)) by field_simp]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hs hInf0 hInf) hc₀.le
    have ht := htail N ν hν hexp hK F hFm ℓ hℓ hne hLip s hs
    refine (measure_mono
      (fun ξ (hξ : s < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|) => hξ.le)).trans
      (ht.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC.le
  · have hz : ∀ i, ℓ i = 0 := by simpa using hne
    have hc : ∀ ξ, F ξ = F 0 := by
      intro ξ
      have h := abs_sub_le_sum_lip F ℓ hLip ξ 0
      simp only [hz, zero_mul, Finset.sum_const_zero] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    have hm : (∫ ξ, F ξ ∂(Measure.pi fun _ : Fin N => ν)) = F 0 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hc), integral_const]
      simp
    have he : {ξ : Fin N → ℝ | s < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ξ hξ
      change s < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)| at hξ
      rw [hc ξ, hm, sub_self, abs_zero] at hξ
      exact hs.not_gt hξ
    rw [he, measure_empty]
    exact bot_le

variable {d : ℕ}

/-- `localizedExitAverage D N E m ζ x` repackaged as a function of the finitely many
coordinates `ξ` of the scenery on the box of radius `N + m` around `x`, via `siteExtend`, so
that it can be fed to the finite-coordinate concentration inequality
`weighted_tail_of_norm_bounds`. -/
noncomputable def boxExitAverage (D : Set (Site d)) (N : ℕ) (E : Site d → Set (Site d))
    (m : ℕ) (x : Site d) (ξ : Fin (boxFinset x (N + m)).card → ℝ) : ℝ :=
  localizedExitAverage D N E m (siteExtend (boxFinset x (N + m)) ξ) x

/-- `boxExitAverage D N E m x` is measurable in its finite coordinate vector, since
`localizedExitAverage` is measurable in the scenery and `siteExtend` is measurable. -/
theorem measurable_boxExitAverage (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) (x : Site d) : Measurable (boxExitAverage D N E m x) :=
  (measurable_localizedExitAverage hd D N E m x).comp (measurable_siteExtend _)

/-- `boxExitAverage` evaluated at the coordinates of a scenery `ζ` picked out on the box
recovers `localizedExitAverage D N E m ζ x`, since `localizedExitAverage` only reads `ζ` on
that box. -/
theorem boxExitAverage_pick (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) (x : Site d) (ζ : Site d → ℝ) :
    boxExitAverage D N E m x (fun i => ζ (siteEnum (boxFinset x (N + m)) i)) =
      localizedExitAverage D N E m ζ x :=
  localizedExitAverage_congr_box hd D N E m x _ ζ (fun _ hz => siteExtend_siteEnum _ ζ hz)

/-- `boxExitAverage`'s coordinate Lipschitz bound: `exitInfluence D N m x` at the site enumerated
by `i` bounds the effect of changing that coordinate, transported from
`abs_localizedExitAverage_update_le` through `siteExtend`. -/
theorem abs_boxExitAverage_update_le (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) (x : Site d)
    (ξ : Fin (boxFinset x (N + m)).card → ℝ) (i : Fin (boxFinset x (N + m)).card) (v : ℝ) :
    |boxExitAverage D N E m x ξ - boxExitAverage D N E m x (Function.update ξ i v)| ≤
      exitInfluence D N m x (siteEnum (boxFinset x (N + m)) i) * |ξ i - v| := by
  have h := abs_localizedExitAverage_update_le hd D N E m
    (siteExtend (boxFinset x (N + m)) ξ) x (siteEnum (boxFinset x (N + m)) i) v
  have hv : siteExtend (boxFinset x (N + m)) ξ (siteEnum (boxFinset x (N + m)) i) = ξ i := by
    simp [siteExtend, siteEnum]
  simpa only [boxExitAverage, siteExtend_update, hv] using h

/-- The cube exit average satisfies a concentration estimate uniform over the
exit horizon, the continuation domains, and the starting site. -/
theorem exists_cube_exit_concentration (hBallGreen : External.BallGreenBounds)
    (θ K : ℝ) (hθ : 0 < θ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ * |z|)) ν → (∫ z, Real.exp (θ * |z|) ∂ν) ≤ K →
        ∀ r : ℕ, 2 ≤ r → ∀ N : ℕ, ∀ E : Site 4 → Set (Site 4), ∀ x : Site 4,
        ∀ a : ℝ, 0 ≤ a →
          LatticeProb.iidLaw 4 ν {ζ | a < |localizedExitAverage
            {w : Site 4 | ∀ i, |(w i : ℝ) - (x i : ℝ)| ≤ r} N E (r ^ 2) ζ x -
            ∫ η, localizedExitAverage {w : Site 4 | ∀ i, |(w i : ℝ) - (x i : ℝ)| ≤ r}
              N E (r ^ 2) η x ∂LatticeProb.iidLaw 4 ν|} ≤
            ENNReal.ofReal (C * Real.exp (-(c * min (a ^ 2) (a * (r : ℝ) ^ 2)))) := by
  obtain ⟨B, hB, hGreen⟩ := exists_cube_exit_green_bound hBallGreen
  obtain ⟨c, C, hc, hC, htail⟩ := weighted_tail_of_norm_bounds θ K B hθ hB
  refine ⟨c, C, hc, hC, ?_⟩
  intro ν hν hexp hK r hr N E x a ha
  haveI := hν
  classical
  set D : Set (Site 4) := {w | ∀ i, |(w i : ℝ) - (x i : ℝ)| ≤ r}
  set S := boxFinset x (N + r ^ 2)
  set F := boxExitAverage D N E (r ^ 2) x
  set ℓ : Fin S.card → ℝ := fun i => exitInfluence D N (r ^ 2) x (siteEnum S i)
  have hℓ : ∀ i, 0 ≤ ℓ i := fun i => exitInfluence_nonneg D N (r ^ 2) x _
  have hmax : ∀ i, ℓ i ≤ B / (r : ℝ) ^ 2 := fun i =>
    (exitInfluence_le_green_exit (by norm_num) D N (r ^ 2) x _).trans (hGreen r hr x _)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hsum : (∑ i, ℓ i) ≤ (r : ℝ) ^ 2 := by
    change (∑ i : Fin S.card, exitInfluence D N (r ^ 2) x (siteEnum S i)) ≤ _
    rw [sum_siteEnum S (fun y => exitInfluence D N (r ^ 2) x y)]
    have ht := finset_sum_exitInfluence_le (by norm_num) D N (r ^ 2) x S
    exact ht.trans_eq (by norm_cast)
  have hsquare : (∑ i, ℓ i ^ 2) ≤ B := by
    calc (∑ i, ℓ i ^ 2) ≤ ∑ i, (B / (r : ℝ) ^ 2) * ℓ i := by
          refine Finset.sum_le_sum fun i _ => ?_
          nlinarith [mul_le_mul_of_nonneg_right (hmax i) (hℓ i)]
      _ = (B / (r : ℝ) ^ 2) * ∑ i, ℓ i := (Finset.mul_sum _ _ _).symm
      _ ≤ (B / (r : ℝ) ^ 2) * (r : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = B := by field_simp
  have hFm : Measurable F := measurable_boxExitAverage (by norm_num) D N E (r ^ 2) x
  have hLip : ∀ ξ i v, |F ξ - F (Function.update ξ i v)| ≤ ℓ i * |ξ i - v| :=
    abs_boxExitAverage_update_le (by norm_num) D N E (r ^ 2) x
  have ht := htail S.card ν hν hexp hK F hFm ℓ hℓ hLip hsquare
    ((r : ℝ) ^ 2) (by positivity) hmax a ha
  have hm : (∫ ζ, localizedExitAverage D N E (r ^ 2) ζ x ∂LatticeProb.iidLaw 4 ν) =
      ∫ ξ, F ξ ∂(Measure.pi fun _ : Fin S.card => ν) := by
    have hp := integral_pick ν (siteEnum S) (siteEnum_injective S) F hFm.aestronglyMeasurable
    simpa only [F, S, boxExitAverage_pick (d := 4) (by norm_num)] using hp
  have he : {ζ : Site 4 → ℝ | a < |localizedExitAverage D N E (r ^ 2) ζ x -
      ∫ η, localizedExitAverage D N E (r ^ 2) η x ∂LatticeProb.iidLaw 4 ν|} =
      (fun ζ : Site 4 → ℝ => fun i => ζ (siteEnum S i)) ⁻¹'
        {ξ | a < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin S.card => ν)|} := by
    ext ζ
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hm, F, S,
      boxExitAverage_pick (d := 4) (by norm_num)]
  have hme : MeasurableSet
      {ξ : Fin S.card → ℝ | a < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin S.card => ν)|} :=
    measurableSet_lt measurable_const (hFm.sub measurable_const).abs
  change LatticeProb.iidLaw 4 ν {ζ | a < |localizedExitAverage D N E (r ^ 2) ζ x -
    ∫ η, localizedExitAverage D N E (r ^ 2) η x ∂LatticeProb.iidLaw 4 ν|} ≤ _
  rw [he, (LatticeProb.measurePreserving_pick _ ν (siteEnum S)
    (siteEnum_injective S)).measure_preimage hme.nullMeasurableSet]
  exact ht

end Sandpile
