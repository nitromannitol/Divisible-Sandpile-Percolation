/-
The mean profile of the odometer killed at the origin. Finite survival
probabilities bound an approximately subharmonic function from above. The
localization comparison supplies the lower bound and identifies the limit.
-/
import Sandpile.Support.OriginKilled
import Sandpile.Support.HitProb
import Sandpile.Support.RefinedIncrement
import Sandpile.Frozen.DGT4MeanLower
import LatticeProb.Prob.Coordinate

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

theorem integrable_avg_field {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → Site d → ℝ} (hint : ∀ x, Integrable (fun a => F a x) μ) (x : Site d) :
    Integrable (fun a => avg (F a) x) μ := by
  unfold avg LatticeProb.walkOp LatticeProb.nbrSum
  exact (integrable_finsetSum _ fun i _ => (hint _).add (hint _)).div_const _

theorem integral_avg_field {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → Site d → ℝ} (hint : ∀ x, Integrable (fun a => F a x) μ) (x : Site d) :
    (∫ a, avg (F a) x ∂μ) = avg (fun y => ∫ a, F a y ∂μ) x := by
  unfold avg LatticeProb.walkOp LatticeProb.nbrSum
  rw [integral_div, integral_finsetSum Finset.univ (f := fun (i : Fin d) a => F a (x + unit i) + F a (x - unit i)) (fun (i : Fin d) _ => (hint (x + unit i)).add (hint (x - unit i)))]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_add (hint _) (hint _)

noncomputable def originMean (ν : Measure ℝ) (n : ℕ) (x : Site d) : ℝ :=
  ∫ ζ, originOdometer ζ n x ∂LatticeProb.iidLaw d ν

noncomputable def fullMean (d : ℕ) (ν : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ ζ, odometerOf ζ n 0 ∂LatticeProb.iidLaw d ν

theorem originMean_zero (ν : Measure ℝ) (n : ℕ) : originMean ν n (0 : Site d) = 0 := by
  simp only [originMean, originOdometer_zero, integral_zero]

theorem originMean_le_fullMean (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (n : ℕ) (x : Site d) :
    originMean ν n x ≤ fullMean d ν n := by
  rw [fullMean, ← integral_odometerOf_eq d ν n x]
  exact integral_mono (integrable_localizedOdometer hd ν hpos _ n x)
    (integrable_odometerOf d ν hpos n x) fun ζ => localizedOdometer_le_full hd _ ζ n x

theorem originMean_le_avg_add (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (n : ℕ) {x : Site d} (hx : x ≠ 0) :
    originMean ν n x ≤ avg (originMean (d := d) ν n) x + ∫ z, max z 0 ∂ν := by
  have hi := fun y => integrable_localizedOdometer hd ν hpos {z : Site d | z ≠ 0} n y
  have hic := integrable_coord_pos d ν hpos x
  have hp : ∀ ζ : Site d → ℝ, originOdometer ζ n x ≤
      avg (originOdometer ζ n) x + max (ζ x) 0 := by
    intro ζ
    have ha := avg_nonneg (fun y => localizedOdometer_nonneg hd {z : Site d | z ≠ 0} ζ n y) x
    refine (localizedOdometer_le_succ hd _ ζ n x).trans ?_
    rw [localizedOdometer_succ' hd _ ζ n x hx]
    refine max_le (by positivity) ?_
    linarith [le_max_left (ζ x) 0]
  have h := integral_mono (hi x) ((integrable_avg_field hi x).add hic) hp
  change originMean ν n x ≤ ∫ ζ, avg (originOdometer ζ n) x + max (ζ x) 0 ∂LatticeProb.iidLaw d ν at h
  rw [integral_add (integrable_avg_field hi x) hic,
    integral_avg_field hi x] at h
  have hcoord : (∫ ζ, max (ζ x) 0 ∂LatticeProb.iidLaw d ν) = ∫ z, max z 0 ∂ν :=
    LatticeProb.integral_eval (μ := fun _ : Site d => ν) x (fun z => max z 0) hpos.aestronglyMeasurable
  rw [hcoord] at h
  exact h

/-- A bounded function vanishing at the origin and approximately subharmonic
is bounded by finite survival, with a linear accumulation of the error. -/
theorem le_survival_add_error (hd : 1 ≤ d) {f : Site d → ℝ} {M C : ℝ}
    (hC : 0 ≤ C) (hf0 : f 0 = 0) (hfM : ∀ x, f x ≤ M)
    (hf : ∀ x, x ≠ 0 → f x ≤ avg f x + C) : ∀ k : ℕ, ∀ x : Site d,
      f x ≤ (1 - LatticeProb.srwHitBy d k x) * M + (k : ℝ) * C := by
  intro k
  induction k with
  | zero =>
    intro x
    by_cases hx : x = 0
    · subst hx
      simp [LatticeProb.srwHitBy_zero, hf0]
    · simpa [LatticeProb.srwHitBy_zero, hx] using hfM x
  | succ k ih =>
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [hf0, LatticeProb.srwHitBy_succ_origin]
      simp only [sub_self, zero_mul, zero_add]
      exact mul_nonneg (Nat.cast_nonneg _) hC
    · have h := (hf x hx).trans (add_le_add (avg_mono_le ih x) le_rfl)
      have hav : avg (fun y => (1 - LatticeProb.srwHitBy d k y) * M + (k : ℝ) * C) x =
          (1 - LatticeProb.srwHitBy d (k + 1) x) * M + (k : ℝ) * C := by
        rw [avg_add]
        change LatticeProb.walkOp (fun y => (1 - LatticeProb.srwHitBy d k y) * M) x +
          LatticeProb.walkOp (fun _ => (k : ℝ) * C) x = _
        rw [LatticeProb.walkOp_mul_const, LatticeProb.walkOp_sub,
          LatticeProb.walkOp_const hd, LatticeProb.walkOp_const hd,
          ← LatticeProb.srwHitBy_succ_of_ne hx k]
      rw [hav] at h
      push_cast
      linarith

theorem originMean_survival_upper (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (n k : ℕ) (x : Site d) :
    originMean ν n x ≤ (1 - LatticeProb.srwHitBy d k x) * fullMean d ν n +
      (k : ℝ) * ∫ z, max z 0 ∂ν :=
  le_survival_add_error hd (integral_nonneg fun _ => le_max_right _ _)
    (originMean_zero ν n) (originMean_le_fullMean hd ν hpos n)
    (fun _ hx => originMean_le_avg_add hd ν hpos n hx) k x

theorem originMean_survival_lower (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (n : ℕ) (x : Site d) :
    (1 - LatticeProb.srwHitProb d x) * fullMean d ν n ≤ originMean ν n x := by
  haveI : NeZero d := ⟨by omega⟩
  have hM : 0 ≤ fullMean d ν n := integral_nonneg fun ζ => odometerOf_nonneg ζ n 0
  by_cases hx : x = 0
  · subst hx
    have hhit : LatticeProb.srwHitProb d (0 : Site d) = 1 := by
      rw [LatticeProb.srwHitProb, tsum_eq_single 0]
      · simp [LatticeProb.srwFirstHit_zero]
      · intro k hk
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        exact LatticeProb.srwFirstHit_succ_origin j
    rw [hhit, originMean_zero]
    ring_nf
    exact le_rfl
  · have h := (mean_localization_bound hd ν hpos {z : Site d | z ≠ 0} n x hx).2
    have he : {X : ℕ → Site d | exitNat {z : Site d | z ≠ 0} n X ≤ n} ⊆
        LatticeProb.hitOrigin d := by
      intro X hX
      obtain ⟨j, hj, he⟩ := exitNat_le_iff.mp hX
      exact ⟨j, by simpa only [Set.mem_setOf_eq, not_not] using he⟩
    have hprob := ENNReal.toReal_mono (measure_ne_top (walkLaw d x) _)
      (measure_mono he : walkLaw d x _ ≤ walkLaw d x _)
    change (walkLaw d x _).toReal ≤ (LatticeProb.siteWalkLaw d x (LatticeProb.hitOrigin d)).toReal at hprob
    rw [LatticeProb.siteWalkLaw_hitOrigin hd x,
      ENNReal.toReal_ofReal (LatticeProb.srwHitProb_nonneg x)] at hprob
    have hb := mul_le_mul_of_nonneg_right hprob hM
    change fullMean d ν n - originMean ν n x ≤
      ((walkLaw d x) {X : ℕ → Site d | exitNat {z : Site d | z ≠ 0} n X ≤ n}).toReal * fullMean d ν n at h
    linarith

theorem originMean_profile_limit (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν)
    (hdiv : Tendsto (fullMean d ν) atTop atTop) (x : Site d) :
    Tendsto (fun n => originMean ν n x / fullMean d ν n) atTop
      (𝓝 (1 - LatticeProb.srwHitProb d x)) := by
  have hM := hdiv.eventually_gt_atTop 0
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hM] with n hn
    have hb := originMean_survival_lower hd ν hpos n x
    exact ha.trans_le ((le_div_iff₀ hn).mpr hb)
  · intro b hb
    have hhit : Tendsto (fun k => LatticeProb.srwHitBy d k x) atTop
        (𝓝 (LatticeProb.srwHitProb d x)) :=
      (LatticeProb.summable_srwFirstHit (by omega) x).hasSum.tendsto_sum_nat.comp
        (Filter.tendsto_add_atTop_nat 1)
    have hsurv := (tendsto_const_nhds (x := (1 : ℝ))).sub hhit
    obtain ⟨k, hk⟩ := (hsurv.eventually_lt_const hb).exists
    have herr : Tendsto (fun n => (k : ℝ) * (∫ z, max z 0 ∂ν) / fullMean d ν n)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop hdiv
    have hupper : Tendsto (fun n => (1 - LatticeProb.srwHitBy d k x) +
        (k : ℝ) * (∫ z, max z 0 ∂ν) / fullMean d ν n) atTop
        (𝓝 (1 - LatticeProb.srwHitBy d k x)) := by
      simpa only [add_zero] using tendsto_const_nhds.add herr
    filter_upwards [hM, hupper.eventually_lt_const hk] with n hn hnb
    apply lt_of_le_of_lt _ hnb
    have h := div_le_div_of_nonneg_right (originMean_survival_upper hd ν hpos n k x) hn.le
    calc originMean ν n x / fullMean d ν n
        ≤ ((1 - LatticeProb.srwHitBy d k x) * fullMean d ν n +
          (k : ℝ) * ∫ z, max z 0 ∂ν) / fullMean d ν n := h
      _ = (1 - LatticeProb.srwHitBy d k x) + (k : ℝ) * (∫ z, max z 0 ∂ν) / fullMean d ν n := by
        rw [add_div, mul_div_cancel_right₀ _ hn.ne']

theorem avg_originMean_profile_limit (hd : 3 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν)
    (hdiv : Tendsto (fullMean d ν) atTop atTop) :
    Tendsto (fun n => avg (originMean (d := d) ν n) 0 / fullMean d ν n) atTop
      (𝓝 (1 / green d 0 0)) := by
  have hd1 : 1 ≤ d := by omega
  have hcoord := originMean_profile_limit hd1 ν hpos hdiv
  have hav : Tendsto (fun n => avg (fun x : Site d => originMean ν n x / fullMean d ν n) 0) atTop
      (𝓝 (avg (fun x => 1 - LatticeProb.srwHitProb d x) 0)) := by
    unfold avg LatticeProb.walkOp LatticeProb.nbrSum
    exact (tendsto_finsetSum Finset.univ (fun i _ => (hcoord _).add (hcoord _))).div_const _
  have hf (n : ℕ) : avg (fun x : Site d => originMean ν n x / fullMean d ν n) 0 =
      avg (originMean (d := d) ν n) 0 / fullMean d ν n :=
    LatticeProb.walkOp_div_const _ _ _
  have hl : avg (fun x : Site d => 1 - LatticeProb.srwHitProb d x) 0 = 1 / green d 0 0 := by
    change LatticeProb.walkOp (fun x : Site d => 1 - LatticeProb.srwHitProb d x) 0 = _
    rw [LatticeProb.walkOp_sub, LatticeProb.walkOp_const hd1]
    have hr : LatticeProb.walkOp (LatticeProb.srwHitProb d) 0 = 1 - 1 / green d 0 0 := by
      simpa [LatticeProb.walkOp, LatticeProb.nbrSum] using External.Sec16.return_probability d hd
    rw [hr]
    ring
  simpa only [hf, hl] using hav

theorem origin_frozen_mean_ratio (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0) (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z) :
    Tendsto (fun n => green d 0 0 * (∫ σ, avg (originOdometer (scenery d σ) n) 0
        ∂centeredMassLaw d ν) / meanOdometer (centeredMassLaw d ν) n) atTop (𝓝 1) := by
  have hd1 : 1 ≤ d := by omega
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    hint.abs.mono' (by fun_prop) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
      exact max_le (le_abs_self z) (abs_nonneg z))
  obtain ⟨c, hc, t₀, hl⟩ := (Sandpile.Frozen.dgt4_mean_lower d hd).1 ν inferInstance hint hmean hnondeg
  have hmdiv := tendsto_atTop_of_log_lower hc (by positivity : (0 : ℝ) < 2 / d) hl
  have hdiv : Tendsto (fullMean d ν) atTop atTop := by
    change Tendsto (fun n => meanOdometer (centeredMassLaw d ν) n) atTop atTop at hmdiv
    change Tendsto (fun n => fullMean d ν n) atTop atTop
    simpa only [meanOdometer_eq d ν hd1, fullMean] using hmdiv
  have h := (avg_originMean_profile_limit (by omega) ν hpos hdiv).const_mul (green d 0 0)
  have hG : green d 0 0 ≠ 0 := by
    rw [External.Sec16.green_eq, sub_zero]
    exact ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le
      (LatticeProb.one_le_srwGreenInf_origin (by omega)))
  have he (n : ℕ) : (∫ σ, avg (originOdometer (scenery d σ) n) 0 ∂centeredMassLaw d ν) =
      avg (originMean (d := d) ν n) 0 := by
    rw [integral_scenery d ν hd1 (F := fun ζ => avg (originOdometer ζ n) 0)
      (measurable_avg_originOdometer hd1 n).aestronglyMeasurable,
      integral_avg_field (fun x => integrable_localizedOdometer hd1 ν hpos _ n x) 0]
    rfl
  simpa only [he, meanOdometer_eq d ν hd1, fullMean, ← mul_div_assoc, one_div, mul_inv_cancel₀ hG] using h

end Sandpile
