import Sandpile.Frozen.WeightedExpConcentration
import Sandpile.Frozen.DifferenceRepresentation
import Sandpile.External.BPSHProved
import Sandpile.Support.EventBridge
import Sandpile.Support.CrudeIncrement
import Sandpile.Support.PointwiseConc
import Sandpile.Support.Stopped
import Sandpile.Support.IncrementBall
import Sandpile.External.VarianceScale

/-!
# The upper tail of `u_t - V_t` in dimension four

`lem:d4-difference-tail` (`sandpile.tex:3008-3047`) reads the difference through the
optimal-stopping representation, bounds it by the largest positive part of `-V_r(y)` over the
times and sites the walk can reach, and then unions the sub-exponential tail of a single
membrane value over those `C(t+2)^5` pairs. This file carries the three ingredients: the
membrane as a linear functional of the scenery in a box, with the `\ell^2` and `\ell^\infty`
bounds that `eq:d4-full-window-bounds` gives in dimension four; the pathwise bound on the
optimal-stopping supremum; and the union bound over the reachable pairs.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- The membrane field read as a linear functional of the box coordinates. -/
noncomputable def boxMembrane (t : ℕ) (x : Site d)
    (ξ : Fin (boxFinset x t).card → ℝ) : ℝ :=
  ∑ i, greenTime d t x (boxEnum x t i) * ξ i

/-- `boxMembrane` evaluated at the coordinates of `ζ` picked out by `boxEnum` recovers
`membrane ζ t x`. -/
theorem boxMembrane_pick (t : ℕ) (x : Site d) (ζ : Site d → ℝ) :
    boxMembrane t x (fun i => ζ (boxEnum x t i)) = membrane ζ t x :=
  (membrane_eq_sum_boxEnum t x ζ).symm

/-- `boxMembrane t x` is measurable, being a finite sum of coordinate projections
scaled by `greenTime`. -/
theorem measurable_boxMembrane (t : ℕ) (x : Site d) : Measurable (boxMembrane t x) := by
  unfold boxMembrane
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _

/-- Updating a single coordinate `i` of `ξ` changes `boxMembrane t x ξ` by at most
`greenTime d t x (boxEnum x t i)` times the size of the update: the Lipschitz constant of
`boxMembrane` in each coordinate is its Green-function coefficient. -/
theorem abs_boxMembrane_update_le (t : ℕ) (x : Site d)
    (ξ : Fin (boxFinset x t).card → ℝ) (i : Fin (boxFinset x t).card) (y : ℝ) :
    |boxMembrane t x ξ - boxMembrane t x (Function.update ξ i y)|
      ≤ greenTime d t x (boxEnum x t i) * |ξ i - y| := by
  classical
  have h : boxMembrane t x ξ - boxMembrane t x (Function.update ξ i y)
      = greenTime d t x (boxEnum x t i) * (ξ i - y) := by
    unfold boxMembrane
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · rw [Function.update_self]; ring
    · intro j _ hj
      rw [Function.update_of_ne hj]
      ring
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [h, abs_mul, abs_of_nonneg (greenTime_nonneg t x (boxEnum x t i))]

/-- The membrane field has mean zero under the i.i.d. scenery law: `membrane` is a finite
linear combination of coordinates, each of mean zero, so its integral vanishes. -/
theorem integral_membrane_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0) (t : ℕ) (x : Site d) :
    ∫ ζ, membrane ζ t x ∂(LatticeProb.iidLaw d ν) = 0 := by
  classical
  have hrw : (∫ ζ, membrane ζ t x ∂(LatticeProb.iidLaw d ν))
      = ∫ ζ, (∑ i : Fin (boxFinset x t).card,
          greenTime d t x (boxEnum x t i) * ζ (boxEnum x t i)) ∂(LatticeProb.iidLaw d ν) :=
    integral_congr_ae (Filter.Eventually.of_forall (membrane_eq_sum_boxEnum t x))
  rw [hrw, integral_finsetSum _
    (fun i _ => (integrable_coord ν hint (boxEnum x t i)).const_mul _)]
  simp only [integral_const_mul, integral_coord ν hint, hmean, mul_zero,
    Finset.sum_const_zero]

/-- The box-coordinate transposition of `integral_membrane_zero`: `boxMembrane t x` has mean
zero under the product law, via the coordinate-picking measure isomorphism
`integral_pick`. -/
theorem integral_boxMembrane_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0) (t : ℕ) (x : Site d) :
    ∫ ξ, boxMembrane t x ξ ∂(Measure.pi fun _ : Fin (boxFinset x t).card => ν) = 0 := by
  rw [← integral_pick ν (boxEnum x t) (boxEnum_injective x t) (boxMembrane t x)
    (measurable_boxMembrane t x).aestronglyMeasurable]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ζ => boxMembrane_pick t x ζ)]
  exact integral_membrane_zero ν hint hmean t x

/-- `g_1 = p_0` is the Kronecker delta, hence at most one. -/
theorem greenTime_one_le_one (x y : Site d) : greenTime d 1 x y ≤ 1 := by
  rw [greenTime_succ, greenTime_zero, heatKernel_zero, zero_add]
  split <;> norm_num

/-- `log 3 ≥ 1`, since `e < 3`. -/
theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have he : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h1 : Real.log (Real.exp 1) ≤ Real.log 3 :=
    Real.log_le_log (Real.exp_pos 1) he.le
  rwa [Real.log_exp] at h1

/-- **The two norms of the Green coefficients in dimension four.**  The full
window bounds of `eq:d4-full-window-bounds` give `∑_z g_t(x,z)^2 ≤ C log(t+2)`
and `g_t(x,y) ≤ C` for `t ≥ 2`; the two remaining times are read off `g_0 = 0`
and `g_1 = p_0`. -/
theorem exists_greenTime_norm_bounds_four (hVS : Sandpile.External.VarianceScale) :
    ∃ M : ℝ, 1 ≤ M ∧
      (∀ (t : ℕ) (x : Site 4), (∑' z : Site 4, greenTime 4 t x z ^ 2)
          ≤ M * Real.log ((t : ℝ) + 2)) ∧
      (∀ (t : ℕ) (x y : Site 4), greenTime 4 t x y ≤ M) := by
  classical
  obtain ⟨C, hC, -, hfull⟩ := hVS.2.2
  refine ⟨max C 81, le_trans (by norm_num) (le_max_right _ _), ?_, ?_⟩
  · intro t x
    have hlog0 : (0 : ℝ) ≤ Real.log ((t : ℝ) + 2) := by
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
      linarith
    rcases Nat.lt_or_ge t 2 with hlt | hge
    · interval_cases t
      · have hz : ∀ z : Site 4, greenTime 4 0 x z ^ 2 = 0 := by
          intro z; rw [greenTime_zero]; ring
        rw [tsum_congr hz, tsum_zero]
        positivity
      · have hle : (∑' z : Site 4, greenTime 4 1 x z ^ 2) ≤ 81 := by
          rw [tsum_greenTime_sq_eq_sum]
          calc ∑ z ∈ boxFinset x 1, greenTime 4 1 x z ^ 2
              ≤ ∑ _z ∈ boxFinset x 1, (1 : ℝ) := by
                refine Finset.sum_le_sum fun z _ => ?_
                have h0 := greenTime_nonneg 1 x z
                have h1 := greenTime_one_le_one (d := 4) x z
                nlinarith
            _ = ((boxFinset x 1).card : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            _ = 81 := by rw [card_boxFinset]; norm_num
        have hlog : (1 : ℝ) ≤ Real.log (((1 : ℕ) : ℝ) + 2) := by
          have : (((1 : ℕ) : ℝ) + 2) = 3 := by norm_num
          rw [this]; exact one_le_log_three
        have h81 : (81 : ℝ) ≤ max C 81 := le_max_right _ _
        nlinarith [hle, hlog, h81]
    · have h := (hfull t hge x).1
      have hCM : C ≤ max C 81 := le_max_left _ _
      nlinarith [h, hlog0, hCM]
  · intro t x y
    rcases Nat.lt_or_ge t 2 with hlt | hge
    · interval_cases t
      · rw [greenTime_zero]
        exact le_trans (by norm_num) (le_max_right (C : ℝ) 81)
      · exact le_trans (greenTime_one_le_one (d := 4) x y)
          (le_trans (by norm_num) (le_max_right (C : ℝ) 81))
    · exact le_trans ((hfull t hge x).2 y) (le_max_left _ _)

/-- **The sub-exponential tail of a single membrane value in dimension four.**
The membrane at a site is a linear functional of the scenery in a box whose
coefficients have `ℓ²` norm at most `M log(m+2)` and `ℓ^∞` norm at most `M`. -/
theorem exists_membrane_tail_four (hVS : Sandpile.External.VarianceScale)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ w, w ∂ν = 0 →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ (m : ℕ) (y : Site 4) (L s : ℝ), 1 ≤ L → Real.log ((m : ℝ) + 2) ≤ L → 0 ≤ s →
          LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | s ≤ |membrane ζ m y|} ≤
            ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2 / L) s))) := by
  classical
  obtain ⟨M, hM, hM2, hMinf⟩ := exists_greenTime_norm_bounds_four hVS
  obtain ⟨c₀, C₀, hc₀, hC₀, hconc⟩ := Sandpile.Frozen.weighted_exp_concentration.2.1 θ₀ K₀ hθ₀
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  refine ⟨c₀ / M, max C₀ 1, div_pos hc₀ hM0,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro ν hprob hmean hexpint hexp m y L s hL hlogL hs
  haveI := hprob
  have hint : Integrable id ν := LatticeProb.integrable_id_of_exp_moment ν θ₀ hθ₀ hexpint
  rcases hs.eq_or_lt with hs0 | hspos
  · subst hs0
    refine le_trans prob_le_one ?_
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (max C₀ 1 * Real.exp (-(c₀ / M * min ((0:ℝ) ^ 2 / L) 0))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : ((0:ℝ) ^ 2 / L) = 0 := by simp
          rw [h1]
          simp
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hempty : {ζ : Site 4 → ℝ | s ≤ |membrane ζ 0 y|} = ∅ := by
      ext ζ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      rw [membrane_zero]
      simpa using hspos
    rw [hempty]
    simp
  · set N := (boxFinset y m).card with hN
    set ℓ : Fin N → ℝ := fun i => greenTime 4 m y (boxEnum y m i) with hℓ
    have hℓnn : ∀ i, 0 ≤ ℓ i := fun i => greenTime_nonneg _ _ _
    obtain ⟨i₀, hi₀⟩ := exists_siteEnum_eq (boxFinset y m)
      (mem_boxFinset (x := y) (y := y) (r := m) (by rw [boxDist_self]; exact Nat.zero_le m))
    have hℓi₀ : (1 : ℝ) ≤ ℓ i₀ := by
      have hval : ℓ i₀ = greenTime 4 m y y := congrArg (greenTime 4 m y) hi₀
      rw [hval]
      exact one_le_greenTime_self m hm y
    have hne : ∃ i, ℓ i ≠ 0 := ⟨i₀, by intro h; rw [h] at hℓi₀; linarith⟩
    have hTwo : lTwoNorm ℓ ^ 2 = ∑ i, ℓ i ^ 2 := lTwoNorm_sq ℓ
    have hTwoLe : lTwoNorm ℓ ^ 2 ≤ M * L := by
      rw [hTwo, hℓ]
      have hsum : ∑ i : Fin N, greenTime 4 m y (boxEnum y m i) ^ 2
          = ∑' z : Site 4, greenTime 4 m y z ^ 2 := by
        rw [tsum_greenTime_sq_eq_sum]
        exact sum_boxEnum y m fun z => greenTime 4 m y z ^ 2
      rw [hsum]
      exact le_trans (hM2 m y) (mul_le_mul_of_nonneg_left hlogL hM0.le)
    have hTwoPos : 0 < lTwoNorm ℓ ^ 2 := by
      rw [hTwo]
      refine lt_of_lt_of_le (pow_pos (by linarith : (0:ℝ) < ℓ i₀) 2) ?_
      exact Finset.single_le_sum (f := fun i : Fin N => ℓ i ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
    haveI : Nonempty (Fin N) := ⟨i₀⟩
    have hInfLe : lInfNorm ℓ ≤ M := ciSup_le fun i => hMinf m y _
    have hInfPos : 0 < lInfNorm ℓ := lt_of_lt_of_le (by linarith) (le_lInfNorm ℓ i₀)
    have hmean0 : (∫ ξ, boxMembrane m y ξ ∂(Measure.pi fun _ : Fin N => ν)) = 0 :=
      integral_boxMembrane_zero ν hint hmean m y
    have hkey := hconc N ν hprob hexpint hexp (boxMembrane m y)
      (measurable_boxMembrane m y) ℓ hℓnn hne
      (fun ξ i z => abs_boxMembrane_update_le m y ξ i z) s hs
    rw [hmean0] at hkey
    have hmp := LatticeProb.measurePreserving_pick _ ν (boxEnum y m) (boxEnum_injective y m)
    have hmeasset : MeasurableSet {ξ : Fin N → ℝ | s ≤ |boxMembrane m y ξ - 0|} :=
      measurableSet_le measurable_const
        (((measurable_boxMembrane m y).sub measurable_const).abs)
    have hpre : {ζ : Site 4 → ℝ | s ≤ |membrane ζ m y|}
        = (fun ζ : Site 4 → ℝ => fun i => ζ (boxEnum y m i)) ⁻¹'
          {ξ | s ≤ |boxMembrane m y ξ - 0|} := by
      ext ζ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, sub_zero, boxMembrane_pick m y ζ]
    have hmin : (c₀ / M) * min (s ^ 2 / L) s
        ≤ c₀ * min (s ^ 2 / lTwoNorm ℓ ^ 2) (s / lInfNorm ℓ) := by
      rw [mul_min_of_nonneg _ _ (div_pos hc₀ hM0).le, mul_min_of_nonneg _ _ hc₀.le]
      refine min_le_min ?_ ?_
      · rw [show (c₀ / M) * (s ^ 2 / L) = c₀ * (s ^ 2 / (M * L)) by
          field_simp]
        refine mul_le_mul_of_nonneg_left ?_ hc₀.le
        exact div_le_div_of_nonneg_left (sq_nonneg s) hTwoPos hTwoLe
      · rw [show (c₀ / M) * s = c₀ * (s / M) by ring]
        refine mul_le_mul_of_nonneg_left ?_ hc₀.le
        exact div_le_div_of_nonneg_left hs hInfPos hInfLe
    calc LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | s ≤ |membrane ζ m y|}
        = (Measure.pi fun _ : Fin N => ν) {ξ | s ≤ |boxMembrane m y ξ - 0|} := by
          rw [hpre]; exact hmp.measure_preimage hmeasset.nullMeasurableSet
      _ ≤ ENNReal.ofReal (C₀ * Real.exp (-(c₀ *
            min (s ^ 2 / lTwoNorm ℓ ^ 2) (s / lInfNorm ℓ)))) := by
          simpa using hkey
      _ ≤ ENNReal.ofReal (max C₀ 1 * Real.exp (-(c₀ / M * min (s ^ 2 / L) s))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr (by linarith))
            (Real.exp_nonneg _) (le_trans hC₀.le (le_max_left _ _))

/-- **The optimal-stopping supremum is below any uniform bound on the negative
part of the membrane over the reachable pairs.**  A walk of at most `t` steps
from `x` stays in the box of radius `t`, and the time it stops reading is at
most `t`. -/
theorem stoppingSup_neg_membrane_le (hd : 1 ≤ d) (x : Site d) (ζ : Site d → ℝ) (t : ℕ)
    {lam : ℝ}
    (hlam : ∀ m : ℕ, m ≤ t → ∀ z ∈ boxFinset x t, -(membrane ζ m z) ≤ lam) :
    stoppingSup t x (fun k X => -(membrane ζ (t - k) (X k))) ≤ lam := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  show sSup {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ t) ∧
      a = ∫ X, -(membrane ζ (t - τ X) (X (τ X))) ∂(walkLaw d x)} ≤ lam
  refine csSup_le ⟨_, stoppingSup_mem t x (fun k X => -(membrane ζ (t - k) (X k)))⟩ ?_
  rintro a ⟨τ, hτ, hτt, rfl⟩
  rw [integral_walkLaw x (F := fun X => -(membrane ζ (t - τ X) (X (τ X))))
    ((measurable_stoppedMembrane t ζ hτ hτt).neg.aestronglyMeasurable)]
  have hae : (fun ξ => -(membrane ζ (t - τ (walkPath x ξ))
        (walkPath x ξ (τ (walkPath x ξ)))))
      ≤ᵐ[Measure.infinitePi fun _ : ℕ => stepLaw d] fun _ => lam := by
    filter_upwards [ae_boxDist_walkPath hd x] with ξ hξ
    exact hlam _ (Nat.sub_le t _) _ (mem_boxFinset (le_trans (hξ _) (hτt _)))
  have hmono := integral_mono_ae
    ((integrable_stoppedMembrane hd x ζ t hτ hτt).neg) (integrable_const lam) hae
  simpa using hmono

/-- **The difference is below any uniform bound on the negative part of the
membrane over the reachable pairs.** -/
theorem odometerOf_sub_membrane_le (hd : 1 ≤ d) (ζ : Site d → ℝ) (t : ℕ) (x : Site d)
    {lam : ℝ}
    (hlam : ∀ m : ℕ, m ≤ t → ∀ z ∈ boxFinset x t, -(membrane ζ m z) ≤ lam) :
    odometerOf ζ t x - membrane ζ t x ≤ lam := by
  rw [Sandpile.Frozen.difference_representation d hd ζ t x]
  exact stoppingSup_neg_membrane_le hd x ζ t hlam

/-- **The union bound over the reachable pairs.** -/
theorem measure_difference_gt_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    (t : ℕ) (x : Site d) (lam : ℝ) :
    LatticeProb.iidLaw d ν {ζ : Site d → ℝ | lam < odometerOf ζ t x - membrane ζ t x} ≤
      ∑ m ∈ Finset.range (t + 1), ∑ z ∈ boxFinset x t,
        LatticeProb.iidLaw d ν {ζ : Site d → ℝ | lam ≤ |membrane ζ m z|} := by
  classical
  have hsub : {ζ : Site d → ℝ | lam < odometerOf ζ t x - membrane ζ t x} ⊆
      ⋃ m ∈ Finset.range (t + 1), ⋃ z ∈ boxFinset x t,
        {ζ : Site d → ℝ | lam ≤ |membrane ζ m z|} := by
    intro ζ hζ
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hcon
    have hlam : ∀ m : ℕ, m ≤ t → ∀ z ∈ boxFinset x t, -(membrane ζ m z) ≤ lam := by
      intro m hm z hz
      have h := hcon m (Finset.mem_range.mpr (by omega)) z hz
      have h2 : -(membrane ζ m z) ≤ |membrane ζ m z| := neg_le_abs _
      linarith
    have := odometerOf_sub_membrane_le hd ζ t x hlam
    exact absurd hζ (by simpa using this)
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  exact Finset.sum_le_sum fun m _ => measure_biUnion_finset_le _ _

/-- **The upper tail of `u_t - V_t` in dimension four.**  The union bound over
the `(t+1)(2t+1)^4` reachable pairs, against the sub-exponential tail of a
single membrane value, with the logarithmic shift chosen so that the polynomial
factor is beaten. -/
theorem exists_difference_tail_four (hVS : Sandpile.External.VarianceScale)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ A₀ c C : ℝ, 1 ≤ A₀ ∧ 0 < c ∧ 0 < C ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ w, w ∂ν = 0 →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ t : ℕ, 2 ≤ t → ∀ x : Site 4, ∀ v : ℝ, 0 ≤ v →
          LatticeProb.iidLaw 4 ν
              {ζ : Site 4 → ℝ |
                A₀ * Real.log ((t : ℝ) + 2) + v < odometerOf ζ t x - membrane ζ t x} ≤
            ENNReal.ofReal (C * Real.exp (-(c * v)) / ((t : ℝ) + 2) ^ 2) := by
  classical
  obtain ⟨c₀, C₀, hc₀, hC₀, htail⟩ := exists_membrane_tail_four hVS θ₀ K₀ hθ₀
  refine ⟨max 1 (7 / c₀), c₀, 16 * C₀, le_max_left _ _, hc₀, by positivity, ?_⟩
  intro ν hprob hmean hexpint hexp t ht x v hv
  haveI := hprob
  set A₀ : ℝ := max 1 (7 / c₀) with hA₀def
  have hA₀ : (1 : ℝ) ≤ A₀ := le_max_left _ _
  have hA₀c : (7 : ℝ) ≤ c₀ * A₀ := by
    have h := le_max_right (1 : ℝ) (7 / c₀)
    rw [← hA₀def] at h
    have h2 : (7 : ℝ) ≤ A₀ * c₀ := (div_le_iff₀ hc₀).mp h
    linarith [h2, mul_comm A₀ c₀]
  set T : ℝ := (t : ℝ) + 2 with hTdef
  have htR : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hT4 : (4 : ℝ) ≤ T := by rw [hTdef]; linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  set L : ℝ := Real.log T with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    exact le_trans one_le_log_three (Real.log_le_log (by norm_num) (by linarith))
  set lam : ℝ := A₀ * L + v with hlamdef
  have hlam0 : (0 : ℝ) ≤ lam := by rw [hlamdef]; nlinarith
  -- the tail of a single membrane value at the shifted level
  have hterm : ∀ m ∈ Finset.range (t + 1), ∀ z ∈ boxFinset x t,
      LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | lam ≤ |membrane ζ m z|} ≤
        ENNReal.ofReal (C₀ * Real.exp (-(c₀ * lam))) := by
    intro m hm z _
    have hmt : m ≤ t := by have := Finset.mem_range.mp hm; omega
    have hlogm : Real.log ((m : ℝ) + 2) ≤ L := by
      rw [hLdef, hTdef]
      refine Real.log_le_log (by positivity) ?_
      have : (m : ℝ) ≤ (t : ℝ) := by exact_mod_cast hmt
      linarith
    refine le_trans (htail ν hprob hmean hexpint hexp m z L lam hL1 hlogm hlam0) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₀.le
    have hmin : lam ≤ min (lam ^ 2 / L) lam := by
      refine le_min ?_ le_rfl
      rw [le_div_iff₀ (by linarith)]
      nlinarith [hlamdef, hA₀, hL1, hv]
    nlinarith [hmin, hc₀]
  -- the union bound
  have hcount := measure_difference_gt_le (d := 4) ν (by norm_num) t x lam
  have hcard : ((Finset.range (t + 1)).card * (boxFinset x t).card : ℕ)
      = (t + 1) * (2 * t + 1) ^ 4 := by
    rw [Finset.card_range, card_boxFinset]
  refine le_trans hcount ?_
  have hstep : ∑ m ∈ Finset.range (t + 1), ∑ z ∈ boxFinset x t,
      LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | lam ≤ |membrane ζ m z|} ≤
      ENNReal.ofReal ((((t + 1) * (2 * t + 1) ^ 4 : ℕ) : ℝ) *
        (C₀ * Real.exp (-(c₀ * lam)))) := by
    have h1 : ∑ m ∈ Finset.range (t + 1), ∑ z ∈ boxFinset x t,
        LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | lam ≤ |membrane ζ m z|} ≤
        ∑ _m ∈ Finset.range (t + 1), ∑ _z ∈ boxFinset x t,
          ENNReal.ofReal (C₀ * Real.exp (-(c₀ * lam))) :=
      Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun z hz => hterm m hm z hz
    refine le_trans h1 (le_of_eq ?_)
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, card_boxFinset,
      nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine le_trans hstep (ENNReal.ofReal_le_ofReal ?_)
  -- the arithmetic of the polynomial factor against the power of `T`
  have hexpsplit : Real.exp (-(c₀ * lam))
      = Real.exp (-(c₀ * A₀ * L)) * Real.exp (-(c₀ * v)) := by
    rw [← Real.exp_add, hlamdef]
    congr 1
    ring
  have hpow : Real.exp (-(c₀ * A₀ * L)) = T ^ (-(c₀ * A₀)) := by
    rw [hLdef, Real.rpow_def_of_pos hT0]
    congr 1
    ring
  have hpow7 : T ^ (-(c₀ * A₀)) ≤ T ^ (-(7 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hT7 : T ^ (-(7 : ℝ)) = (T ^ (7 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hT0.le, ← Real.rpow_natCast T 7]
    norm_num
  have hcardle : (((t + 1) * (2 * t + 1) ^ 4 : ℕ) : ℝ) ≤ 16 * T ^ (5 : ℕ) := by
    have h1 : ((t : ℝ) + 1) ≤ T := by rw [hTdef]; linarith
    have h2 : (2 * (t : ℝ) + 1) ≤ 2 * T := by rw [hTdef]; linarith
    have h3 : (0 : ℝ) ≤ 2 * (t : ℝ) + 1 := by positivity
    have h4 : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
    push_cast
    nlinarith [pow_le_pow_left₀ h3 h2 4, h1, h4, hT0, pow_nonneg hT0.le 4]
  have hexpv : (0 : ℝ) < Real.exp (-(c₀ * v)) := Real.exp_pos _
  have hT7pos : (0 : ℝ) < T ^ (7 : ℕ) := by positivity
  calc (((t + 1) * (2 * t + 1) ^ 4 : ℕ) : ℝ) * (C₀ * Real.exp (-(c₀ * lam)))
      = (((t + 1) * (2 * t + 1) ^ 4 : ℕ) : ℝ) * C₀ *
          (Real.exp (-(c₀ * A₀ * L)) * Real.exp (-(c₀ * v))) := by
        rw [hexpsplit]; ring
    _ ≤ (16 * T ^ (5 : ℕ)) * C₀ * ((T ^ (7 : ℕ))⁻¹ * Real.exp (-(c₀ * v))) := by
        have hle : Real.exp (-(c₀ * A₀ * L)) ≤ (T ^ (7 : ℕ))⁻¹ := by
          rw [hpow, ← hT7]; exact hpow7
        have hnn : (0 : ℝ) ≤ (((t + 1) * (2 * t + 1) ^ 4 : ℕ) : ℝ) * C₀ :=
          mul_nonneg (Nat.cast_nonneg _) hC₀.le
        have h16 : (0 : ℝ) ≤ 16 * T ^ (5 : ℕ) * C₀ := by positivity
        have hprod : Real.exp (-(c₀ * A₀ * L)) * Real.exp (-(c₀ * v))
            ≤ (T ^ (7 : ℕ))⁻¹ * Real.exp (-(c₀ * v)) :=
          mul_le_mul_of_nonneg_right hle hexpv.le
        have hcards : (((t + 1) * (2 * t + 1) ^ 4 : ℕ) : ℝ) * C₀ ≤ 16 * T ^ (5 : ℕ) * C₀ :=
          mul_le_mul_of_nonneg_right hcardle hC₀.le
        nlinarith [hprod, hcards, hnn, h16, mul_nonneg (inv_nonneg.mpr hT7pos.le) hexpv.le]
    _ = 16 * C₀ * Real.exp (-(c₀ * v)) / T ^ 2 := by
        field_simp

/-- `∫_0^a c e^{cs}\,ds = e^{ca} - 1`. -/
theorem integral_exp_scaled (c a : ℝ) :
    (∫ s in (0 : ℝ)..a, c * Real.exp (c * s)) = Real.exp (c * a) - 1 := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) a,
      HasDerivAt (fun u : ℝ => Real.exp (c * u)) (c * Real.exp (c * s)) s := by
    intro s _
    have h1 : HasDerivAt (fun u : ℝ => c * u) c s := by
      simpa using (hasDerivAt_id s).const_mul c
    have h2 := h1.exp
    simpa [mul_comm] using h2
  have hint : IntervalIntegrable (fun s : ℝ => c * Real.exp (c * s)) volume 0 a :=
    (Continuous.intervalIntegrable (by continuity) 0 a)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

/-- **`lem:d4-difference-tail`, in the form the frozen statement asks for.**
The tail of `u_t - V_t` above the logarithmic shift is integrated against the
exponential by the layer-cake formula. -/
theorem exists_difference_exp_moment_four (hVS : Sandpile.External.VarianceScale)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ A₀ c C : ℝ, 0 < A₀ ∧ 0 < c ∧ 0 < C ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ w, w ∂ν = 0 →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ t : ℕ, 2 ≤ t → ∀ x : Site 4,
          ∫⁻ ζ, ENNReal.ofReal (Real.exp (c * max 0 (odometerOf ζ t x -
              membrane ζ t x - A₀ * Real.log ((t : ℝ) + 2))) - 1)
              ∂(LatticeProb.iidLaw 4 ν) ≤
            ENNReal.ofReal (C / ((t : ℝ) + 2) ^ 2) := by
  classical
  obtain ⟨A₀, c₁, C₁, hA₀, hc₁, hC₁, hdt⟩ := exists_difference_tail_four hVS θ₀ K₀ hθ₀
  refine ⟨A₀, c₁ / 2, C₁, by linarith, by linarith, hC₁, ?_⟩
  intro ν hprob hmean hexpint hexp t ht x
  haveI := hprob
  set c : ℝ := c₁ / 2 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  set T : ℝ := (t : ℝ) + 2 with hTdef
  have htR : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hT0 : (0 : ℝ) < T := by rw [hTdef]; linarith
  set W : (Site 4 → ℝ) → ℝ := fun ζ =>
    max 0 (odometerOf ζ t x - membrane ζ t x - A₀ * Real.log T) with hWdef
  have hWmble : Measurable W := by
    refine Measurable.max measurable_const ?_
    exact ((measurable_odometerOf t x).sub (measurable_membrane t x)).sub measurable_const
  have hWnn : 0 ≤ᵐ[LatticeProb.iidLaw 4 ν] W :=
    Filter.Eventually.of_forall fun ζ => le_max_left _ _
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul (μ := LatticeProb.iidLaw 4 ν)
    (f := W) (g := fun s : ℝ => c * Real.exp (c * s)) hWnn hWmble.aemeasurable
    (fun _ _ => Continuous.intervalIntegrable (by continuity) _ _)
    (Filter.Eventually.of_forall fun s => by positivity)
  have hrw : ∀ ζ : Site 4 → ℝ,
      Real.exp (c * W ζ) - 1 = ∫ s in (0 : ℝ)..(W ζ), c * Real.exp (c * s) :=
    fun ζ => (integral_exp_scaled c (W ζ)).symm
  rw [lintegral_congr fun ζ => by rw [hrw ζ], hlayer]
  -- the tail bound at each level
  have hterm : ∀ s ∈ Set.Ioi (0 : ℝ),
      LatticeProb.iidLaw 4 ν {ζ | s < W ζ} * ENNReal.ofReal (c * Real.exp (c * s)) ≤
        ENNReal.ofReal (C₁ * c / T ^ 2 * Real.exp (-(c * s))) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hset : {ζ : Site 4 → ℝ | s < W ζ}
        = {ζ : Site 4 → ℝ |
            A₀ * Real.log T + s < odometerOf ζ t x - membrane ζ t x} := by
      ext ζ
      simp only [Set.mem_setOf_eq, hWdef, lt_max_iff]
      constructor
      · rintro (h | h)
        · exact absurd h (not_lt.mpr hs0.le)
        · linarith
      · intro h
        exact Or.inr (by linarith)
    rw [hset]
    have hmeas := hdt ν hprob hmean hexpint hexp t ht x s hs0.le
    have hprod : ENNReal.ofReal (C₁ * Real.exp (-(c₁ * s)) / T ^ 2) *
        ENNReal.ofReal (c * Real.exp (c * s))
        = ENNReal.ofReal (C₁ * c / T ^ 2 * Real.exp (-(c * s))) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show -(c * s) = -(c₁ * s) + c * s by rw [hcdef]; ring, Real.exp_add]
      field_simp
    calc LatticeProb.iidLaw 4 ν
          {ζ : Site 4 → ℝ | A₀ * Real.log T + s < odometerOf ζ t x - membrane ζ t x} *
            ENNReal.ofReal (c * Real.exp (c * s))
        ≤ ENNReal.ofReal (C₁ * Real.exp (-(c₁ * s)) / T ^ 2) *
            ENNReal.ofReal (c * Real.exp (c * s)) := by
          exact mul_le_mul' (by rw [hTdef]; exact hmeas) le_rfl
      _ = ENNReal.ofReal (C₁ * c / T ^ 2 * Real.exp (-(c * s))) := hprod
  refine le_trans (setLIntegral_mono' measurableSet_Ioi hterm) ?_
  -- the remaining integral is elementary
  have hintg : IntegrableOn (fun s : ℝ => C₁ * c / T ^ 2 * Real.exp (-(c * s)))
      (Set.Ioi (0 : ℝ)) := by
    have h := (exp_neg_integrableOn_Ioi (0 : ℝ) hc).const_mul (C₁ * c / T ^ 2)
    have heq : (fun x : ℝ => C₁ * c / T ^ 2 * Real.exp (-c * x))
        = fun s : ℝ => C₁ * c / T ^ 2 * Real.exp (-(c * s)) := by
      funext s; rw [neg_mul]
    rwa [heq] at h
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun s : ℝ => C₁ * c / T ^ 2 * Real.exp (-(c * s)) :=
    Filter.Eventually.of_forall fun s => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hintg hnn]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  have hform : (∫ s in Set.Ioi (0 : ℝ), Real.exp (-(c * s)))
      = ∫ s in Set.Ioi (0 : ℝ), Real.exp (-c * s) := by
    simp [neg_mul]
  rw [hform, integral_exp_neg_mul_Ioi_zero hc]
  field_simp

end Sandpile
