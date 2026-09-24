/-
The mean overshoot of the ball exit time past a horizon decays geometrically,
uniformly in the starting point and in the Brownian model.

`Sandpile/Support/LimExitTail.lean` bounds the probability that the motion has not
left the ball of radius `s` by the `n`-th block time `n·T₀`, `T₀ = 4ds²`, by `κⁿ`
with `κ = 1/√(2π)`, uniformly in everything.  The mean overshoot
`E[(τ_s − t)⁺]` obeys the one-step inequality

  `(θ − t)⁺ ≤ T₀·1_{θ > t} + (θ − t − T₀)⁺`,

so iterating and letting the horizon go to infinity (the overshoot is dominated by
the integrable exit time and tends to zero pointwise) gives

  `E[(τ_s − n·T₀)⁺] ≤ T₀·κⁿ/(1 − κ)`.

This is the quantitative form of the `T → ∞` limit of `sandpile.tex:2511-2513`: it
turns every statement of `LimBallStoppedTail.lean` whose horizon was chosen after
the probability space into one whose horizon is chosen before it, and it is what a
chaining estimate needs, since a rate is what lets a growing modulus constant be
beaten.
-/
import Sandpile.Support.LimExitTail
import LatticeProb.Prob.BrownianExitTime

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- The block length `4ds²` of `LimExitTail.lean`. -/
noncomputable def blockLen (d : ℕ) (s : ℝ) : ℝ≥0 := ⟨4 * d * s ^ 2, by positivity⟩

theorem blockLen_pos {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) : 0 < blockLen d s := by
  rw [blockLen, ← NNReal.coe_lt_coe]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  show (0 : ℝ) < 4 * d * s ^ 2
  positivity

/-- The geometric ratio `1/√(2π)` of the block estimate. -/
noncomputable def blockRatio : ℝ := 1 / Real.sqrt (2 * Real.pi)

theorem blockRatio_pos : 0 < blockRatio := by
  rw [blockRatio]
  positivity

theorem blockRatio_lt_one : blockRatio < 1 := by
  rw [blockRatio, div_lt_one (by positivity)]
  have h2 : (2 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h1 : (1 : ℝ) < Real.sqrt (2 * Real.pi) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  exact h1

section

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {y : Space d} {B : ℝ≥0 → Ω → Space d}
  {P : Measure Ω} [IsProbabilityMeasure P] {s : ℝ}

/-- The exit time exceeds the `m`-th block time only on the event that the motion is still
in the ball at every block time up to `m`. -/
theorem measure_exitTime_gt_le (hd : 0 < d) (hB : IsBrownian d y B P)
    (hc : ∀ ω, Continuous fun t => B t ω) (hs : 0 < s) (m : ℕ) :
    P {ω | ((m : ℝ) * (blockLen d s : ℝ)) < (LatticeProb.exitTime B y s ω).toReal}
      ≤ ENNReal.ofReal (blockRatio ^ m) := by
  have hsub : {ω | ((m : ℝ) * (blockLen d s : ℝ)) < (LatticeProb.exitTime B y s ω).toReal}
      ⊆ {ω | ∀ k : Fin (m + 1), dist (B (blockTime (blockLen d s) k) ω) y < s} := by
    intro ω hω k
    by_contra hdist
    rw [not_lt] at hdist
    have hle : LatticeProb.exitTime B y s ω ≤ ((blockTime (blockLen d s) k : ℝ≥0) : ℝ≥0∞) := by
      refine (LatticeProb.exitTime_le_iff hc y s ω _).mpr
        ⟨blockTime (blockLen d s) k, le_rfl, ?_⟩
      rwa [← dist_eq_norm]
    have hk : ((blockTime (blockLen d s) k : ℝ≥0) : ℝ)
        ≤ (m : ℝ) * (blockLen d s : ℝ) := by
      rw [blockTime]
      push_cast
      have : (k : ℝ) ≤ (m : ℝ) := by
        have := Nat.lt_succ_iff.mp k.isLt
        exact_mod_cast this
      have hb : (0 : ℝ) ≤ (blockLen d s : ℝ) := (blockLen d s).coe_nonneg
      nlinarith
    have hlt : ((m : ℝ) * (blockLen d s : ℝ)) < (LatticeProb.exitTime B y s ω).toReal := hω
    have hthis : (LatticeProb.exitTime B y s ω).toReal
        ≤ ((blockTime (blockLen d s) k : ℝ≥0) : ℝ) := by
      have h2 := ENNReal.toReal_mono (by simp) hle
      simpa using h2
    linarith
  refine le_trans (measure_mono hsub) ?_
  have h := ballBlockEvent_measure_le hd hB s hs m
  refine le_trans h ?_
  rw [blockRatio, ← ENNReal.ofReal_pow (by positivity)]

end

section

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {y : Space d} {B : ℝ≥0 → Ω → Space d}
  {P : Measure Ω} [IsProbabilityMeasure P] {s : ℝ}

/-- The overshoot of the exit time past a horizon. -/
noncomputable def exitOvershoot (B : ℝ≥0 → Ω → Space d) (y : Space d) (s t : ℝ) (ω : Ω) : ℝ :=
  max ((LatticeProb.exitTime B y s ω).toReal - t) 0

omit [MeasurableSpace Ω] in
theorem exitOvershoot_nonneg (B : ℝ≥0 → Ω → Space d) (y : Space d) (s t : ℝ) (ω : Ω) :
    0 ≤ exitOvershoot B y s t ω := le_max_right _ _

omit [MeasurableSpace Ω] in
theorem exitOvershoot_antitone (B : ℝ≥0 → Ω → Space d) (y : Space d) (s : ℝ) {t t' : ℝ}
    (h : t ≤ t') (ω : Ω) : exitOvershoot B y s t' ω ≤ exitOvershoot B y s t ω := by
  unfold exitOvershoot
  refine max_le_max ?_ le_rfl
  linarith

omit [MeasurableSpace Ω] in
theorem exitOvershoot_le_step (B : ℝ≥0 → Ω → Space d) (y : Space d) (s t : ℝ) {T₀ : ℝ}
    (hT₀ : 0 ≤ T₀) (ω : Ω) :
    exitOvershoot B y s t ω
      ≤ T₀ * Set.indicator {ω | t < (LatticeProb.exitTime B y s ω).toReal} (fun _ => (1 : ℝ)) ω
        + exitOvershoot B y s (t + T₀) ω := by
  set θ := (LatticeProb.exitTime B y s ω).toReal with hθ
  by_cases hlt : t < θ
  · rw [Set.indicator_of_mem (show ω ∈ {ω | t < (LatticeProb.exitTime B y s ω).toReal} from hlt),
      mul_one]
    unfold exitOvershoot
    rcases le_total θ (t + T₀) with h | h
    · rw [max_eq_left (show (0:ℝ) ≤ θ - t by linarith),
        max_eq_right (show θ - (t + T₀) ≤ (0:ℝ) by linarith)]
      linarith
    · rw [max_eq_left (show (0:ℝ) ≤ θ - t by linarith),
        max_eq_left (show (0:ℝ) ≤ θ - (t + T₀) by linarith)]
      linarith
  · rw [not_lt] at hlt
    unfold exitOvershoot
    rw [max_eq_right (by linarith)]
    have : 0 ≤ T₀ * Set.indicator {ω | t < (LatticeProb.exitTime B y s ω).toReal}
        (fun _ => (1 : ℝ)) ω :=
      mul_nonneg hT₀ (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    have h2 : (0 : ℝ) ≤ max (θ - (t + T₀)) 0 := le_max_right _ _
    linarith

theorem measurable_exitOvershoot (hm : ∀ t, StronglyMeasurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) (y : Space d) (s t : ℝ) :
    Measurable (exitOvershoot B y s t) := by
  have h := (LatticeProb.measurable_exitTime hm hc y s).ennreal_toReal
  exact (h.sub measurable_const).max measurable_const

theorem integrable_exitOvershoot (hm : ∀ t, StronglyMeasurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) (y : Space d) (s t : ℝ)
    (hint : Integrable (fun ω => (LatticeProb.exitTime B y s ω).toReal) P) :
    Integrable (exitOvershoot B y s t) P := by
  refine Integrable.mono' (hint.norm.add (integrable_const |t|))
    (measurable_exitOvershoot hm hc y s t).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (exitOvershoot_nonneg B y s t ω)]
  simp only [Pi.add_apply]
  unfold exitOvershoot
  rcases le_total ((LatticeProb.exitTime B y s ω).toReal - t) 0 with h | h
  · rw [max_eq_right h]
    positivity
  · rw [max_eq_left h]
    have h1 : (LatticeProb.exitTime B y s ω).toReal
        ≤ ‖(LatticeProb.exitTime B y s ω).toReal‖ := le_abs_self _
    have h2 : -t ≤ |t| := neg_le_abs t
    linarith


/-- The integrated one-step inequality. -/
theorem integral_exitOvershoot_step (_hd : 0 < d) (_hB : IsBrownian d y B P)
    (hc : ∀ ω, Continuous fun t => B t ω) (hm : ∀ t, StronglyMeasurable (B t)) (_hs : 0 < s)
    (hint : Integrable (fun ω => (LatticeProb.exitTime B y s ω).toReal) P) {m : ℕ} (t : ℝ)
    (hmt : P {ω | t < (LatticeProb.exitTime B y s ω).toReal} ≤ ENNReal.ofReal (blockRatio ^ m)) :
    (∫ ω, exitOvershoot B y s t ω ∂P)
      ≤ (blockLen d s : ℝ) * blockRatio ^ m
        + ∫ ω, exitOvershoot B y s (t + (blockLen d s : ℝ)) ω ∂P := by
  classical
  set T₀ : ℝ := (blockLen d s : ℝ) with hT₀
  have hT₀0 : 0 ≤ T₀ := (blockLen d s).coe_nonneg
  have hmeas : MeasurableSet {ω | t < (LatticeProb.exitTime B y s ω).toReal} :=
    measurableSet_lt measurable_const ((LatticeProb.measurable_exitTime hm hc y s).ennreal_toReal)
  have hind : Integrable
      (fun ω => T₀ * Set.indicator {ω | t < (LatticeProb.exitTime B y s ω).toReal}
        (fun _ => (1 : ℝ)) ω) P :=
    ((integrable_const (1 : ℝ)).indicator hmeas).const_mul T₀
  have hmono := integral_mono (integrable_exitOvershoot hm hc y s t hint)
    (hind.add (integrable_exitOvershoot hm hc y s (t + T₀) hint))
    (fun ω => exitOvershoot_le_step B y s t hT₀0 ω)
  simp only [Pi.add_apply] at hmono
  rw [integral_add hind (integrable_exitOvershoot hm hc y s (t + T₀) hint)] at hmono
  refine le_trans hmono ?_
  have hle : P.real {ω | t < (LatticeProb.exitTime B y s ω).toReal} ≤ blockRatio ^ m := by
    have h2 := ENNReal.toReal_mono (by simp) hmt
    rwa [ENNReal.toReal_ofReal (pow_nonneg blockRatio_pos.le m)] at h2
  have hkey : (∫ a, T₀ * Set.indicator {ω | t < (LatticeProb.exitTime B y s ω).toReal}
      (fun _ => (1 : ℝ)) a ∂P) ≤ T₀ * blockRatio ^ m := by
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) hmeas]
    simp only [smul_eq_mul, mul_one]
    exact mul_le_mul_of_nonneg_left hle hT₀0
  linarith

/-- **The mean overshoot decays geometrically.** -/
theorem integral_exitOvershoot_le (hd : 0 < d) (hB : IsBrownian d y B P)
    (hc : ∀ ω, Continuous fun t => B t ω) (hm : ∀ t, StronglyMeasurable (B t)) (hs : 0 < s)
    (hint : Integrable (fun ω => (LatticeProb.exitTime B y s ω).toReal) P) (n : ℕ) :
    (∫ ω, exitOvershoot B y s ((n : ℝ) * (blockLen d s : ℝ)) ω ∂P)
      ≤ (blockLen d s : ℝ) * blockRatio ^ n / (1 - blockRatio) := by
  classical
  set T₀ : ℝ := (blockLen d s : ℝ) with hT₀
  have hT₀0 : 0 < T₀ := by
    rw [hT₀, ← NNReal.coe_zero, NNReal.coe_lt_coe]
    exact blockLen_pos hd hs
  have hκ0 : 0 < blockRatio := blockRatio_pos
  have hκ1 : blockRatio < 1 := blockRatio_lt_one
  set F : ℕ → ℝ := fun j => ∫ ω, exitOvershoot B y s (((n + j : ℕ) : ℝ) * T₀) ω ∂P with hF
  -- the iterated inequality
  have hstep : ∀ j : ℕ, F j ≤ T₀ * blockRatio ^ (n + j) + F (j + 1) := by
    intro j
    have hmt := measure_exitTime_gt_le hd hB hc hs (n + j)
    have h := integral_exitOvershoot_step (m := n + j) hd hB hc hm hs hint
      (((n + j : ℕ) : ℝ) * T₀) hmt
    have hcast : (((n + j : ℕ) : ℝ) * T₀) + T₀ = ((n + (j + 1) : ℕ) : ℝ) * T₀ := by
      push_cast
      ring
    rw [hcast] at h
    exact h
  have hiter : ∀ j : ℕ, F 0 ≤ T₀ * (∑ i ∈ Finset.range j, blockRatio ^ (n + i)) + F j := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      refine le_trans ih ?_
      have h := hstep k
      rw [Finset.sum_range_succ, mul_add]
      linarith
  -- the tail tends to zero
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hzero : (0 : ℝ) = ∫ _ω : Ω, (0 : ℝ) ∂P := by simp
    rw [hF, hzero]
    refine tendsto_integral_of_dominated_convergence
      (fun ω => (LatticeProb.exitTime B y s ω).toReal) (fun j => ?_) hint (fun j => ?_) ?_
    · exact (measurable_exitOvershoot hm hc y s _).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (exitOvershoot_nonneg B y s _ ω)]
      unfold exitOvershoot
      have hnn : (0 : ℝ) ≤ ((n + j : ℕ) : ℝ) * T₀ := by positivity
      rcases le_total ((LatticeProb.exitTime B y s ω).toReal - ((n + j : ℕ) : ℝ) * T₀) 0
        with h | h
      · rw [max_eq_right h]
        exact ENNReal.toReal_nonneg
      · rw [max_eq_left h]
        linarith
    · filter_upwards with ω
      refine tendsto_const_nhds.congr' ?_
      have hbig : ∀ᶠ j : ℕ in atTop,
          (LatticeProb.exitTime B y s ω).toReal ≤ ((n + j : ℕ) : ℝ) * T₀ := by
        have hdiv : Tendsto (fun j : ℕ => ((n + j : ℕ) : ℝ) * T₀) atTop atTop := by
          have h1 : Tendsto (fun j : ℕ => ((n + j : ℕ) : ℝ)) atTop atTop := by
            have : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
            refine tendsto_atTop_mono (fun j => ?_) this
            push_cast
            linarith [Nat.cast_nonneg (α := ℝ) n]
          exact h1.atTop_mul_const hT₀0
        exact hdiv.eventually_ge_atTop _
      filter_upwards [hbig] with j hj
      unfold exitOvershoot
      rw [max_eq_right (by linarith)]
  -- the geometric sum
  have hgeo : ∀ j : ℕ, (∑ i ∈ Finset.range j, blockRatio ^ (n + i))
      ≤ blockRatio ^ n / (1 - blockRatio) := by
    intro j
    have hrw : (∑ i ∈ Finset.range j, blockRatio ^ (n + i))
        = blockRatio ^ n * ∑ i ∈ Finset.range j, blockRatio ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_add]
    have hd1 : (0 : ℝ) < 1 - blockRatio := by linarith
    have hne : blockRatio ≠ 1 := ne_of_lt hκ1
    have hsum : (∑ i ∈ Finset.range j, blockRatio ^ i) ≤ 1 / (1 - blockRatio) := by
      have h1 : (∑ i ∈ Finset.range j, blockRatio ^ i)
          = (1 - blockRatio ^ j) / (1 - blockRatio) := by
        rw [geom_sum_eq hne]
        field_simp
        ring
      have h2 : (1 : ℝ) - blockRatio ^ j ≤ 1 := by nlinarith [pow_nonneg hκ0.le j]
      rw [h1, div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    rw [hrw]
    calc blockRatio ^ n * (∑ i ∈ Finset.range j, blockRatio ^ i)
        ≤ blockRatio ^ n * (1 / (1 - blockRatio)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = blockRatio ^ n / (1 - blockRatio) := by ring
  -- pass to the limit
  have hfinal : ∀ j : ℕ, F 0 ≤ T₀ * (blockRatio ^ n / (1 - blockRatio)) + F j := by
    intro j
    refine le_trans (hiter j) ?_
    have := mul_le_mul_of_nonneg_left (hgeo j) hT₀0.le
    linarith
  have hconv : Tendsto (fun j => T₀ * (blockRatio ^ n / (1 - blockRatio)) + F j) atTop
      (𝓝 (T₀ * (blockRatio ^ n / (1 - blockRatio)) + 0)) := tendsto_const_nhds.add hlim
  rw [add_zero] at hconv
  have := ge_of_tendsto hconv (Eventually.of_forall hfinal)
  have hF0 : F 0 = ∫ ω, exitOvershoot B y s ((n : ℝ) * T₀) ω ∂P := by
    rw [hF]
    norm_num
  rw [hF0] at this
  calc (∫ ω, exitOvershoot B y s ((n : ℝ) * T₀) ω ∂P)
      ≤ T₀ * (blockRatio ^ n / (1 - blockRatio)) := this
    _ = T₀ * blockRatio ^ n / (1 - blockRatio) := by ring

end

end Sandpile.Support
