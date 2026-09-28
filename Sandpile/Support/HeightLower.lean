import Sandpile.Support.MassConc
import Sandpile.Support.UniformTail

/-!
# The three clauses of the height lower bound `thm:dgt4-height-lower`

The three clauses of `thm:dgt4-height-lower` (`sandpile.tex:4124-4147`). The first two are
compositions of what is already proved: the uniform lower-tail bound of `sandpile.tex:4180-4186`
feeds the uniform mean lower bound, and the pointwise concentration is
`eq:dgt4-pointwise-concentration` in the mass-field language. The third clause is the ratio limit
`u_t(x)/E u_t(0) → 1`. In `L²` it is the variance bound divided by the square of the mean, which
diverges. Almost surely it is a Borel-Cantelli argument along the scales `t_k = ⌈e^{√k}⌉`, whose
logarithm is at least `√k`, so that the mean at `t_k` is at least a constant times `k^{1/d}` and
the concentration bound is summable in `k`; the passage from the scales to all times uses that
the mean is concave and vanishes at time zero, so that `t ↦ E u_t(0)/t` is nonincreasing and the
mean grows by at most the factor `t_{k+1}/t_k`, which tends to one.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### Moments from the exponential moment -/

/-- A law with an exponential moment has a second moment. -/
theorem integrable_sq_of_exp_moment (ν : Measure ℝ) (θ₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    Integrable (fun z => z ^ 2) ν := by
  refine (hexp.const_mul (4 / θ₀ ^ 2)).mono'
    ((measurable_id.pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  have h := sq_le_four_exp (θ₀ * |z|) (by positivity)
  have hz : (θ₀ * |z|) ^ 2 = θ₀ ^ 2 * z ^ 2 := by rw [mul_pow, sq_abs]
  rw [hz] at h
  have hpos : (0 : ℝ) < θ₀ ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z), div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith [h]

/-! ### The scenery bridge for integrals -/

/-- Any integral of a function of the scenery is the same under the mass law as
under the i.i.d. law of the one-site scenery. -/
theorem integral_scenery (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    {F : (Site d → ℝ) → ℝ} (hF : AEStronglyMeasurable F (LatticeProb.iidLaw d ν)) :
    ∫ σ, F (scenery d σ) ∂(centeredMassLaw d ν) = ∫ ζ, F ζ ∂(LatticeProb.iidLaw d ν) := by
  have h := integral_map (μ := centeredMassLaw d ν) (φ := scenery d) (f := F)
    (measurable_scenery d).aemeasurable
    (by rw [map_scenery_centeredMassLaw d ν hd]; exact hF)
  rw [map_scenery_centeredMassLaw d ν hd] at h
  rw [← h]

/-- The uniform second moment about the mean, in the mass-field language of the
frozen statements and with the square written as a natural power. -/
theorem exists_odometer_variance_bound (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : Integrable (fun z => z ^ 2) ν) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (t : ℕ) (x : Site d),
      ∫ σ, (odometer σ t x - meanOdometer (centeredMassLaw d ν) t) ^ 2
          ∂(centeredMassLaw d ν) ≤ V := by
  obtain ⟨V, hV, hb⟩ := exists_odometerOf_variance_bound hGH hd ν (integrable_abs_rpow_two ν hsq)
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  refine ⟨V, hV, fun t x => ?_⟩
  have hmeas : AEStronglyMeasurable
      (fun ζ : Site d → ℝ =>
        (odometerOf ζ t x - ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)) ^ 2)
      (LatticeProb.iidLaw d ν) :=
    (((measurable_odometerOf t x).sub measurable_const).pow_const 2).aestronglyMeasurable
  have hEq : ∫ σ, (odometer σ t x - meanOdometer (centeredMassLaw d ν) t) ^ 2
        ∂(centeredMassLaw d ν)
      = ∫ ζ, (odometerOf ζ t x - ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)) ^ 2
        ∂(LatticeProb.iidLaw d ν) := by
    rw [← integral_scenery d ν hd1 hmeas, meanOdometer_eq d ν hd1 t]
    exact integral_congr_ae (Filter.Eventually.of_forall fun σ => by
      simp only [congrFun (odometer_eq_odometerOf σ t) x])
  rw [hEq]
  refine le_trans (le_of_eq ?_) (hb t x)
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only []
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

/-! ### The mean diverges -/

/-- A sequence bounded below past an index by a positive multiple of a positive
power of the logarithm tends to infinity. -/
theorem tendsto_atTop_of_log_lower {m : ℕ → ℝ} {c p : ℝ} (hc : 0 < c) (hp : 0 < p)
    {t₀ : ℕ} (h : ∀ t : ℕ, t₀ ≤ t → c * (Real.log t) ^ p ≤ m t) :
    Tendsto m atTop atTop := by
  have hlog : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrpow : Tendsto (fun t : ℕ => (Real.log t) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp hlog
  exact tendsto_atTop_mono' atTop (eventually_atTop.2 ⟨t₀, h⟩) (hrpow.const_mul_atTop hc)

/-! ### The ratio tends to one in `L²` -/

/-- The `L²` half of the third clause of `thm:dgt4-height-lower`: the variance
bound divided by the square of the mean, which diverges. -/
theorem tendsto_ratio_L2 (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : Integrable (fun z => z ^ 2) ν)
    (hdiv : Tendsto (fun t : ℕ => meanOdometer (centeredMassLaw d ν) t) atTop atTop)
    (x : Site d) :
    Tendsto (fun t : ℕ => ∫ σ, (odometer σ t x /
      meanOdometer (centeredMassLaw d ν) t - 1) ^ 2 ∂(centeredMassLaw d ν)) atTop (𝓝 0) := by
  obtain ⟨V, hV, hb⟩ := exists_odometer_variance_bound hGH hd ν hsq
  set m : ℕ → ℝ := fun t => meanOdometer (centeredMassLaw d ν) t with hm
  have hnonneg : ∀ t : ℕ, 0 ≤ ∫ σ, (odometer σ t x / m t - 1) ^ 2 ∂(centeredMassLaw d ν) :=
    fun t => integral_nonneg fun σ => sq_nonneg _
  have hsqdiv : Tendsto (fun t : ℕ => m t ^ 2) atTop atTop := by
    have := hdiv.atTop_mul_atTop₀ hdiv
    simpa [pow_two] using this
  refine squeeze_zero' (g := fun t : ℕ => V / m t ^ 2) (Eventually.of_forall hnonneg) ?_
    ((tendsto_const_nhds (x := V)).div_atTop hsqdiv)
  filter_upwards [hdiv.eventually_gt_atTop 0] with t ht
  have ht2 : (0 : ℝ) < m t ^ 2 := by positivity
  have hEq : ∫ σ, (odometer σ t x / m t - 1) ^ 2 ∂(centeredMassLaw d ν)
      = (∫ σ, (odometer σ t x - m t) ^ 2 ∂(centeredMassLaw d ν)) / m t ^ 2 := by
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun σ => ?_)
    field_simp
  rw [hEq]
  gcongr
  exact hb t x

/-! ### The mean is concave, so `t ↦ E u_t(0)/t` is nonincreasing -/

/-- The averaging operator is monotone. -/
theorem avg_mono_le {f g : Site d → ℝ} (h : ∀ y, f y ≤ g y) (x : Site d) :
    avg f x ≤ avg g x := by
  show (∑ i : Fin d, (f (x + LatticeProb.unit i) + f (x - LatticeProb.unit i)))
        / (2 * (d : ℝ))
      ≤ (∑ i : Fin d, (g (x + LatticeProb.unit i) + g (x - LatticeProb.unit i)))
        / (2 * (d : ℝ))
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact Finset.sum_le_sum fun i _ => add_le_add (h _) (h _)

/-- **The mean odometer is concave**: its increments are nonincreasing.  This is
the scenery form of the concavity clause of `lem:reflection-increment`, and it
holds because the reflected part `(-ζ(0) - P u_t(0))₊` decreases pointwise as the
odometer grows. -/
theorem meanOdometerOf_concave (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z => max z 0) ν) (t : ℕ) :
    (∫ ζ, odometerOf ζ (t + 2) 0 ∂(LatticeProb.iidLaw d ν))
        - ∫ ζ, odometerOf ζ (t + 1) 0 ∂(LatticeProb.iidLaw d ν)
      ≤ (∫ ζ, odometerOf ζ (t + 1) 0 ∂(LatticeProb.iidLaw d ν))
        - ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) := by
  rw [show t + 2 = (t + 1) + 1 from rfl,
    meanOdometerOf_succ_sub hd ν hint hmean hpos (t + 1),
    meanOdometerOf_succ_sub hd ν hint hmean hpos t]
  refine integral_mono (integrable_reflected ν hint hpos (t + 1))
    (integrable_reflected ν hint hpos t) fun ζ => ?_
  have havg : avg (odometerOf ζ t) 0 ≤ avg (odometerOf ζ (t + 1)) 0 :=
    avg_mono_le (fun y => odometerOf_le_succ ζ t y) 0
  exact max_le_max le_rfl (by linarith)

/-- A sequence starting at zero whose increments are nonincreasing satisfies
`t a_{t+1} ≤ (t+1) a_t`, which is `a_t/t` nonincreasing. -/
theorem concave_seq_step (a : ℕ → ℝ) (h0 : a 0 = 0)
    (hcc : ∀ k : ℕ, a (k + 2) - a (k + 1) ≤ a (k + 1) - a k) (t : ℕ) :
    (t : ℝ) * a (t + 1) ≤ ((t : ℝ) + 1) * a t := by
  have hanti : Antitone fun k : ℕ => a (k + 1) - a k :=
    antitone_nat_of_succ_le fun k => hcc k
  have htel : ∀ n : ℕ, a n = ∑ k ∈ Finset.range n, (a (k + 1) - a k) := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ m ih => rw [Finset.sum_range_succ, ← ih]; ring
  have hsum : ∑ _k ∈ Finset.range t, (a (t + 1) - a t)
      ≤ ∑ k ∈ Finset.range t, (a (k + 1) - a k) :=
    Finset.sum_le_sum fun k hk => hanti (le_of_lt (Finset.mem_range.mp hk))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← htel t] at hsum
  linarith

/-- Hence `a_t s ≤ a_s t` for `1 ≤ s ≤ t`: the mean grows by at most the ratio of
the times. -/
theorem concave_seq_mul_le (a : ℕ → ℝ)
    (hstep : ∀ t : ℕ, (t : ℝ) * a (t + 1) ≤ ((t : ℝ) + 1) * a t)
    (s : ℕ) (hs : 1 ≤ s) :
    ∀ t : ℕ, s ≤ t → a t * (s : ℝ) ≤ a s * (t : ℝ) := by
  intro t hst
  induction t, hst using Nat.le_induction with
  | base => rw [mul_comm]
  | succ n hn ih =>
      have hsR : (0 : ℝ) ≤ (s : ℝ) := by positivity
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        have : 1 ≤ n := le_trans hs hn
        exact_mod_cast this
      have h1 := hstep n
      have h2 : (s : ℝ) * ((n : ℝ) * a (n + 1)) ≤ (s : ℝ) * (((n : ℝ) + 1) * a n) :=
        mul_le_mul_of_nonneg_left h1 hsR
      have h3 : ((n : ℝ) + 1) * (a n * (s : ℝ)) ≤ ((n : ℝ) + 1) * (a s * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      have A : (n : ℝ) * (a (n + 1) * (s : ℝ)) ≤ (n : ℝ) * (a s * ((n : ℝ) + 1)) := by
        nlinarith [h2, h3]
      have := le_of_mul_le_mul_left A hnpos
      push_cast
      linarith

/-! ### The scales `t_k = t₀ + ⌈e^{√k}⌉` -/

/-- The increment of `Real.sqrt` is bounded by `1 / Real.sqrt x`, via the identity
`(√(x + 1) - √x)(√(x + 1) + √x) = 1`. -/
theorem sqrt_succ_sub_sqrt_le (x : ℝ) (hx : 0 < x) :
    Real.sqrt (x + 1) - Real.sqrt x ≤ 1 / Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have ha : Real.sqrt (x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hb : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hmono : Real.sqrt x ≤ Real.sqrt (x + 1) := Real.sqrt_le_sqrt (by linarith)
  have hprod : (Real.sqrt (x + 1) - Real.sqrt x) * (Real.sqrt (x + 1) + Real.sqrt x) = 1 := by
    have h : (Real.sqrt (x + 1) - Real.sqrt x) * (Real.sqrt (x + 1) + Real.sqrt x)
        = Real.sqrt (x + 1) ^ 2 - Real.sqrt x ^ 2 := by ring
    rw [h, ha, hb]; ring
  have hkey : (Real.sqrt (x + 1) - Real.sqrt x) * Real.sqrt x ≤ 1 := by
    refine le_trans ?_ (le_of_eq hprod)
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    linarith [Real.sqrt_nonneg (x + 1)]
  rw [le_div_iff₀ hs]
  exact hkey

/-- `Real.sqrt` of the natural numbers tends to infinity. -/
theorem tendsto_sqrt_natCast_atTop :
    Tendsto (fun k : ℕ => Real.sqrt (k : ℝ)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

/-- The increments `√(k + 1) - √k` tend to zero, squeezed between `0` and `1 / √k` via
`sqrt_succ_sub_sqrt_le`. -/
theorem tendsto_sqrt_succ_sub_sqrt :
    Tendsto (fun k : ℕ => Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun k : ℕ => 1 / Real.sqrt (k : ℝ)) atTop (𝓝 0) :=
    Filter.Tendsto.congr (fun k => by simp [Pi.inv_apply, one_div])
      tendsto_sqrt_natCast_atTop.inv_tendsto_atTop
  refine squeeze_zero' ?_ ?_ hinv
  · filter_upwards with k
    have : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    linarith
  · filter_upwards [eventually_gt_atTop 0] with k hk
    exact sqrt_succ_sub_sqrt_le _ (by exact_mod_cast hk)

/-- The scales of the almost-sure argument: `t_k = t₀ + ⌈e^{√k}⌉`, past the index
`t₀` from which the mean lower bound holds. -/
noncomputable def scaleTime (t₀ k : ℕ) : ℕ := t₀ + ⌈Real.exp (Real.sqrt k)⌉₊

/-- `scaleTime t₀ k` is at least `t₀`, since it adds a nonnegative ceiling term to `t₀`. -/
theorem le_scaleTime (t₀ k : ℕ) : t₀ ≤ scaleTime t₀ k := Nat.le_add_right _ _

/-- `scaleTime t₀ k` is at least one, since `⌈exp (√k)⌉₊` is strictly positive. -/
theorem one_le_scaleTime (t₀ k : ℕ) : 1 ≤ scaleTime t₀ k := by
  have h : 0 < ⌈Real.exp (Real.sqrt (k : ℝ))⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
  rw [scaleTime]
  omega

/-- `exp (√k)` is at most `scaleTime t₀ k`, from `Nat.le_ceil` together with `t₀ ≥ 0`. -/
theorem exp_sqrt_le_scaleTime (t₀ k : ℕ) :
    Real.exp (Real.sqrt (k : ℝ)) ≤ (scaleTime t₀ k : ℝ) := by
  have h := Nat.le_ceil (Real.exp (Real.sqrt (k : ℝ)))
  have ht : (0 : ℝ) ≤ (t₀ : ℝ) := Nat.cast_nonneg _
  rw [scaleTime]
  push_cast
  linarith

/-- `√k` is at most `log (scaleTime t₀ k)`, taking logarithms of `exp_sqrt_le_scaleTime`. -/
theorem sqrt_le_log_scaleTime (t₀ k : ℕ) :
    Real.sqrt (k : ℝ) ≤ Real.log (scaleTime t₀ k : ℝ) := by
  have h := exp_sqrt_le_scaleTime t₀ k
  have hpos : (0 : ℝ) < Real.exp (Real.sqrt (k : ℝ)) := Real.exp_pos _
  calc Real.sqrt (k : ℝ) = Real.log (Real.exp (Real.sqrt (k : ℝ))) := (Real.log_exp _).symm
    _ ≤ Real.log (scaleTime t₀ k : ℝ) := Real.log_le_log hpos h

/-- `exp (√k)` tends to infinity, as `Real.exp` composed with `√·` tending to infinity on the
naturals. -/
theorem tendsto_exp_sqrt_natCast_atTop :
    Tendsto (fun k : ℕ => Real.exp (Real.sqrt (k : ℝ))) atTop atTop :=
  Real.tendsto_exp_atTop.comp tendsto_sqrt_natCast_atTop

/-- `scaleTime t₀` tends to infinity, since it is bounded below by `exp (√k)`
(`exp_sqrt_le_scaleTime`), which itself tends to infinity. -/
theorem tendsto_scaleTime (t₀ : ℕ) : Tendsto (scaleTime t₀) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [tendsto_exp_sqrt_natCast_atTop.eventually_ge_atTop ((b : ℝ))] with k hk
  have h1 : ((b : ℕ) : ℝ) ≤ (scaleTime t₀ k : ℝ) := le_trans hk (exp_sqrt_le_scaleTime t₀ k)
  exact_mod_cast h1

/-- The scales grow by a factor tending to one. -/
theorem scaleTime_ratio (t₀ : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, (scaleTime t₀ (k + 1) : ℝ) ≤ (1 + δ) * (scaleTime t₀ k : ℝ) := by
  have heq : ∀ k : ℕ,
      (Real.exp (Real.sqrt ((k : ℝ) + 1)) + 1) / Real.exp (Real.sqrt (k : ℝ))
        = Real.exp (Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ))
          + 1 / Real.exp (Real.sqrt (k : ℝ)) := by
    intro k
    rw [Real.exp_sub, add_div]
  have h1 : Tendsto (fun k : ℕ =>
      Real.exp (Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ))) atTop (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto (0 : ℝ)).comp tendsto_sqrt_succ_sub_sqrt
    rw [Real.exp_zero] at h
    exact h
  have h2 : Tendsto (fun k : ℕ => 1 / Real.exp (Real.sqrt (k : ℝ))) atTop (𝓝 0) :=
    Filter.Tendsto.congr (fun k => by simp [Pi.inv_apply, one_div])
      tendsto_exp_sqrt_natCast_atTop.inv_tendsto_atTop
  have hq : Tendsto (fun k : ℕ =>
      (Real.exp (Real.sqrt ((k : ℝ) + 1)) + 1) / Real.exp (Real.sqrt (k : ℝ)))
      atTop (𝓝 1) := by
    have h := h1.add h2
    rw [add_zero] at h
    exact h.congr fun k => (heq k).symm
  have hlt : ∀ᶠ k : ℕ in atTop,
      (Real.exp (Real.sqrt ((k : ℝ) + 1)) + 1) / Real.exp (Real.sqrt (k : ℝ)) < 1 + δ :=
    hq.eventually_lt_const (by linarith)
  filter_upwards [hlt] with k hk
  have hepos : (0 : ℝ) < Real.exp (Real.sqrt (k : ℝ)) := Real.exp_pos _
  rw [div_lt_iff₀ hepos] at hk
  have hceil : ((⌈Real.exp (Real.sqrt (((k + 1 : ℕ)) : ℝ))⌉₊ : ℕ) : ℝ)
      < Real.exp (Real.sqrt (((k + 1 : ℕ)) : ℝ)) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hcast : Real.sqrt (((k + 1 : ℕ)) : ℝ) = Real.sqrt ((k : ℝ) + 1) := by push_cast; ring_nf
  rw [hcast] at hceil
  have hle : Real.exp (Real.sqrt (k : ℝ))
      ≤ ((⌈Real.exp (Real.sqrt ((k : ℕ) : ℝ))⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have ht : (0 : ℝ) ≤ (t₀ : ℝ) := Nat.cast_nonneg _
  rw [scaleTime, scaleTime]
  push_cast
  nlinarith [hceil, hk, hle, ht, hδ]

/-! ### Summability of the stretched-exponential tail -/

/-- The stretched-exponential tail `exp (-(α k ^ p))` is summable for any `α, p > 0`, by
comparison with `1 / k ^ 2` past an index where `log k = o(k ^ p)` forces `2 log k ≤ α k ^ p`. -/
theorem summable_exp_neg_rpow {α p : ℝ} (hα : 0 < α) (hp : 0 < p) :
    Summable (fun k : ℕ => Real.exp (-(α * (k : ℝ) ^ p))) := by
  obtain ⟨N₀, hN₀⟩ := (_root_.isLittleO_log_rpow_atTop hp).def (show (0 : ℝ) < α / 2 by positivity)
    |>.exists_forall_of_atTop
  obtain ⟨N, hN, hNge⟩ : ∃ N : ℕ, 1 ≤ N ∧ (N₀ : ℝ) ≤ (N : ℕ) := by
    refine ⟨max 1 ⌈N₀⌉₊, le_max_left _ _, ?_⟩
    exact le_trans (Nat.le_ceil N₀) (by exact_mod_cast le_max_right 1 ⌈N₀⌉₊)
  have hbound : ∀ k : ℕ, N ≤ k → Real.exp (-(α * (k : ℝ) ^ p)) ≤ 1 / (k : ℝ) ^ 2 := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans hN hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hkN : (N₀ : ℝ) ≤ (k : ℝ) := le_trans hNge (by exact_mod_cast hk)
    have h := hN₀ (k : ℝ) hkN
    have hlogpos : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
    have hrpow : (0 : ℝ) ≤ (k : ℝ) ^ p := Real.rpow_nonneg hk0.le _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogpos, abs_of_nonneg hrpow] at h
    have h2 : 2 * Real.log (k : ℝ) ≤ α * (k : ℝ) ^ p := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 2)] at h
      linarith
    have hexp : Real.exp (-(α * (k : ℝ) ^ p)) ≤ Real.exp (-(2 * Real.log (k : ℝ))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hval : Real.exp (-(2 * Real.log (k : ℝ))) = 1 / (k : ℝ) ^ 2 := by
      rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log hk0, one_div, sq]
    linarith [hexp, hval.le, hval.ge]
  have hcomp : Summable (fun n : ℕ => 1 / ((n + N : ℕ) : ℝ) ^ 2) := by
    have hg : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    exact (summable_nat_add_iff N).mpr hg
  refine (summable_nat_add_iff N).mp ?_
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hcomp
  exact hbound (n + N) (Nat.le_add_left _ _)

/-! ### From the scales to all times -/

/-- **The squeeze from a sequence of scales to all times.**  If `u` and `m` are
nondecreasing, the scales `n k` tend to infinity, and along the scales the ratio
is within `δ` of one while the mean grows by at most `1 + δ` from one scale to
the next, then the ratio tends to one along all times. -/
theorem tendsto_ratio_of_scales {u m : ℕ → ℝ} {n : ℕ → ℕ}
    (hu : Monotone u) (hm : Monotone m) (hnT : Tendsto n atTop atTop)
    (hgood : ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      0 < m (n k) ∧ (1 - δ) * m (n k) ≤ u (n k) ∧ u (n k) ≤ (1 + δ) * m (n k) ∧
        m (n (k + 1)) ≤ (1 + δ) * m (n k)) :
    Tendsto (fun t : ℕ => u t / m t) atTop (𝓝 1) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ0, hδ1, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 3 * δ < ε :=
    ⟨min (ε / 4) (1 / 2), lt_min (by linarith) (by norm_num), min_le_right _ _, by
      have : min (ε / 4) (1 / 2) ≤ ε / 4 := min_le_left _ _
      linarith⟩
  obtain ⟨K, hKgood⟩ := hgood δ hδ0
  refine ⟨n K, fun t ht => ?_⟩
  obtain ⟨N, hN⟩ := (tendsto_atTop.1 hnT (t + 1)).exists_forall_of_atTop
  have hPK : n K ≤ t := ht
  have hKN : K ≤ N := by
    by_contra hcon
    rw [Nat.not_le] at hcon
    have := hN K (le_of_lt hcon)
    omega
  set k := Nat.findGreatest (fun j => n j ≤ t) N with hkdef
  have hkP : n k ≤ t := Nat.findGreatest_spec (P := fun j => n j ≤ t) hKN hPK
  have hKk : K ≤ k := Nat.le_findGreatest hKN hPK
  have hkN : k < N := by
    have hNnot : ¬ (n N ≤ t) := by have := hN N le_rfl; omega
    rcases lt_or_eq_of_le (Nat.findGreatest_le (P := fun j => n j ≤ t) N) with h | h
    · exact h
    · exact absurd (h ▸ hkP) hNnot
  have hnext : t < n (k + 1) := by
    have hg := Nat.findGreatest_is_greatest (P := fun j => n j ≤ t)
      (Nat.lt_succ_self k) (show k + 1 ≤ N by omega)
    exact not_le.mp hg
  obtain ⟨hmpos, hlow, hhigh, hrat⟩ := hKgood k hKk
  obtain ⟨hmpos', hlow', hhigh', hrat'⟩ := hKgood (k + 1) (by omega)
  have hmt1 : m (n k) ≤ m t := hm hkP
  have hmt2 : m t ≤ m (n (k + 1)) := hm (le_of_lt hnext)
  have hut1 : u (n k) ≤ u t := hu hkP
  have hut2 : u t ≤ u (n (k + 1)) := hu (le_of_lt hnext)
  have hmtpos : 0 < m t := lt_of_lt_of_le hmpos hmt1
  have hUp : u t ≤ (1 + 3 * δ) * m t := by
    have e1 : u t ≤ (1 + δ) * m (n (k + 1)) := le_trans hut2 hhigh'
    have e3 : (1 + δ) * m (n (k + 1)) ≤ (1 + δ) * ((1 + δ) * m (n k)) :=
      mul_le_mul_of_nonneg_left hrat (by linarith)
    have e4 : (1 + δ) * ((1 + δ) * m (n k)) ≤ (1 + δ) * ((1 + δ) * m t) := by
      nlinarith [hmt1, hδ0]
    have e5 : (1 + δ) * ((1 + δ) * m t) ≤ (1 + 3 * δ) * m t := by
      nlinarith [hmtpos.le, mul_nonneg hδ0.le (show (0 : ℝ) ≤ 1 - δ by linarith)]
    linarith
  have hLo : (1 - 2 * δ) * m t ≤ u t := by
    have f2 : (1 + δ) * u (n k) ≤ (1 + δ) * u t :=
      mul_le_mul_of_nonneg_left hut1 (by linarith)
    have f3 : (1 + δ) * ((1 - δ) * m (n k)) ≤ (1 + δ) * u (n k) :=
      mul_le_mul_of_nonneg_left hlow (by linarith)
    have f4 : (1 - δ) * m (n (k + 1)) ≤ (1 - δ) * ((1 + δ) * m (n k)) :=
      mul_le_mul_of_nonneg_left hrat (by linarith)
    have f5 : (1 - δ) * m t ≤ (1 - δ) * m (n (k + 1)) :=
      mul_le_mul_of_nonneg_left hmt2 (by linarith)
    have f6 : (1 - δ) * m t ≤ (1 + δ) * u t := by nlinarith [f2, f3, f4, f5]
    have h2 : (0 : ℝ) < 1 + δ := by linarith
    refine le_of_mul_le_mul_left ?_ h2
    nlinarith [f6, hmtpos.le, sq_nonneg δ]
  rw [Real.dist_eq, abs_sub_lt_iff]
  refine ⟨?_, ?_⟩
  · have hb : u t / m t ≤ 1 + 3 * δ := by rw [div_le_iff₀ hmtpos]; linarith
    linarith
  · have hb : 1 - 2 * δ ≤ u t / m t := by rw [le_div_iff₀ hmtpos]; linarith
    linarith

/-! ### The mean odometer along the scales -/

/-- The mean of `odometerOf` at the origin is monotone in `t`, from the pointwise monotonicity
`odometerOf_le_succ`. -/
theorem meanOdometerOf_mono (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) :
    Monotone fun t : ℕ => ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) :=
  monotone_nat_of_le_succ fun n =>
    integral_mono (integrable_odometerOf d ν hpos n 0)
      (integrable_odometerOf d ν hpos (n + 1) 0) fun ζ => odometerOf_le_succ ζ n 0

/-- `meanOdometer` is monotone in `t`, transported from `meanOdometerOf_mono` via
`meanOdometer_eq`. -/
theorem meanOdometer_mono (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) :
    Monotone fun t : ℕ => meanOdometer (centeredMassLaw d ν) t := by
  simp only [meanOdometer_eq d ν hd]
  exact meanOdometerOf_mono ν hpos

/-- The mean odometer vanishes at time zero. -/
theorem meanOdometer_zero (d : ℕ) (ν : Measure ℝ) :
    meanOdometer (centeredMassLaw d ν) 0 = 0 := by
  rw [meanOdometer]
  simp [Sandpile.odometer]

/-- `meanOdometer` is concave: its increments over `t` are nonincreasing, transported from
`meanOdometerOf_concave` via `meanOdometer_eq`. -/
theorem meanOdometer_concave (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z => max z 0) ν) (t : ℕ) :
    meanOdometer (centeredMassLaw d ν) (t + 2) - meanOdometer (centeredMassLaw d ν) (t + 1)
      ≤ meanOdometer (centeredMassLaw d ν) (t + 1) - meanOdometer (centeredMassLaw d ν) t := by
  simp only [meanOdometer_eq d ν hd]
  exact meanOdometerOf_concave hd ν hint hmean hpos t

/-- `(√k)^p = k^{p/2}`. -/
theorem sqrt_rpow_eq (k : ℕ) (p : ℝ) :
    (Real.sqrt (k : ℝ)) ^ p = (k : ℝ) ^ (p / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg k)]
  ring_nf

/-- Along the scales the mean is at least a constant times `k^{1/d}`. -/
theorem meanOdometer_scale_lower {c₁ : ℝ} {t₀ : ℕ} (hd : 1 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hlower : ∀ t : ℕ, t₀ ≤ t →
      c₁ * (Real.log t) ^ ((2 : ℝ) / d) ≤ meanOdometer (centeredMassLaw d ν) t)
    (hc₁ : 0 < c₁) (k : ℕ) :
    c₁ * (k : ℝ) ^ ((1 : ℝ) / d) ≤ meanOdometer (centeredMassLaw d ν) (scaleTime t₀ k) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h1 := hlower (scaleTime t₀ k) (le_scaleTime t₀ k)
  have h2 : Real.sqrt (k : ℝ) ≤ Real.log ((scaleTime t₀ k : ℕ) : ℝ) := sqrt_le_log_scaleTime t₀ k
  have h3 : (Real.sqrt (k : ℝ)) ^ ((2 : ℝ) / d)
      ≤ (Real.log ((scaleTime t₀ k : ℕ) : ℝ)) ^ ((2 : ℝ) / d) :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) h2 (by positivity)
  have h4 : (Real.sqrt (k : ℝ)) ^ ((2 : ℝ) / d) = (k : ℝ) ^ ((1 : ℝ) / d) := by
    rw [sqrt_rpow_eq k ((2 : ℝ) / d)]
    congr 1
    field_simp
  rw [h4] at h3
  calc c₁ * (k : ℝ) ^ ((1 : ℝ) / d)
      ≤ c₁ * (Real.log ((scaleTime t₀ k : ℕ) : ℝ)) ^ ((2 : ℝ) / d) :=
        mul_le_mul_of_nonneg_left h3 hc₁.le
    _ ≤ _ := h1

/-- Along the scales the mean grows by at most a factor tending to one. -/
theorem meanOdometer_scale_ratio (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z => max z 0) ν) (t₀ : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop,
      meanOdometer (centeredMassLaw d ν) (scaleTime t₀ (k + 1))
        ≤ (1 + δ) * meanOdometer (centeredMassLaw d ν) (scaleTime t₀ k) := by
  set M : ℕ → ℝ := fun t => meanOdometer (centeredMassLaw d ν) t with hM
  have hstep : ∀ t : ℕ, (t : ℝ) * M (t + 1) ≤ ((t : ℝ) + 1) * M t :=
    concave_seq_step M (meanOdometer_zero d ν)
      (fun k => meanOdometer_concave hd ν hint hmean hpos k)
  have hMono : Monotone M := meanOdometer_mono hd ν hpos
  have hM0 : M 0 = 0 := meanOdometer_zero d ν
  have hMnn : ∀ t, 0 ≤ M t := fun t => by
    have h := hMono (Nat.zero_le t)
    rw [hM0] at h
    exact h
  filter_upwards [scaleTime_ratio t₀ hδ] with k hk
  have h1 : (1 : ℕ) ≤ scaleTime t₀ k := one_le_scaleTime t₀ k
  have h2 : scaleTime t₀ k ≤ scaleTime t₀ (k + 1) := by
    have : ⌈Real.exp (Real.sqrt ((k : ℕ) : ℝ))⌉₊ ≤ ⌈Real.exp (Real.sqrt (((k + 1 : ℕ)) : ℝ))⌉₊ := by
      refine Nat.ceil_le_ceil ?_ |>.trans_eq rfl
      refine Real.exp_le_exp.mpr (Real.sqrt_le_sqrt ?_)
      exact_mod_cast Nat.le_succ k
    rw [scaleTime, scaleTime]
    omega
  have hmul := concave_seq_mul_le M hstep (scaleTime t₀ k) h1 (scaleTime t₀ (k + 1)) h2
  have hnpos : (0 : ℝ) < (scaleTime t₀ k : ℝ) := by exact_mod_cast h1
  have hle : M (scaleTime t₀ (k + 1)) * (scaleTime t₀ k : ℝ)
      ≤ (1 + δ) * M (scaleTime t₀ k) * (scaleTime t₀ k : ℝ) := by
    refine le_trans hmul ?_
    have := mul_le_mul_of_nonneg_left hk (hMnn (scaleTime t₀ k))
    nlinarith [this]
  exact le_of_mul_le_mul_right hle hnpos

/-! ### The ratio tends to one almost surely -/

/-- `s - 1 ≤ min (s²) s`, the form in which the concentration bound is summed. -/
theorem sub_one_le_min_sq (s : ℝ) : s - 1 ≤ min (s ^ 2) s :=
  le_min (by nlinarith [sq_nonneg (2 * s - 1)]) (by linarith)

/-- **The almost-sure half of the third clause of `thm:dgt4-height-lower`.**  Along
the scales `t_k = t₀ + ⌈e^{√k}⌉` the mean is at least `c₁ k^{1/d}`, so the
concentration bound is summable in `k`; Borel-Cantelli gives the limit along the
scales for every `ε = 1/(j+1)`, and the squeeze carries it to all times. -/
theorem tendsto_ratio_ae (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν)
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    {c C c₁ : ℝ} (hc : 0 < c) (hC : 0 < C) (hc₁ : 0 < c₁) {t₀ : ℕ}
    (hconc : ∀ (y : Site d) (t : ℕ) (s : ℝ), 0 ≤ s →
      centeredMassLaw d ν
          {σ | s ≤ |odometer σ t y - meanOdometer (centeredMassLaw d ν) t|} ≤
        ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2) s))))
    (hlower : ∀ t : ℕ, t₀ ≤ t →
      c₁ * (Real.log t) ^ ((2 : ℝ) / d) ≤ meanOdometer (centeredMassLaw d ν) t)
    (x : Site d) :
    ∀ᵐ σ ∂(centeredMassLaw d ν),
      Tendsto (fun t : ℕ => odometer σ t x /
        meanOdometer (centeredMassLaw d ν) t) atTop (𝓝 1) := by
  classical
  set P : Measure (Site d → ℝ) := centeredMassLaw d ν with hP
  set M : ℕ → ℝ := fun t => meanOdometer P t with hMdef
  set n : ℕ → ℕ := scaleTime t₀ with hn
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hp : (0 : ℝ) < (1 : ℝ) / d := by positivity
  have hMscale : ∀ k : ℕ, c₁ * (k : ℝ) ^ ((1 : ℝ) / d) ≤ M (n k) :=
    meanOdometer_scale_lower hd ν hlower hc₁
  have hM0 : M 0 = 0 := meanOdometer_zero d ν
  have hMnn : ∀ t : ℕ, 0 ≤ M t := by
    intro t
    have h : M 0 ≤ M t := meanOdometer_mono hd ν hpos (Nat.zero_le t)
    rw [hM0] at h
    exact h
  have hMpos : ∀ k : ℕ, 1 ≤ k → 0 < M (n k) := by
    intro k hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have : (0 : ℝ) < c₁ * (k : ℝ) ^ ((1 : ℝ) / d) := by positivity
    exact lt_of_lt_of_le this (hMscale k)
  -- Borel-Cantelli at the level `ε = 1/(j+1)`
  have hBC : ∀ j : ℕ, ∀ᵐ σ ∂P, ∀ᶠ k in atTop,
      |odometer σ (n k) x - M (n k)| < (1 / ((j : ℝ) + 1)) * M (n k) := by
    intro j
    set ε : ℝ := 1 / ((j : ℝ) + 1) with hε
    have hεpos : 0 < ε := by positivity
    set β : ℝ := c * ε * c₁ with hβ
    have hβpos : 0 < β := by positivity
    set g : ℕ → ℝ := fun k => C * Real.exp c * Real.exp (-(β * (k : ℝ) ^ ((1 : ℝ) / d)))
      with hg
    have hgnn : ∀ k, 0 ≤ g k := fun k => by positivity
    have hgsum : Summable g := (summable_exp_neg_rpow hβpos hp).mul_left _
    have hbound : ∀ k : ℕ,
        P {σ | ε * M (n k) ≤ |odometer σ (n k) x - M (n k)|} ≤ ENNReal.ofReal (g k) := by
      intro k
      have hsnn : 0 ≤ ε * M (n k) := mul_nonneg hεpos.le (hMnn _)
      refine le_trans (hconc x (n k) (ε * M (n k)) hsnn) ?_
      refine ENNReal.ofReal_le_ofReal ?_
      set s : ℝ := ε * M (n k) with hs
      have h1 : c * (s - 1) ≤ c * min (s ^ 2) s :=
        mul_le_mul_of_nonneg_left (sub_one_le_min_sq s) hc.le
      have h2 : β * (k : ℝ) ^ ((1 : ℝ) / d) ≤ c * s := by
        have := mul_le_mul_of_nonneg_left (hMscale k) (mul_pos hc hεpos).le
        calc β * (k : ℝ) ^ ((1 : ℝ) / d)
            = c * ε * (c₁ * (k : ℝ) ^ ((1 : ℝ) / d)) := by rw [hβ]; ring
          _ ≤ c * ε * M (n k) := by
              exact mul_le_mul_of_nonneg_left (hMscale k) (by positivity)
          _ = c * s := by rw [hs]; ring
      have h3 : Real.exp (-(c * min (s ^ 2) s))
          ≤ Real.exp c * Real.exp (-(β * (k : ℝ) ^ ((1 : ℝ) / d))) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        linarith
      calc C * Real.exp (-(c * min (s ^ 2) s))
          ≤ C * (Real.exp c * Real.exp (-(β * (k : ℝ) ^ ((1 : ℝ) / d)))) :=
            mul_le_mul_of_nonneg_left h3 hC.le
        _ = g k := by rw [hg]; ring
    have hsum : ∑' k : ℕ, P {σ | ε * M (n k) ≤ |odometer σ (n k) x - M (n k)|} ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
      rw [← ENNReal.ofReal_tsum_of_nonneg hgnn hgsum]
      exact ENNReal.ofReal_ne_top
    have h0 := MeasureTheory.measure_setOf_frequently_eq_zero (μ := P)
      (p := fun k σ => ε * M (n k) ≤ |odometer σ (n k) x - M (n k)|) hsum
    have hae : ∀ᵐ σ ∂P, ∀ᶠ k in atTop,
        ¬ (ε * M (n k) ≤ |odometer σ (n k) x - M (n k)|) := by
      have h1 : {σ : Site d → ℝ |
            ¬ (∀ᶠ k in atTop, ¬ (ε * M (n k) ≤ |odometer σ (n k) x - M (n k)|))}
          = {σ : Site d → ℝ |
            ∃ᶠ k in atTop, ε * M (n k) ≤ |odometer σ (n k) x - M (n k)|} := by
        ext σ
        simp only [Set.mem_setOf_eq, Filter.not_eventually, not_not]
      rw [ae_iff, h1]
      exact h0
    filter_upwards [hae] with σ hσ
    filter_upwards [hσ] with k hk
    exact lt_of_not_ge hk
  have hall : ∀ᵐ σ ∂P, ∀ j : ℕ, ∀ᶠ k in atTop,
      |odometer σ (n k) x - M (n k)| < (1 / ((j : ℝ) + 1)) * M (n k) :=
    MeasureTheory.ae_all_iff.2 hBC
  filter_upwards [hall] with σ hσ
  have humono : Monotone fun t : ℕ => odometer σ t x := by
    intro s t hst
    have h1 : odometer σ s x = odometerOf (scenery d σ) s x :=
      congrFun (odometer_eq_odometerOf σ s) x
    have h2 : odometer σ t x = odometerOf (scenery d σ) t x :=
      congrFun (odometer_eq_odometerOf σ t) x
    simp only [h1, h2]
    exact odometerOf_mono_time (scenery d σ) x hst
  refine tendsto_ratio_of_scales (u := fun t : ℕ => odometer σ t x) (m := M) (n := n)
    humono (meanOdometer_mono hd ν hpos) (tendsto_scaleTime t₀) ?_
  intro δ hδ
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  have hjnn : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  have hev : ∀ᶠ k : ℕ in atTop,
      (|odometer σ (n k) x - M (n k)| < (1 / ((j : ℝ) + 1)) * M (n k) ∧
        M (n (k + 1)) ≤ (1 + δ) * M (n k)) ∧ 1 ≤ k :=
    ((hσ j).and (meanOdometer_scale_ratio hd ν hint hmean hpos t₀ hδ)).and
      (eventually_ge_atTop 1)
  obtain ⟨K, hK⟩ := hev.exists_forall_of_atTop
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨⟨habs, hrat⟩, hk1⟩ := hK k hk
  have hmp : 0 < M (n k) := hMpos k hk1
  have hδabs : |odometer σ (n k) x - M (n k)| < δ * M (n k) := by
    refine lt_of_lt_of_le habs ?_
    exact mul_le_mul_of_nonneg_right hj.le (hMnn _)
  rw [abs_lt] at hδabs
  exact ⟨hmp, by linarith [hδabs.1], by linarith [hδabs.2], hrat⟩

end Sandpile
