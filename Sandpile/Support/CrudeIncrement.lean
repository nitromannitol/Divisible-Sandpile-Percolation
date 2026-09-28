import Sandpile.Frozen.DGT4SmoothedOdometerTail
import Sandpile.Support.HeightLower

/-!
# The crude logarithmic upper bound on the mean odometer

The crude logarithmic upper bound `eq:dgt4-crude-log-upper` of
`sandpile.tex:4482-4502`.

The paper bounds the lower tail of `ζ(0) + P u_t(0)` by applying
`lem:weighted-exp-conc` to that functional directly.  Here the same tail is
obtained from two results that are already proved, which avoids building the
Lipschitz weights of `ζ(0) + P u_t(0)` a second time: on the event that
`-ζ(0) - P u_t(0)` exceeds `h`, either `ζ(0)` falls below `-(h + E u_t(0))/2`,
which the exponential moment bounds by Markov's inequality, or the smoothed
centred odometer `P(u_t - E u_t(0))(0)` falls below `-(h + E u_t(0))/2`, which
is `lem:dgt4-smoothed-odometer-tail` at `m = 1`.  Integrating the resulting tail
against `h` in `eq:dgt4-height-increment` gives the increment bound
`E u_{t+1}(0) - E u_t(0) ≤ C e^{-c E u_t(0)}`, and integrating that is
`exists_log_upper_of_increment`.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### The lower tail of the one-site law from its exponential moment -/

/-- Markov's inequality for the exponential moment: a law with
`∫ e^{θ₀|z|} ≤ K₀` has `ν(-∞, -s] ≤ K₀ e^{-θ₀ s}`. -/
theorem measureReal_Iic_le_of_exp_moment (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {θ₀ K₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀) (s : ℝ) :
    ν.real (Set.Iic (-s)) ≤ K₀ * Real.exp (-(θ₀ * s)) := by
  have hmeas : MeasurableSet (Set.Iic (-s)) := measurableSet_Iic
  have hlow : ∀ z ∈ Set.Iic (-s), Real.exp (θ₀ * s) ≤ Real.exp (θ₀ * |z|) := by
    intro z hz
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hθ₀.le)
    have : z ≤ -s := hz
    have : s ≤ -z := by linarith
    exact le_trans this (neg_le_abs z)
  have hint : ∫ z in Set.Iic (-s), Real.exp (θ₀ * s) ∂ν
      ≤ ∫ z in Set.Iic (-s), Real.exp (θ₀ * |z|) ∂ν := by
    refine setIntegral_mono_on (integrable_const _) (hexpint.integrableOn) hmeas hlow
  have hleft : ∫ _z in Set.Iic (-s), Real.exp (θ₀ * s) ∂ν
      = ν.real (Set.Iic (-s)) * Real.exp (θ₀ * s) := by
    rw [setIntegral_const, smul_eq_mul]
  have hright : ∫ z in Set.Iic (-s), Real.exp (θ₀ * |z|) ∂ν ≤ K₀ := by
    refine le_trans ?_ hexp
    refine setIntegral_le_integral hexpint ?_
    exact Filter.Eventually.of_forall fun z => (Real.exp_pos _).le
  have hexppos : (0 : ℝ) < Real.exp (θ₀ * s) := Real.exp_pos _
  have hkey : ν.real (Set.Iic (-s)) * Real.exp (θ₀ * s) ≤ K₀ := by
    rw [← hleft]; linarith [hint, hright]
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hexppos]
  exact hkey

/-! ### The lower tail of `ζ(0) + P u_t(0)` about its mean -/

/-- On the event that `-ζ(0) - P u_t(0)` exceeds `h`, either the scenery at the
origin falls below `-(h + E u_t(0))/2` or the smoothed centred odometer does. -/
theorem reflected_subset (hd : 1 ≤ d) (ζ : Site d → ℝ) (t : ℕ) (mean h : ℝ)
    (hh : h ≤ -(ζ 0) - avg (odometerOf ζ t) 0) :
    ζ 0 ≤ -((h + mean) / 2) ∨
      (avg^[1] fun x => odometerOf ζ t x - mean) 0 ≤ -((h + mean) / 2) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [not_le] at h1 h2
  rw [avg_iterate_sub_const hd 1 (odometerOf ζ t) mean 0, Function.iterate_one] at h2
  linarith

/-- **The lower tail of `ζ(0) + P u_t(0)`.**  For `E u_t(0) ≥ 2` the tail decays
exponentially in `h + E u_t(0)`. -/
theorem exists_reflected_tail (_hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (t : ℕ) (h : ℝ), 0 ≤ h →
      2 ≤ (∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)) →
      (LatticeProb.iidLaw d ν).real
          {ζ : Site d → ℝ | h ≤ -(ζ 0) - avg (odometerOf ζ t) 0} ≤
        C * Real.exp (-(c * ((h + ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)) / 2))) := by
  classical
  haveI := hprob
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  obtain ⟨c₀, C₀, hc₀, hC₀, hsm⟩ :=
    Sandpile.Frozen.dgt4_smoothed_odometer_tail d hd ν hprob hmean hvar hvar' θ₀ K₀ hθ₀
      hexpint hexp
  have hK₀ : 0 < max K₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨min θ₀ c₀, max K₀ 1 + C₀, lt_min hθ₀ hc₀, by positivity, ?_⟩
  intro t h hh hmean2
  set P : Measure (Site d → ℝ) := LatticeProb.iidLaw d ν with hP
  set mean : ℝ := ∫ η, odometerOf η t 0 ∂P with hmeandef
  set s : ℝ := (h + mean) / 2 with hsdef
  have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; linarith
  have hs0 : (0 : ℝ) ≤ s := by linarith
  set A : Set (Site d → ℝ) := {ζ : Site d → ℝ | h ≤ -(ζ 0) - avg (odometerOf ζ t) 0} with hA
  set A₁ : Set (Site d → ℝ) := {ζ : Site d → ℝ | ζ 0 ≤ -s} with hA₁
  set A₂ : Set (Site d → ℝ) :=
    {ζ : Site d → ℝ | (avg^[1] fun x => odometerOf ζ t x - mean) 0 ≤ -s} with hA₂
  have hsub : A ⊆ A₁ ∪ A₂ := by
    intro ζ hζ
    rcases reflected_subset hd1 ζ t mean h hζ with h1 | h2
    · exact Or.inl h1
    · exact Or.inr h2
  have hb₁ : P.real A₁ ≤ max K₀ 1 * Real.exp (-(θ₀ * s)) := by
    rw [hA₁, measureReal_coord_le ν 0 (-s)]
    exact measureReal_Iic_le_of_exp_moment ν hθ₀ hexpint
      (le_trans hexp (le_max_left K₀ 1)) s
  have hb₂ : P.real A₂ ≤ C₀ * Real.exp (-(c₀ * s)) := by
    have hmm := hsm 1 le_rfl t s hs1
    have hone : ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [hone, Real.one_rpow, Real.one_rpow, mul_one, mul_one] at hmm
    have hmin : min (s ^ 2) s = s := min_eq_right (by nlinarith)
    rw [hmin] at hmm
    have hnn : (0 : ℝ) ≤ C₀ * Real.exp (-(c₀ * s)) := by positivity
    rw [Measure.real, ← ENNReal.toReal_ofReal hnn]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hmm
  have hunion : P.real A ≤ P.real A₁ + P.real A₂ :=
    le_trans (measureReal_mono hsub) (measureReal_union_le _ _)
  have hc1 : Real.exp (-(θ₀ * s)) ≤ Real.exp (-(min θ₀ c₀ * s)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left θ₀ c₀, hs0])
  have hc2 : Real.exp (-(c₀ * s)) ≤ Real.exp (-(min θ₀ c₀ * s)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right θ₀ c₀, hs0])
  calc P.real A ≤ P.real A₁ + P.real A₂ := hunion
    _ ≤ max K₀ 1 * Real.exp (-(min θ₀ c₀ * s)) + C₀ * Real.exp (-(min θ₀ c₀ * s)) := by
        have h1 := mul_le_mul_of_nonneg_left hc1 hK₀.le
        have h2 := mul_le_mul_of_nonneg_left hc2 hC₀.le
        linarith [hb₁, hb₂]
    _ = (max K₀ 1 + C₀) * Real.exp (-(min θ₀ c₀ * s)) := by ring

/-! ### Integrating the tail: the crude increment bound -/

/-- `∫_0^∞ e^{-bh} dh = 1/b`. -/
theorem integral_exp_neg_mul_Ioi_zero {b : ℝ} (hb : 0 < b) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-b * x) = 1 / b := by
  have h := integral_exp_neg_mul_rpow (p := 1) (b := b) one_pos hb
  simp only [Real.rpow_one] at h
  rw [h, show (1 : ℝ) / 1 + 1 = 2 by norm_num, Real.Gamma_two, mul_one,
    show (-1 : ℝ) / 1 = -1 by norm_num]
  rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg hb.le, Real.rpow_one, one_div]

/-- The negative part of the scenery at the origin is integrable. -/
theorem integrable_negPart_coord (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) :
    Integrable (fun ζ : Site d → ℝ => max 0 (-(ζ 0))) (LatticeProb.iidLaw d ν) := by
  have hb : Integrable (fun ζ : Site d → ℝ => ζ 0) (LatticeProb.iidLaw d ν) :=
    integrable_coord ν hint 0
  refine Integrable.mono' hb.abs
    ((measurable_const.max ((measurable_pi_apply 0).neg)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ζ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left 0 _)]
  exact max_le (abs_nonneg _) (neg_le_abs _)

/-- **The one-step bound** `eq:dgt4-one-step-mean-increment`: since `P u_t ≥ 0`,
every increment of the mean is at most `E(-ζ(0))₊`. -/
theorem meanOdometerOf_succ_sub_le (hd1 : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (t : ℕ) :
    (∫ ζ, odometerOf ζ (t + 1) 0 ∂(LatticeProb.iidLaw d ν))
        - ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)
      ≤ ∫ ζ, max 0 (-(ζ 0)) ∂(LatticeProb.iidLaw d ν) := by
  rw [meanOdometerOf_succ_sub hd1 ν hint hmean hpos t]
  refine integral_mono (integrable_reflected ν hint hpos t)
    (integrable_negPart_coord ν hint) fun ζ => ?_
  refine max_le_max le_rfl ?_
  have hz : avg (fun _ : Site d => (0 : ℝ)) 0 = 0 := by
    show (∑ _i : Fin d, ((0 : ℝ) + 0)) / (2 * (d : ℝ)) = 0
    simp
  have h0 : (0 : ℝ) ≤ avg (odometerOf ζ t) 0 := by
    have h := avg_mono_le (d := d) (f := fun _ => (0 : ℝ)) (g := odometerOf ζ t)
      (fun y => odometerOf_nonneg ζ t y) 0
    linarith [hz.le, hz.ge]
  linarith

/-- **The crude increment bound** `E u_{t+1}(0) - E u_t(0) ≤ C e^{-c E u_t(0)}`. -/
theorem exists_crude_increment (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℕ,
      (∫ ζ, odometerOf ζ (t + 1) 0 ∂(LatticeProb.iidLaw d ν))
          - ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)
        ≤ C * Real.exp (-(c * ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν))) := by
  classical
  haveI := hprob
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hint : Integrable id ν := integrable_id_of_exp_moment ν θ₀ hθ₀ hexpint
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    Integrable.mono' hint.abs (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  obtain ⟨c₁, C₁, hc₁, hC₁, htail⟩ :=
    exists_reflected_tail hGH hd ν hprob hmean hvar hvar' θ₀ K₀ hθ₀ hexpint hexp
  set P : Measure (Site d → ℝ) := LatticeProb.iidLaw d ν with hP
  -- the uniform bound on every increment
  set D : ℝ := ∫ ζ, max 0 (-(ζ 0)) ∂P with hD
  have hD0 : 0 ≤ D := integral_nonneg fun ζ => le_max_left _ _
  have huniform : ∀ t : ℕ,
      (∫ ζ, odometerOf ζ (t + 1) 0 ∂P) - ∫ ζ, odometerOf ζ t 0 ∂P ≤ D :=
    fun t => meanOdometerOf_succ_sub_le hd1 ν hint hmean hpos t
  refine ⟨c₁ / 2, max (2 * C₁ / c₁) (D * Real.exp c₁),
    by positivity, lt_of_lt_of_le (by positivity) (le_max_left _ _), ?_⟩
  intro t
  set mean : ℝ := ∫ ζ, odometerOf ζ t 0 ∂P with hmeandef
  have hmeannn : 0 ≤ mean := integral_nonneg fun ζ => odometerOf_nonneg ζ t 0
  rcases lt_or_ge mean 2 with hsmall | hbig
  · -- bounded mean: the uniform bound suffices after enlarging the constant
    refine le_trans (huniform t) ?_
    have h1 : Real.exp (-(c₁ / 2 * mean)) ≥ Real.exp (-c₁) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : D * Real.exp c₁ * Real.exp (-c₁) = D := by
      rw [mul_assoc, ← Real.exp_add]; simp
    calc D = D * Real.exp c₁ * Real.exp (-c₁) := h2.symm
      _ ≤ D * Real.exp c₁ * Real.exp (-(c₁ / 2 * mean)) := by
          have : (0 : ℝ) ≤ D * Real.exp c₁ := by positivity
          exact mul_le_mul_of_nonneg_left h1 this
      _ ≤ max (2 * C₁ / c₁) (D * Real.exp c₁) * Real.exp (-(c₁ / 2 * mean)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · -- large mean: integrate the tail
    set f : (Site d → ℝ) → ℝ := fun ζ => max 0 (-(ζ 0) - avg (odometerOf ζ t) 0) with hf
    have hfint : Integrable f P := integrable_reflected ν hint hpos t
    have hfnn : 0 ≤ᵐ[P] f := Filter.Eventually.of_forall fun ζ => le_max_left _ _
    have hlayer : ∫ ζ, f ζ ∂P = ∫ h in Set.Ioi (0 : ℝ), P.real {ζ | h ≤ f ζ} :=
      hfint.integral_eq_integral_meas_le hfnn
    set A : ℝ := C₁ * Real.exp (-(c₁ * (mean / 2))) with hAdef
    have hAnn : 0 ≤ A := by positivity
    have hbint : IntegrableOn (fun h : ℝ => A * Real.exp (-(c₁ / 2) * h)) (Set.Ioi (0 : ℝ)) :=
      (exp_neg_integrableOn_Ioi 0 (by positivity)).const_mul A
    have hdom : ∫ h in Set.Ioi (0 : ℝ), P.real {ζ | h ≤ f ζ}
        ≤ ∫ h in Set.Ioi (0 : ℝ), A * Real.exp (-(c₁ / 2) * h) := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun h => ENNReal.toReal_nonneg) hbint ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      have hh0 : 0 < h := hh
      have hset : {ζ : Site d → ℝ | h ≤ f ζ}
          = {ζ : Site d → ℝ | h ≤ -(ζ 0) - avg (odometerOf ζ t) 0} := by
        ext ζ
        simp only [Set.mem_setOf_eq, hf, le_max_iff]
        constructor
        · rintro (hc | hc)
          · linarith
          · exact hc
        · intro hc; exact Or.inr hc
      rw [hset]
      refine le_trans (htail t h hh0.le hbig) ?_
      have hsplit : Real.exp (-(c₁ * ((h + mean) / 2)))
          = Real.exp (-(c₁ * (mean / 2))) * Real.exp (-(c₁ / 2) * h) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit, hAdef]
      ring_nf
      exact le_rfl
    have hval : ∫ h in Set.Ioi (0 : ℝ), A * Real.exp (-(c₁ / 2) * h) = A * (2 / c₁) := by
      rw [integral_const_mul, integral_exp_neg_mul_Ioi_zero (by positivity)]
      field_simp
    rw [meanOdometerOf_succ_sub hd1 ν hint hmean hpos t, ← hf, hlayer]
    refine le_trans hdom ?_
    rw [hval]
    have hexpeq : Real.exp (-(c₁ * (mean / 2))) = Real.exp (-(c₁ / 2 * mean)) := by
      congr 1; ring
    calc A * (2 / c₁) = C₁ * Real.exp (-(c₁ * (mean / 2))) * (2 / c₁) := by rw [hAdef]
      _ = (2 * C₁ / c₁) * Real.exp (-(c₁ / 2 * mean)) := by rw [hexpeq]; ring
      _ ≤ max (2 * C₁ / c₁) (D * Real.exp c₁) * Real.exp (-(c₁ / 2 * mean)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- **The crude logarithmic upper bound** `eq:dgt4-crude-log-upper`. -/
theorem exists_crude_log_upper (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)) ≤ C * Real.log ((t : ℝ) + 2) := by
  haveI := hprob
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hint : Integrable id ν := integrable_id_of_exp_moment ν θ₀ hθ₀ hexpint
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    Integrable.mono' hint.abs (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  obtain ⟨c, C, hc, hC, hstep⟩ :=
    exists_crude_increment hGH hd ν hprob hmean hvar hvar' θ₀ K₀ hθ₀ hexpint hexp
  have h0 : (∫ ζ, odometerOf ζ 0 0 ∂(LatticeProb.iidLaw d ν)) = 0 := by
    simp [odometerOf]
  exact exists_log_upper_of_increment C c hC hc _ h0 (meanOdometerOf_mono ν hpos) hstep

end Sandpile
