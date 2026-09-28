import Sandpile.Support.Dgt4ABandLawProfile
import Sandpile.Support.Dgt4ABandWeights

/-!
# The one-site law of a set of band parameters

The one-site law attached to a set of band parameters, and the Step-1 tail profile
`eq:dgt4-band-profile` of `thm:dgt4-many-limits` (`sandpile.tex:5930-6055`) for it.
`BandParameters.law` builds the law from a smoothing resolution `m` and a variance `v` for
the positive summand; `BandParameters.level_sep` records that the band levels are strictly
separated, `P.level i ≤ P.l1 * P.level j` for `i < j`. `bandProfile_law` shows this
constructed law satisfies `BandProfile`, by combining three error terms that all tend to
zero (the exponential tail of the positive summand relative to its own band's weight, the
smoothing width `2/m k`, and the tail-to-weight ratio `P.weight_tail_ratio_tendsto`), and
`bandUpperIsolation_tail_law` specializes this to the first half of
`eq:dgt4-band-upper-isolation`: the mass above the `k`th band level is `o(P.weight k)`.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

/-- The one-site law attached to band parameters, a smoothing resolution `m` and
a variance `v` for the positive summand. -/
def BandParameters.law (P : BandParameters) (m : ℕ → ℕ) (mu : ℝ) (v : ℝ≥0) : Measure ℝ :=
  bandLaw (1 - ∑' k, P.weight k) mu v P.l1 P.level P.weight P.theta m

/-- The bands are separated: every band lies strictly above the next one. -/
theorem BandParameters.level_sep (P : BandParameters) (hA : P.A⁻¹ ≤ P.l1) {i j : ℕ}
    (hij : i < j) : P.level i ≤ P.l1 * P.level j := by
  have hA1 : (1 : ℝ) < P.A := P.hA
  have hA0 : (0 : ℝ) < P.A := zero_lt_one.trans hA1
  have hstep : P.level i ≤ P.level (j - 1) := by
    refine pow_le_pow_right₀ hA1.le ?_
    omega
  have hj : j - 1 + 1 = j := by omega
  have hlevel : P.level (j - 1) * P.A = P.level j := by
    rw [BandParameters.level, BandParameters.level, ← pow_succ, hj]
  have hpos : 0 < P.level j := P.level_pos j
  have : P.level (j - 1) = P.A⁻¹ * P.level j := by
    rw [← hlevel]
    field_simp
  rw [this] at hstep
  refine hstep.trans ?_
  exact mul_le_mul_of_nonneg_right hA hpos.le

/-- **The Step-1 tail profile of the constructed law.** -/
theorem bandProfile_law (P : BandParameters) (hA : P.A⁻¹ ≤ P.l1)
    (m : ℕ → ℕ) (hm : ∀ k, 0 < m k) (hmtop : Tendsto (fun k => (m k : ℝ)) atTop atTop)
    (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (htot : ∑' k, P.weight k ≤ 1) :
    BandProfile P (P.law m mu v) := by
  classical
  set lam : ℝ := 2 / P.l1 with hlamdef
  have hl0 : 0 < P.l1 := P.hl1.1
  have hl1 : P.l1 < 1 := P.hl1.2
  have hlam : 0 < lam := by positivity
  have hlaml1 : lam * P.l1 = 2 := by
    simp only [hlamdef]
    field_simp
  set w0 : ℝ := 1 - ∑' k, P.weight k with hw0def
  have hw0 : 0 ≤ w0 := by simp only [hw0def]; linarith
  -- the three error terms tend to zero
  have hE1 : Tendsto (fun k : ℕ =>
      w0 * (Real.exp (-(mu * lam) + (v : ℝ) * lam ^ 2 / 2) *
        Real.exp (-(lam * (P.l1 * P.level k)))) / P.weight k) atTop (𝓝 0) := by
    have hrewrite : ∀ k : ℕ,
        w0 * (Real.exp (-(mu * lam) + (v : ℝ) * lam ^ 2 / 2) *
            Real.exp (-(lam * (P.l1 * P.level k)))) / P.weight k
          = (w0 * Real.exp (-(mu * lam) + (v : ℝ) * lam ^ 2 / 2) / P.c0) *
              Real.exp (-(P.level k)) := by
      intro k
      rw [BandParameters.weight]
      rw [show -(lam * (P.l1 * P.level k)) = -(2 * P.level k) by
        rw [← mul_assoc, hlaml1]]
      field_simp [P.hc0.ne', Real.exp_ne_zero]
      rw [show -(2 * P.level k) = -(P.level k) + -(P.level k) by ring, Real.exp_add]
      ring
    have hlim : Tendsto (fun k : ℕ => Real.exp (-(P.level k))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp P.level_tendsto)
    have := hlim.const_mul (w0 * Real.exp (-(mu * lam) + (v : ℝ) * lam ^ 2 / 2) / P.c0)
    rw [mul_zero] at this
    exact this.congr fun k => (hrewrite k).symm
  have hE2 : Tendsto (fun k : ℕ => 2 / (m k : ℝ)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hmtop
  have hE3 := P.weight_tail_ratio_tendsto
  have hE : Tendsto (fun k : ℕ =>
      w0 * (Real.exp (-(mu * lam) + (v : ℝ) * lam ^ 2 / 2) *
          Real.exp (-(lam * (P.l1 * P.level k)))) / P.weight k
        + 2 / (m k : ℝ) + (∑' j : ℕ, P.weight (k + 1 + j)) / P.weight k)
      atTop (𝓝 0) := by
    simpa using (hE1.add hE2).add hE3
  intro η hη
  filter_upwards [hE.eventually_lt_const hη] with k hk r hr
  have hset : {z : ℝ | P.level k - (1 - P.l1) * P.level k * r < -z}
      = Iio (-(P.level k - bandWidth P.l1 (P.level k) * r)) := neg_gt_setOf _
  have hmain := abs_bandLaw_profile_le (w0 := w0) (mu := mu) (v := v) (l1 := P.l1) (a := P.level)
    (w := P.weight) (θ := P.theta) (m := m) hw0 P.weight_pos
    (fun k => (P.htheta k).1) (fun k => (P.htheta k).2) hl0 hl1 P.level_pos hm
    P.level_tendsto P.summable_weight (fun i j hij => P.level_sep hA hij) hv hlam k hr.1 hr.2
  rw [BandParameters.law]
  rw [show {z : ℝ | -(z) > P.level k - (1 - P.l1) * P.level k * r}
      = Iio (-(P.level k - bandWidth P.l1 (P.level k) * r)) from hset]
  exact hmain.trans hk.le


/-- **The first half of `eq:dgt4-band-upper-isolation`.**  The mass the law puts
above the `k`th band level is `o(ω_k)`: it is the profile estimate at `r = 0`. -/
theorem bandUpperIsolation_tail_law (P : BandParameters) (hA : P.A⁻¹ ≤ P.l1)
    (m : ℕ → ℕ) (hm : ∀ k, 0 < m k) (hmtop : Tendsto (fun k => (m k : ℝ)) atTop atTop)
    (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (htot : ∑' k, P.weight k ≤ 1) :
    Tendsto (fun k : ℕ =>
        ((P.law m mu v) {z : ℝ | -(z) > P.level k}).toReal / P.weight k) atTop (𝓝 0) := by
  have hprof := bandProfile_law P hA m hm hmtop mu v hv htot
  refine NormedAddGroup.tendsto_nhds_zero.mpr fun η hη => ?_
  filter_upwards [hprof (η / 2) (by linarith)] with k hk
  have hr := hk 0 ⟨le_rfl, zero_le_one⟩
  have hzero : (0 : ℝ) ^ P.theta k = 0 := Real.zero_rpow (by linarith [(P.htheta k).1])
  have hset : P.level k - (1 - P.l1) * P.level k * 0 = P.level k := by ring
  rw [hset, hzero, sub_zero] at hr
  rw [Real.norm_eq_abs]
  linarith


end Sandpile.Support
