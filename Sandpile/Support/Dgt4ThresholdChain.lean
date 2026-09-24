/-
The chain that carries the two case-specific displays of
`prop:dgt4-contact-asymptotics` to the contact thresholds.

The two proofs of the proposition, in case (a) at `sandpile.tex:4969` ff. and in
case (b) at `sandpile.tex:5306` ff., both establish a threshold comparison and a
threshold asymptotic:

  "$\P(\{u_{n+1}(0)=0\}\triangle\{J(0)>\E u_n(0)\})/\P(J(0)>\E u_n(0))\to0$"
  (`eq:dgt4-contact-threshold-relative-error`, `eq:dgt4-b-relative-error`), and
  "$\P(J(0)>\E u_n(0))\sim G(0,0)\kappa/n$"
  (`eq:dgt4-threshold-probability` and the display after
  `eq:dgt4-b-mean-increment`).

They are named here `ThresholdRelativeError` and `ThresholdTailAsymptotics`, and
`pointwiseContactThresholds_of` deduces from the pair the two limits that
`Support/Dgt4Contact.lean` turns into the proposition itself and into the
uniform thresholds of `lem:dgt4-path-survival`.

Both proofs reach the threshold asymptotic in the same way: the mean-increment
estimate gives that the increments of the reciprocal threshold probability
converge, in case (a) to `1/G(0,0)` (`sandpile.tex:5003-5011`) and in case (b)
through the integral `\int_0^{\E u_n(0)/G(0,0)}dr/\E(-\zeta(0)-r)_+\sim n/G(0,0)`
(`sandpile.tex:5335-5341`), and then "summing over $n$" inverts the increment.
That last step is `tendsto_div_nat_of_tendsto_sub`, the Cesaro form of the
Stolz theorem, followed by `tendsto_mul_of_inverse_increment`.
-/
import Sandpile.Support.Dgt4Thresholds

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- `P(J(0) > E u_n(0)) ∼ G(0,0)κ/n`, the threshold asymptotic that each case of
`prop:dgt4-contact-asymptotics` establishes. -/
def ThresholdTailAsymptotics (d : ℕ) (ν : Measure ℝ)
    (J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ) (κ : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (n : ℝ) * ((Sandpile.centeredMassLaw d ν)
      {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n < J σ 0}).toReal)
    atTop (𝓝 (Sandpile.green d 0 0 * κ))

/-- `P({u_{n+1}(0)=0} Δ {J(0) > E u_n(0)}) = o(P(J(0) > E u_n(0)))`, the threshold
comparison that each case of `prop:dgt4-contact-asymptotics` establishes. -/
def ThresholdRelativeError (d : ℕ) (ν : Measure ℝ)
    (J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ) : Prop :=
  Tendsto (fun n : ℕ => ((Sandpile.centeredMassLaw d ν)
        (symmDiff {σ | Sandpile.odometer σ (n + 1) 0 = 0}
          {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n < J σ 0})).toReal /
      ((Sandpile.centeredMassLaw d ν)
        {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n < J σ 0}).toReal)
    atTop (𝓝 0)

/-- Shifting the index by one does not change the limit of `n b n`. -/
theorem tendsto_shift_mul {b : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (n : ℝ) * b n) atTop (𝓝 L)) :
    Tendsto (fun m : ℕ => (m : ℝ) * b (m - 1)) atTop (𝓝 L) := by
  have hshift : Tendsto (fun m : ℕ => ((m - 1 : ℕ) : ℝ) * b (m - 1)) atTop (𝓝 L) :=
    h.comp (tendsto_sub_atTop_nat 1)
  have hden : Tendsto (fun m : ℕ => (m : ℝ) - 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (-1) tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun m : ℕ => ((m : ℝ) - 1)⁻¹) atTop (𝓝 0) :=
    hden.inv_tendsto_atTop
  have hratio : Tendsto (fun m : ℕ => 1 + ((m : ℝ) - 1)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hmul := hratio.mul hshift
  rw [one_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with m hm
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hcast]
  have hne : (m : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  field_simp
  ring

theorem tendsto_div_nat_of_tendsto_sub {g : ℕ → ℝ} {c : ℝ}
    (h : Tendsto (fun n : ℕ => g (n + 1) - g n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => g n / (n : ℝ)) atTop (𝓝 c) := by
  have hc := h.cesaro
  have hz : Tendsto (fun n : ℕ => g 0 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (g 0)
  have hsum := hc.add hz
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Finset.sum_range_sub g n]
  field_simp
  ring

theorem tendsto_mul_of_inverse_increment {B : ℕ → ℝ} (hBpos : ∀ n, 0 < B n) {c : ℝ} (hc : 0 < c)
    (hstolz : Tendsto (fun n : ℕ => (B n)⁻¹ / (n : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (n : ℝ) * B n) atTop (𝓝 c⁻¹) := by
  have hinv := hstolz.inv₀ (ne_of_gt hc)
  refine hinv.congr ?_
  intro n
  have hB := (hBpos n).ne'
  field_simp

/-- The threshold asymptotic from the increments of the reciprocal threshold
probability: "summing over `n`" in both cases of `prop:dgt4-contact-asymptotics`. -/
theorem thresholdTailAsymptotics_of_inverse_increment {ν : Measure ℝ}
    {J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ} {κ : ℝ}
    (hG : 0 < Sandpile.green d 0 0 * κ)
    (hBpos : ∀ n : ℕ, 0 < ((Sandpile.centeredMassLaw d ν)
      {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n < J σ 0}).toReal)
    (h : Tendsto (fun n : ℕ =>
        (((Sandpile.centeredMassLaw d ν)
          {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n + 1) < J σ 0}).toReal)⁻¹ -
        (((Sandpile.centeredMassLaw d ν)
          {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n < J σ 0}).toReal)⁻¹)
      atTop (𝓝 (Sandpile.green d 0 0 * κ)⁻¹)) :
    ThresholdTailAsymptotics d ν J κ := by
  have hstolz := tendsto_div_nat_of_tendsto_sub
    (g := fun n : ℕ => (((Sandpile.centeredMassLaw d ν)
      {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n < J σ 0}).toReal)⁻¹) h
  have := tendsto_mul_of_inverse_increment hBpos (inv_pos.mpr hG) hstolz
  rwa [inv_inv] at this

theorem pointwiseContactThresholds_of {ν : Measure ℝ}
    {J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ} {κ : ℝ}
    (hG : 0 < Sandpile.green d 0 0 * κ)
    (htail : ThresholdTailAsymptotics d ν J κ)
    (hrel : ThresholdRelativeError d ν J) :
    PointwiseContactThresholds d ν J κ := by
  refine ⟨?_, ?_⟩
  · have h1 := tendsto_shift_mul htail
    have h2 := h1.div_const (Sandpile.green d 0 0 * κ)
    rwa [div_self hG.ne'] at h2
  · have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) * ((Sandpile.centeredMassLaw d ν)
        {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n < J σ 0}).toReal :=
      htail.eventually (lt_mem_nhds hG)
    have hEn : Tendsto (fun n : ℕ => (n : ℝ) * ((Sandpile.centeredMassLaw d ν)
        (symmDiff {σ | Sandpile.odometer σ (n + 1) 0 = 0}
          {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n < J σ 0})).toReal)
        atTop (𝓝 0) := by
      have hprod := htail.mul hrel
      rw [mul_zero] at hprod
      refine hprod.congr' ?_
      filter_upwards [hpos] with n hn
      have hBne : ((Sandpile.centeredMassLaw d ν)
          {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n < J σ 0}).toReal ≠ 0 := by
        intro h
        rw [h, mul_zero] at hn
        exact lt_irrefl 0 hn
      field_simp
    have h3 := tendsto_shift_mul hEn
    refine h3.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hm1 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
    rw [hm1]

end Sandpile
