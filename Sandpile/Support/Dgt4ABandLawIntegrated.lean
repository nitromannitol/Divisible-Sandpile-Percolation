import Sandpile.Support.Dgt4ABandLawLower
import Sandpile.Support.Dgt4ABandIntegrated

/-!
# Integrated band profile of the constructed law

The integrated band profile `eq:dgt4-band-integrated-profile` for the
constructed one-site law.

`bandIntegratedProfile_of_profile` needs the lower tail of the law to be
integrable past every level, which is the statement that `-ζ(0)` has a finite
mean overshoot above every level.  For the constructed law this is proved here,
from the same summand decomposition that gives the upper isolation: the positive
summand contributes an exponentially small amount and the `j`th band component
contributes at most its own level `a_j`, and `∑_j ω_j a_j < ∞`.

Combining it with `bandProfile_law` and `bandUpperIsolation_law` gives the
integrated profile for the constructed law itself.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

variable {w0 mu : ℝ} {v : ℝ≥0} {l1 : ℝ} {a w θ : ℕ → ℝ} {m : ℕ → ℕ}

/-- The summands of the density, tested against `h`, sum pointwise to the
density times `h`. -/
theorem bandLawDensity_mul_eq_tsum {h : ℝ → ℝ} (hl0 : 0 < l1) (hl1 : l1 < 1)
    (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k) (hatop : Tendsto a atTop atTop) (x : ℝ) :
    Summable (fun n => bandSummand w0 mu v l1 a w θ m h n x) ∧
      bandLawDensity w0 mu v l1 a w θ m x * h x
        = ∑' n, bandSummand w0 mu v l1 a w θ m h n x := by
  have hfin : Summable fun k => w k * bandComponent l1 (a k) (θ k) (m k) x * h x := by
    obtain ⟨s, hs⟩ := bandComponent_finite_support (w := w) (θ := θ) hl0 hl1 ha hm hatop x
    refine summable_of_ne_finset_zero (s := s) fun k hk => ?_
    rw [hs k hk, zero_mul]
  have hsumF : Summable fun n => bandSummand w0 mu v l1 a w θ m h n x := by
    rw [← summable_nat_add_iff 1]
    exact hfin
  refine ⟨hsumF, ?_⟩
  rw [hsumF.tsum_eq_zero_add]
  have h0 : bandSummand w0 mu v l1 a w θ m h 0 x = w0 * gaussianPDFReal mu v x * h x := rfl
  have hs : ∀ k : ℕ, bandSummand w0 mu v l1 a w θ m h (k + 1) x
      = w k * bandComponent l1 (a k) (θ k) (m k) x * h x := fun k => rfl
  rw [h0, show (∑' k : ℕ, bandSummand w0 mu v l1 a w θ m h (k + 1) x)
      = ∑' k : ℕ, w k * bandComponent l1 (a k) (θ k) (m k) x * h x from tsum_congr hs]
  rw [bandLawDensity, add_mul, tsum_mul_right]

/-- **Integrability against the one-site law from integrability of the
summands**, for a nonnegative test function. -/
theorem integrable_bandLaw_of_nonneg {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x)
    (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 ≤ θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hmeas : AEStronglyMeasurable h volume)
    (hint : ∀ n, Integrable (bandSummand w0 mu v l1 a w θ m h n))
    (hnorm : Summable fun n => ∫ x, ‖bandSummand w0 mu v l1 a w θ m h n x‖) :
    Integrable h (bandLaw w0 mu v l1 a w θ m) := by
  classical
  set F : ℕ → ℝ → ℝ := bandSummand w0 mu v l1 a w θ m h with hFdef
  have hFnn : ∀ n x, 0 ≤ F n x := by
    intro n x
    cases n with
    | zero => exact mul_nonneg (mul_nonneg hw0 (gaussianPDFReal_nonneg mu v x)) (hh x)
    | succ j =>
      exact mul_nonneg (mul_nonneg (hw j)
        (bandComponent_nonneg (hθ j) hl1 (ha j) x)) (hh x)
  have hnormeq : ∀ n, ∫ x, ‖F n x‖ = ∫ x, F n x := by
    intro n
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖F n x‖ = F n x
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn n x)]
  have hsumI : Summable fun n => ∫ x, F n x := hnorm.congr hnormeq
  have hInn : ∀ n, 0 ≤ ∫ x, F n x := fun n => integral_nonneg fun x => hFnn n x
  -- the density times `h` is integrable on the line
  have hdensnn : ∀ x, 0 ≤ bandLawDensity w0 mu v l1 a w θ m x * h x := fun x =>
    mul_nonneg (bandLawDensity_pos_of_nonneg hw0 hθ hw hl1 ha x) (hh x)
  have hprod : Integrable (fun x => bandLawDensity w0 mu v l1 a w θ m x * h x) volume := by
    refine ⟨((contDiff_bandLawDensity hl0 hl1 ha hm hatop).continuous.measurable
      (f := bandLawDensity w0 mu v l1 a w θ m)).aestronglyMeasurable.mul hmeas, ?_⟩
    refine (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hdensnn)).mpr ?_
    have hrw : ∀ x : ℝ, ENNReal.ofReal (bandLawDensity w0 mu v l1 a w θ m x * h x)
        = ∑' n, ENNReal.ofReal (F n x) := by
      intro x
      obtain ⟨hsx, heq⟩ := bandLawDensity_mul_eq_tsum (w0 := w0) (mu := mu) (v := v)
        (w := w) (θ := θ) (h := h) hl0 hl1 ha hm hatop x
      rw [heq, ENNReal.ofReal_tsum_of_nonneg (fun n => hFnn n x) hsx]
    rw [lintegral_congr hrw,
      lintegral_tsum fun n => ((hint n).1.aemeasurable.ennreal_ofReal)]
    have hval : ∀ n, ∫⁻ x, ENNReal.ofReal (F n x) = ENNReal.ofReal (∫ x, F n x) := fun n =>
      (ofReal_integral_eq_lintegral_ofReal (hint n)
        (Filter.Eventually.of_forall (hFnn n))).symm
    rw [tsum_congr hval, ← ENNReal.ofReal_tsum_of_nonneg hInn hsumI]
    exact ENNReal.ofReal_lt_top
  -- transport to the law
  have hmeasf : Measurable fun x => ENNReal.ofReal (bandLawDensity w0 mu v l1 a w θ m x) :=
    ((contDiff_bandLawDensity hl0 hl1 ha hm hatop).continuous.measurable).ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume : Measure ℝ),
      ENNReal.ofReal (bandLawDensity w0 mu v l1 a w θ m x) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [bandLaw, integrable_withDensity_iff hmeasf hlt]
  refine hprod.congr (Filter.Eventually.of_forall fun x => ?_)
  show bandLawDensity w0 mu v l1 a w θ m x * h x
      = h x * (ENNReal.ofReal (bandLawDensity w0 mu v l1 a w θ m x)).toReal
  rw [ENNReal.toReal_ofReal (bandLawDensity_pos_of_nonneg hw0 hθ hw hl1 ha x), mul_comm]

/-- **The mean overshoot of `-ζ(0)` above a nonnegative level is finite.** -/
theorem integrable_upperExcess_bandLaw (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k)
    (hθ : ∀ k, 0 < θ k) (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k)
    (hm : ∀ k, 0 < m k) (hatop : Tendsto a atTop atTop) (hv : v ≠ 0)
    (hwa : Summable fun k => w k * a k) {c : ℝ} (hc : 0 ≤ c) :
    Integrable (upperExcess c) (bandLaw w0 mu v l1 a w θ m) := by
  classical
  set h : ℝ → ℝ := upperExcess c with hh
  have hint : ∀ n, Integrable (bandSummand w0 mu v l1 a w θ m h n) := by
    intro n
    cases n with
    | zero =>
      refine ((integrable_gauss_upperExcess (mu := mu) hv c).const_mul w0).congr
        (Filter.Eventually.of_forall fun x => ?_)
      show w0 * (gaussianPDFReal mu v x * h x) = w0 * gaussianPDFReal mu v x * h x
      ring
    | succ j =>
      have hcpt : Integrable fun x : ℝ =>
          bandComponent l1 (a j) (θ j) (m j) x * h x := by
        refine Continuous.integrable_of_hasCompactSupport
          ((contDiff_bandComponent l1 (a j) (θ j) (m j)).continuous.mul
            (continuous_upperExcess c)) ?_
        exact (hasCompactSupport_bandComponent (hm j) hl1 (ha j)).mul_right
      refine (hcpt.const_mul (w j)).congr (Filter.Eventually.of_forall fun x => ?_)
      show w j * (bandComponent l1 (a j) (θ j) (m j) x * h x)
        = w j * bandComponent l1 (a j) (θ j) (m j) x * h x
      ring
  have hFnn : ∀ n x, 0 ≤ bandSummand w0 mu v l1 a w θ m h n x := by
    intro n x
    cases n with
    | zero =>
      exact mul_nonneg (mul_nonneg hw0 (gaussianPDFReal_nonneg mu v x)) (upperExcess_nonneg _ _)
    | succ j =>
      exact mul_nonneg (mul_nonneg (hw j)
        (bandComponent_nonneg (hθ j).le hl1 (ha j) x)) (upperExcess_nonneg _ _)
  have hFint : ∀ j : ℕ, ∫ x, bandSummand w0 mu v l1 a w θ m h (j + 1) x
      = w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x := by
    intro j
    rw [show (fun x => bandSummand w0 mu v l1 a w θ m h (j + 1) x)
        = fun x => w j * (bandComponent l1 (a j) (θ j) (m j) x * h x) from by
      funext x; show w j * bandComponent l1 (a j) (θ j) (m j) x * h x = _; ring]
    exact integral_const_mul _ _
  have hFle : ∀ j : ℕ, ∫ x, bandSummand w0 mu v l1 a w θ m h (j + 1) x ≤ w j * a j := by
    intro j
    rw [hFint j]
    exact mul_le_mul_of_nonneg_left
      (integral_bandComponent_upperExcess_le (hθ j) (hm j) hl0 hl1 (ha j) hc) (hw j)
  have hnormeq : ∀ n, ∫ x, ‖bandSummand w0 mu v l1 a w θ m h n x‖
      = ∫ x, bandSummand w0 mu v l1 a w θ m h n x := by
    intro n
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖bandSummand w0 mu v l1 a w θ m h n x‖ = bandSummand w0 mu v l1 a w θ m h n x
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn n x)]
  have hnorm : Summable fun n => ∫ x, ‖bandSummand w0 mu v l1 a w θ m h n x‖ := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hwa
    · rw [hnormeq]
      exact integral_nonneg fun x => hFnn _ x
    · rw [hnormeq]
      exact hFle j
  exact integrable_bandLaw_of_nonneg (upperExcess_nonneg c) hw0 hw (fun k => (hθ k).le)
    hl0 hl1 ha hm hatop (continuous_upperExcess c).aestronglyMeasurable hint hnorm

/-- The mean overshoot above an arbitrary level, positive or negative, is
finite: the overshoot above `c` is below the overshoot above `0` plus `|c|`. -/
theorem integrable_posPart_bandLaw (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k)
    (hθ : ∀ k, 0 < θ k) (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k)
    (hm : ∀ k, 0 < m k) (hatop : Tendsto a atTop atTop) (hv : v ≠ 0)
    (hsum : Summable w) (htot : w0 + ∑' k, w k = 1)
    (hwa : Summable fun k => w k * a k) (c : ℝ) :
    Integrable (fun z : ℝ => max (-z - c) 0) (bandLaw w0 mu v l1 a w θ m) := by
  haveI : IsProbabilityMeasure (bandLaw w0 mu v l1 a w θ m) :=
    isProbabilityMeasure_bandLaw hw0 hw hθ hl0 hl1 ha hm hatop hv hsum htot
  have h0 := integrable_upperExcess_bandLaw (mu := mu) (v := v) hw0 hw hθ hl0 hl1 ha hm hatop hv
    hwa (c := 0) le_rfl
  refine Integrable.mono' (h0.add (integrable_const |c|))
    ((continuous_upperExcess c).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have h1 : max (-z - c) 0 ≤ max (-z - 0) 0 + |c| := by
    rcases le_or_gt (-z - c) 0 with hz | hz
    · rw [max_eq_right hz]
      positivity
    · rw [max_eq_left hz.le]
      have h2 : -z - 0 ≤ max (-z - 0) 0 := le_max_left _ _
      have h3 : -c ≤ |c| := neg_le_abs c
      linarith
  exact h1

/-- **The lower tail of the constructed law is integrable past every level.** -/
theorem integrableOn_lowerTail_bandLaw (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k)
    (hθ : ∀ k, 0 < θ k) (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k)
    (hm : ∀ k, 0 < m k) (hatop : Tendsto a atTop atTop) (hv : v ≠ 0)
    (hsum : Summable w) (htot : w0 + ∑' k, w k = 1)
    (hwa : Summable fun k => w k * a k) (t : ℝ) :
    IntegrableOn (LatticeProb.lowerTail (bandLaw w0 mu v l1 a w θ m)) (Ioi t) := by
  haveI : IsProbabilityMeasure (bandLaw w0 mu v l1 a w θ m) :=
    isProbabilityMeasure_bandLaw hw0 hw hθ hl0 hl1 ha hm hatop hv hsum htot
  exact integrableOn_lowerTail_of_integrable
    (integrable_posPart_bandLaw hw0 hw hθ hl0 hl1 ha hm hatop hv hsum htot hwa t)

/-- **The integrated band profile of the constructed law**
(`eq:dgt4-band-integrated-profile`). -/
theorem bandIntegratedProfile_law (P : BandParameters) (hA : P.A⁻¹ ≤ P.l1)
    (m : ℕ → ℕ) (hm : ∀ k, 0 < m k) (hmtop : Tendsto (fun k => (m k : ℝ)) atTop atTop)
    (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (htot : ∑' k, P.weight k ≤ 1) :
    BandIntegratedProfile P (P.law m mu v) := by
  have hl0 : 0 < P.l1 := P.hl1.1
  have hl1 : P.l1 < 1 := P.hl1.2
  have hw0 : 0 ≤ 1 - ∑' k, P.weight k := by linarith
  have hwtot : (1 - ∑' k, P.weight k) + ∑' k, P.weight k = 1 := by ring
  have hwa : Summable fun k => P.weight k * P.level k := by
    simpa only [mul_comm] using P.summable_level_weight
  haveI : IsProbabilityMeasure (P.law m mu v) :=
    isProbabilityMeasure_bandLaw hw0 (fun k => (P.weight_pos k).le)
      (fun k => lt_of_lt_of_le one_pos (P.htheta k).1) hl0 hl1 P.level_pos hm P.level_tendsto
      hv P.summable_weight hwtot
  refine bandIntegratedProfile_of_profile P (P.law m mu v) ?_
    (bandProfile_law P hA m hm hmtop mu v hv htot)
    (bandUpperIsolation_law P hA m hm hmtop mu v hv htot)
  intro t
  exact integrableOn_lowerTail_bandLaw hw0 (fun k => (P.weight_pos k).le)
    (fun k => lt_of_lt_of_le one_pos (P.htheta k).1) hl0 hl1 P.level_pos hm P.level_tendsto
    hv P.summable_weight hwtot hwa t

end Sandpile.Support
