/-
The Step-1 upper isolation estimate `eq:dgt4-band-upper-isolation` of
`thm:dgt4-many-limits` (`sandpile.tex:5930-6055`) for the constructed one-site
law: the mass, and the first moment, that the law puts beyond the `k`th band
level are negligible against that band's own weight.

Only the bands above the `k`th and the positive summand contribute; the bands
below are carried by values above `-a_k`, where the integrand vanishes
identically.
-/
import Sandpile.Support.Dgt4ABandLawDensity

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

variable {w0 mu : ℝ} {v : ℝ≥0} {l1 : ℝ} {a w θ : ℕ → ℝ} {m : ℕ → ℕ}

/-- Tilting the Gaussian density by `e^{-x}` shifts its mean. -/
theorem exp_neg_mul_gaussianPDFReal (hv : v ≠ 0) (x : ℝ) :
    Real.exp (-x) * gaussianPDFReal mu v x
      = Real.exp (-mu + (v : ℝ) / 2) * gaussianPDFReal (mu - (v : ℝ)) v x := by
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  simp only [gaussianPDFReal]
  rw [mul_left_comm, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
  congr 1
  field_simp
  ring_nf

theorem integrable_exp_neg_mul_gaussianPDFReal (hv : v ≠ 0) :
    Integrable fun x : ℝ => Real.exp (-x) * gaussianPDFReal mu v x := by
  have := (integrable_gaussianPDFReal (mu - (v : ℝ)) v).const_mul
    (Real.exp (-mu + (v : ℝ) / 2))
  exact this.congr (Filter.Eventually.of_forall fun x =>
    (exp_neg_mul_gaussianPDFReal (mu := mu) hv x).symm)

theorem integral_exp_neg_mul_gaussianPDFReal (hv : v ≠ 0) :
    ∫ x : ℝ, Real.exp (-x) * gaussianPDFReal mu v x = Real.exp (-mu + (v : ℝ) / 2) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    fun x => exp_neg_mul_gaussianPDFReal (mu := mu) hv x), integral_const_mul,
    integral_gaussianPDFReal_eq_one _ hv, mul_one]

/-- The positive part of `-z - c` is below `e^{-(z+c)}`. -/
theorem max_neg_sub_le_exp (c z : ℝ) : max (-z - c) 0 ≤ Real.exp (-(z + c)) := by
  rcases le_or_gt (-z - c) 0 with h | h
  · rw [max_eq_right h]
    exact (Real.exp_pos _).le
  · rw [max_eq_left h.le, show -(z + c) = -z - c by ring]
    have := Real.add_one_le_exp (-z - c)
    linarith


/-- The integrand of the first-moment half of `eq:dgt4-band-upper-isolation`. -/
def upperExcess (c z : ℝ) : ℝ := max (-z - c) 0

lemma upperExcess_nonneg (c z : ℝ) : 0 ≤ upperExcess c z := le_max_right _ _

lemma continuous_upperExcess (c : ℝ) : Continuous (upperExcess c) :=
  (continuous_neg.sub continuous_const).max continuous_const

lemma upperExcess_eq_zero {c z : ℝ} (h : -z ≤ c) : upperExcess c z = 0 :=
  max_eq_right (by linarith)

lemma upperExcess_le {c z d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (h : -z ≤ d) :
    upperExcess c z ≤ d := by
  rcases le_or_gt (-z - c) 0 with hz | hz
  · rw [upperExcess, max_eq_right hz]; exact hd
  · rw [upperExcess, max_eq_left hz.le]; linarith

/-- The positive summand's first moment beyond a level is exponentially small. -/
theorem integrable_gauss_upperExcess (hv : v ≠ 0) (c : ℝ) :
    Integrable fun x : ℝ => gaussianPDFReal mu v x * upperExcess c x := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_gaussianPDFReal (mu := mu) hv).const_mul (Real.exp (-c)))
    (((contDiff_gaussianPDFReal mu v).continuous.mul
      (continuous_upperExcess c)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (gaussianPDFReal_nonneg mu v x) (upperExcess_nonneg c x))]
  have hbound : upperExcess c x ≤ Real.exp (-(x + c)) := max_neg_sub_le_exp c x
  calc gaussianPDFReal mu v x * upperExcess c x
      ≤ gaussianPDFReal mu v x * Real.exp (-(x + c)) :=
        mul_le_mul_of_nonneg_left hbound (gaussianPDFReal_nonneg mu v x)
    _ = Real.exp (-c) * (Real.exp (-x) * gaussianPDFReal mu v x) := by
        rw [show -(x + c) = -x + -c by ring, Real.exp_add]
        ring

theorem integral_gauss_upperExcess_le (hv : v ≠ 0) (c : ℝ) :
    ∫ x : ℝ, gaussianPDFReal mu v x * upperExcess c x
      ≤ Real.exp (-c) * Real.exp (-mu + (v : ℝ) / 2) := by
  have hdom : Integrable fun x : ℝ =>
      Real.exp (-c) * (Real.exp (-x) * gaussianPDFReal mu v x) :=
    (integrable_exp_neg_mul_gaussianPDFReal (mu := mu) hv).const_mul _
  have hmono : ∀ x : ℝ, gaussianPDFReal mu v x * upperExcess c x
      ≤ Real.exp (-c) * (Real.exp (-x) * gaussianPDFReal mu v x) := by
    intro x
    calc gaussianPDFReal mu v x * upperExcess c x
        ≤ gaussianPDFReal mu v x * Real.exp (-(x + c)) :=
          mul_le_mul_of_nonneg_left (max_neg_sub_le_exp c x) (gaussianPDFReal_nonneg mu v x)
      _ = Real.exp (-c) * (Real.exp (-x) * gaussianPDFReal mu v x) := by
          rw [show -(x + c) = -x + -c by ring, Real.exp_add]
          ring
  refine (integral_mono (integrable_gauss_upperExcess hv c) hdom hmono).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_neg_mul_gaussianPDFReal (mu := mu) hv]

/-- Below its own level a band component carries no excess at all. -/
theorem integral_bandComponent_upperExcess_eq_zero {a' θ' : ℝ} {m' : ℕ}
    (hl1 : l1 < 1) (ha : 0 < a') {c : ℝ} (hc : a' ≤ c) :
    ∫ x : ℝ, bandComponent l1 a' θ' m' x * upperExcess c x = 0 := by
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.zero_apply]
  rcases le_or_gt x (-a') with hx | hx
  · rw [bandComponent_eq_zero_of_le hl1 ha hx, zero_mul]
  · rw [upperExcess_eq_zero (by linarith), mul_zero]

/-- Above its own level a band component carries at most its level. -/
theorem integral_bandComponent_upperExcess_le {a' θ' : ℝ} {m' : ℕ} (hθ : 0 < θ') (hm : 0 < m')
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : 0 < a') {c : ℝ} (hc : 0 ≤ c) :
    ∫ x : ℝ, bandComponent l1 a' θ' m' x * upperExcess c x ≤ a' := by
  have hint : Integrable fun x : ℝ => bandComponent l1 a' θ' m' x * upperExcess c x := by
    refine Continuous.integrable_of_hasCompactSupport
      ((contDiff_bandComponent l1 a' θ' m').continuous.mul (continuous_upperExcess c)) ?_
    exact (hasCompactSupport_bandComponent hm hl1 ha).mul_right
  have hdom : Integrable fun x : ℝ => bandComponent l1 a' θ' m' x * a' :=
    (integrable_bandComponent hm hl1 ha).mul_const a'
  have hpt : ∀ x : ℝ, bandComponent l1 a' θ' m' x * upperExcess c x
      ≤ bandComponent l1 a' θ' m' x * a' := by
    intro x
    rcases le_or_gt x (-a') with hx | hx
    · rw [bandComponent_eq_zero_of_le hl1 ha hx, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (upperExcess_le hc ha.le (by linarith))
        (bandComponent_nonneg hθ.le hl1 ha x)
  refine (integral_mono hint hdom hpt).trans (le_of_eq ?_)
  rw [integral_mul_const, integral_bandComponent_eq_one hθ hm hl0 hl1 ha, one_mul]



/-- **The first-moment half of `eq:dgt4-band-upper-isolation`, as an estimate.**
Beyond the `k`th band level only the positive summand and the bands above
contribute. -/
theorem integral_upperExcess_bandLaw_le (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k)
    (hθ : ∀ k, 0 < θ k) (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k)
    (hm : ∀ k, 0 < m k) (hatop : Tendsto a atTop atTop) (hv : v ≠ 0)
    (hwa : Summable fun k => w k * a k) (hmono : Monotone a) (k : ℕ) :
    ∫ z, upperExcess (a k) z ∂(bandLaw w0 mu v l1 a w θ m)
      ≤ w0 * (Real.exp (-(a k)) * Real.exp (-mu + (v : ℝ) / 2))
        + ∑' j : ℕ, w (k + 1 + j) * a (k + 1 + j) := by
  classical
  set h : ℝ → ℝ := upperExcess (a k) with hh
  have hak : 0 ≤ a k := (ha k).le
  -- integrability of each summand
  have hint : ∀ n, Integrable (bandSummand w0 mu v l1 a w θ m h n) := by
    intro n
    cases n with
    | zero =>
      refine ((integrable_gauss_upperExcess (mu := mu) hv (a k)).const_mul w0).congr
        (Filter.Eventually.of_forall fun x => ?_)
      show w0 * (gaussianPDFReal mu v x * h x) = w0 * gaussianPDFReal mu v x * h x
      ring
    | succ j =>
      have hcpt : Integrable fun x : ℝ =>
          bandComponent l1 (a j) (θ j) (m j) x * h x := by
        refine Continuous.integrable_of_hasCompactSupport
          ((contDiff_bandComponent l1 (a j) (θ j) (m j)).continuous.mul
            (continuous_upperExcess (a k))) ?_
        exact (hasCompactSupport_bandComponent (hm j) hl1 (ha j)).mul_right
      refine (hcpt.const_mul (w j)).congr (Filter.Eventually.of_forall fun x => ?_)
      show w j * (bandComponent l1 (a j) (θ j) (m j) x * h x)
        = w j * bandComponent l1 (a j) (θ j) (m j) x * h x
      ring
  -- the summand integrals are nonnegative and dominated by `w j * a j`
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
      (integral_bandComponent_upperExcess_le (hθ j) (hm j) hl0 hl1 (ha j) hak) (hw j)
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
  -- the decomposition
  have hsplit := integral_bandLaw (h := h) hw0 hw (fun k => (hθ k).le) hl0 hl1 ha hm hatop
    hint hnorm
  have hcsum : Summable fun j : ℕ => w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x := by
    have := hnorm
    rw [← summable_nat_add_iff 1] at this
    refine this.congr fun j => ?_
    rw [hnormeq, hFint j]
  have hzero : ∀ j : ℕ, j ≤ k →
      w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x = 0 := by
    intro j hj
    rw [integral_bandComponent_upperExcess_eq_zero hl1 (ha j) (hmono hj), mul_zero]
  have hhead : ∑ j ∈ Finset.range (k + 1),
      w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x = 0 :=
    Finset.sum_eq_zero fun j hj => hzero j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have htail : (∑' j : ℕ, w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x)
      = ∑' i : ℕ, w (i + (k + 1)) *
          ∫ x, bandComponent l1 (a (i + (k + 1))) (θ (i + (k + 1))) (m (i + (k + 1))) x * h x := by
    rw [← hcsum.sum_add_tsum_nat_add (k + 1), hhead, zero_add]
  have hwatail : Summable fun i : ℕ => w (i + (k + 1)) * a (i + (k + 1)) := by
    simpa [Function.comp_def] using hwa.comp_injective (add_left_injective (k + 1))
  have htaille : (∑' i : ℕ, w (i + (k + 1)) *
        ∫ x, bandComponent l1 (a (i + (k + 1))) (θ (i + (k + 1))) (m (i + (k + 1))) x * h x)
      ≤ ∑' j : ℕ, w (k + 1 + j) * a (k + 1 + j) := by
    have hsub : Summable fun i : ℕ => w (i + (k + 1)) *
        ∫ x, bandComponent l1 (a (i + (k + 1))) (θ (i + (k + 1))) (m (i + (k + 1))) x * h x := by
      simpa [Function.comp_def] using hcsum.comp_injective (add_left_injective (k + 1))
    calc (∑' i : ℕ, w (i + (k + 1)) *
          ∫ x, bandComponent l1 (a (i + (k + 1))) (θ (i + (k + 1))) (m (i + (k + 1))) x * h x)
        ≤ ∑' i : ℕ, w (i + (k + 1)) * a (i + (k + 1)) := by
          refine Summable.tsum_le_tsum (fun i => ?_) hsub hwatail
          exact mul_le_mul_of_nonneg_left
            (integral_bandComponent_upperExcess_le (hθ _) (hm _) hl0 hl1 (ha _) hak) (hw _)
      _ = ∑' j : ℕ, w (k + 1 + j) * a (k + 1 + j) :=
          tsum_congr fun i => by rw [show i + (k + 1) = k + 1 + i by omega]
  have hgauss : (∫ x, w0 * gaussianPDFReal mu v x * h x)
      ≤ w0 * (Real.exp (-(a k)) * Real.exp (-mu + (v : ℝ) / 2)) := by
    have hcm : (∫ x, w0 * gaussianPDFReal mu v x * h x)
        = w0 * ∫ x, gaussianPDFReal mu v x * h x := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hcm]
    exact mul_le_mul_of_nonneg_left
      (integral_gauss_upperExcess_le (mu := mu) hv (a k)) hw0
  have hbridge : (∑' j : ℕ, ∫ x, w j * bandComponent l1 (a j) (θ j) (m j) x * h x)
      = ∑' j : ℕ, w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x :=
    tsum_congr fun j => by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hsplit, hbridge, htail]
  linarith [htaille, hgauss]



/-- **`eq:dgt4-band-upper-isolation` for the constructed law.** -/
theorem bandUpperIsolation_law (P : BandParameters) (hA : P.A⁻¹ ≤ P.l1)
    (m : ℕ → ℕ) (hm : ∀ k, 0 < m k) (hmtop : Tendsto (fun k => (m k : ℝ)) atTop atTop)
    (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (htot : ∑' k, P.weight k ≤ 1) :
    BandUpperIsolation P (P.law m mu v) := by
  classical
  have hl0 : 0 < P.l1 := P.hl1.1
  have hl1 : P.l1 < 1 := P.hl1.2
  set w0 : ℝ := 1 - ∑' k, P.weight k with hw0def
  have hw0 : 0 ≤ w0 := by simp only [hw0def]; linarith
  have hmonoP : Monotone P.level := fun i j hij =>
    pow_le_pow_right₀ (le_of_lt P.hA) hij
  have hwa : Summable fun k => P.weight k * P.level k := by
    refine P.summable_level_weight.congr fun k => ?_
    ring
  set C : ℝ := Real.exp (-mu + (v : ℝ) / 2) with hC
  have hC0 : 0 < C := Real.exp_pos _
  refine ⟨bandUpperIsolation_tail_law P hA m hm hmtop mu v hv htot, ?_⟩
  -- the two pieces of the bound
  have hpiece1 : Tendsto (fun k : ℕ =>
      w0 * C / (P.c0 * (1 - P.l1)) / P.level k) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds P.level_tendsto
  have hratio := P.level_weight_tail_ratio_tendsto
  have hpiece2 : Tendsto (fun k : ℕ =>
      (1 - P.l1)⁻¹ * ((∑' j : ℕ, P.level (k + 1 + j) * P.weight (k + 1 + j)) /
        (P.level k * P.weight k))) atTop (𝓝 0) := by
    have := hratio.const_mul (1 - P.l1)⁻¹
    rwa [mul_zero] at this
  have hlim : Tendsto (fun k : ℕ =>
      w0 * C / (P.c0 * (1 - P.l1)) / P.level k
        + (1 - P.l1)⁻¹ * ((∑' j : ℕ, P.level (k + 1 + j) * P.weight (k + 1 + j)) /
            (P.level k * P.weight k))) atTop (𝓝 0) := by
    simpa using hpiece1.add hpiece2
  refine squeeze_zero (fun k => ?_) (fun k => ?_) hlim
  · have hden : 0 < P.weight k * (1 - P.l1) * P.level k := by
      have := P.weight_pos k
      have := P.level_pos k
      positivity
    exact div_nonneg (integral_nonneg fun z => le_max_right _ _) hden.le
  · have hden : 0 < P.weight k * (1 - P.l1) * P.level k := by
      have := P.weight_pos k
      have := P.level_pos k
      positivity
    have hnum := integral_upperExcess_bandLaw_le (w0 := w0) (mu := mu) (v := v) (l1 := P.l1)
      (a := P.level) (w := P.weight) (θ := P.theta) (m := m) hw0
      (fun k => (P.weight_pos k).le) (fun k => lt_of_lt_of_le one_pos (P.htheta k).1)
      hl0 hl1 P.level_pos hm P.level_tendsto hv hwa hmonoP k
    have hstep : (∫ z, upperExcess (P.level k) z ∂(P.law m mu v)) /
        (P.weight k * (1 - P.l1) * P.level k)
        ≤ (w0 * (Real.exp (-(P.level k)) * C)
            + ∑' j : ℕ, P.weight (k + 1 + j) * P.level (k + 1 + j)) /
          (P.weight k * (1 - P.l1) * P.level k) :=
      div_le_div_of_nonneg_right hnum hden.le
    refine le_trans hstep (le_of_eq ?_)
    have hwk : P.weight k = P.c0 * Real.exp (-(P.level k)) := rfl
    have hswap : (∑' j : ℕ, P.weight (k + 1 + j) * P.level (k + 1 + j))
        = ∑' j : ℕ, P.level (k + 1 + j) * P.weight (k + 1 + j) :=
      tsum_congr fun j => mul_comm _ _
    rw [hswap, hwk]
    have he : Real.exp (-(P.level k)) ≠ 0 := Real.exp_ne_zero _
    have hc0 : P.c0 ≠ 0 := P.hc0.ne'
    have hLk : P.level k ≠ 0 := (P.level_pos k).ne'
    have hl1' : (1 : ℝ) - P.l1 ≠ 0 := by linarith
    field_simp

end Sandpile.Support

