import Sandpile.Support.Dgt4ABandLawUpper

/-!
# The Step-1 lower isolation estimate for the constructed law

The Step-1 lower isolation estimate `eq:dgt4-band-lower-isolation` of `thm:dgt4-many-limits`
(`sandpile.tex:5930-6055`) for the constructed one-site law, proved as
`bandLowerIsolation_law` and bundled with the rest of Step 1 as `bandLawProfile_law`.

Below the `k`th band level the `k`th component and every band above it contribute nothing at
all, since they are carried strictly below that level
(`integral_bandComponent_lowerTail_eq_zero`, `bandComponent_mul_lowerTail_eq_zero`). What is
left is the positive summand, whose exponential moment is finite
(`integral_gauss_lowerTail_le`), and the finitely many bands below, each bounded via
`integral_bandComponent_lowerTail_le` and damped by the parameter inequality
`1 - λ₀ℓ₁ + (λ₀-1)/A < 0`; these two pieces are combined in `integral_lowerTail_bandLaw_le`,
and `tendsto_nat_mul_exp_neg_pow` handles the resulting `k e^{-cA^k} → 0` limit.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

variable {w0 mu : ℝ} {v : ℝ≥0} {l1 : ℝ} {a w θ : ℕ → ℝ} {m : ℕ → ℕ}

/-- Tilting the Gaussian density by `e^{-λx}` shifts its mean. -/
theorem exp_neg_lam_mul_gaussianPDFReal (hv : v ≠ 0) (lam x : ℝ) :
    Real.exp (-(lam * x)) * gaussianPDFReal mu v x
      = Real.exp (-(lam * mu) + lam ^ 2 * (v : ℝ) / 2) *
          gaussianPDFReal (mu - lam * (v : ℝ)) v x := by
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  simp only [gaussianPDFReal]
  rw [mul_left_comm, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
  congr 1
  field_simp
  ring_nf

/-- The exponentially tilted Gaussian density is integrable: `exp_neg_lam_mul_gaussianPDFReal`
rewrites it as a constant multiple of the Gaussian density with shifted mean `mu - lam * v`,
which is integrable. -/
theorem integrable_exp_neg_lam_mul_gaussianPDFReal (hv : v ≠ 0) (lam : ℝ) :
    Integrable fun x : ℝ => Real.exp (-(lam * x)) * gaussianPDFReal mu v x := by
  have h := (integrable_gaussianPDFReal (mu - lam * (v : ℝ)) v).const_mul
    (Real.exp (-(lam * mu) + lam ^ 2 * (v : ℝ) / 2))
  exact h.congr (Filter.Eventually.of_forall fun x =>
    (exp_neg_lam_mul_gaussianPDFReal (mu := mu) hv lam x).symm)

/-- The integral of the exponentially tilted Gaussian density: `exp_neg_lam_mul_gaussianPDFReal`
reduces it to the total mass of the shifted Gaussian density, which is `1`
(`integral_gaussianPDFReal_eq_one`). -/
theorem integral_exp_neg_lam_mul_gaussianPDFReal (hv : v ≠ 0) (lam : ℝ) :
    ∫ x : ℝ, Real.exp (-(lam * x)) * gaussianPDFReal mu v x
      = Real.exp (-(lam * mu) + lam ^ 2 * (v : ℝ) / 2) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    fun x => exp_neg_lam_mul_gaussianPDFReal (mu := mu) hv lam x), integral_const_mul,
    integral_gaussianPDFReal_eq_one _ hv, mul_one]

/-- The integrand of `eq:dgt4-band-lower-isolation`. -/
def lowerTail (lam c z : ℝ) : ℝ :=
  Real.exp (-(lam * z)) * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z

/-- `lowerTail` is nonnegative, being a product of a positive exponential and an
`{0, 1}`-valued indicator. -/
lemma lowerTail_nonneg (lam c z : ℝ) : 0 ≤ lowerTail lam c z :=
  mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- `lowerTail` is dominated by the bare exponential weight `Real.exp (-(lam * z))`, since the
indicator factor is at most `1`. -/
lemma lowerTail_le (lam c z : ℝ) : lowerTail lam c z ≤ Real.exp (-(lam * z)) := by
  rw [lowerTail]
  nth_rewrite 2 [← mul_one (Real.exp (-(lam * z)))]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  by_cases h : z ∈ {z : ℝ | -z ≤ c}
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]
    norm_num

/-- `lowerTail lam c z` vanishes once `z` lies below the threshold `-c`, i.e. `c < -z`, since
the indicator is then zero. -/
lemma lowerTail_eq_zero {lam c z : ℝ} (h : c < -z) : lowerTail lam c z = 0 := by
  rw [lowerTail, Set.indicator_of_notMem (by simpa using not_le.mpr h), mul_zero]

/-- `lowerTail lam c` is measurable, being a product of the measurable exponential map and the
indicator of the measurable set `{z | -z ≤ c}`. -/
lemma measurable_lowerTail (lam c : ℝ) : Measurable (lowerTail lam c) := by
  unfold lowerTail
  refine Measurable.mul ?_ ?_
  · exact Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)
  · exact measurable_const.indicator (measurableSet_le measurable_neg measurable_const)

/-- The positive summand's contribution is its exponential moment. -/
theorem integrable_gauss_lowerTail (hv : v ≠ 0) (lam c : ℝ) :
    Integrable fun x : ℝ => gaussianPDFReal mu v x * lowerTail lam c x := by
  refine Integrable.mono' (integrable_exp_neg_lam_mul_gaussianPDFReal (mu := mu) hv lam)
    (((contDiff_gaussianPDFReal mu v).continuous.measurable.mul
      (measurable_lowerTail lam c)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (gaussianPDFReal_nonneg mu v x) (lowerTail_nonneg lam c x))]
  calc gaussianPDFReal mu v x * lowerTail lam c x
      ≤ gaussianPDFReal mu v x * Real.exp (-(lam * x)) :=
        mul_le_mul_of_nonneg_left (lowerTail_le lam c x) (gaussianPDFReal_nonneg mu v x)
    _ = Real.exp (-(lam * x)) * gaussianPDFReal mu v x := mul_comm _ _

/-- The exponential-moment bound on the positive summand's lower-tail contribution: the
pointwise bound `lowerTail_le` and `integral_exp_neg_lam_mul_gaussianPDFReal` give the same
exponential-moment bound as `integrable_gauss_lowerTail` establishes integrability for. -/
theorem integral_gauss_lowerTail_le (hv : v ≠ 0) (lam c : ℝ) :
    ∫ x : ℝ, gaussianPDFReal mu v x * lowerTail lam c x
      ≤ Real.exp (-(lam * mu) + lam ^ 2 * (v : ℝ) / 2) := by
  have hmono : ∀ x : ℝ, gaussianPDFReal mu v x * lowerTail lam c x
      ≤ Real.exp (-(lam * x)) * gaussianPDFReal mu v x := by
    intro x
    calc gaussianPDFReal mu v x * lowerTail lam c x
        ≤ gaussianPDFReal mu v x * Real.exp (-(lam * x)) :=
          mul_le_mul_of_nonneg_left (lowerTail_le lam c x) (gaussianPDFReal_nonneg mu v x)
      _ = Real.exp (-(lam * x)) * gaussianPDFReal mu v x := mul_comm _ _
  refine (integral_mono (integrable_gauss_lowerTail hv lam c)
    (integrable_exp_neg_lam_mul_gaussianPDFReal (mu := mu) hv lam) hmono).trans (le_of_eq ?_)
  exact integral_exp_neg_lam_mul_gaussianPDFReal (mu := mu) hv lam

/-- A band at or above the level contributes nothing below it. -/
theorem integral_bandComponent_lowerTail_eq_zero {a' θ' : ℝ} {m' : ℕ} (hm : 0 < m')
    (hl1 : l1 < 1) (ha : 0 < a') {lam c : ℝ} (hc : c ≤ l1 * a') :
    ∫ x : ℝ, bandComponent l1 a' θ' m' x * lowerTail lam c x = 0 := by
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.zero_apply]
  rcases le_or_gt (-(l1 * a')) x with hx | hx
  · rw [bandComponent_eq_zero_of_ge hm hl1 ha hx, zero_mul]
  · rw [lowerTail_eq_zero (by linarith), mul_zero]

/-- A band below the level contributes at most `e^{λ a}`. -/
theorem integral_bandComponent_lowerTail_le {a' θ' : ℝ} {m' : ℕ} (hθ : 0 < θ') (hm : 0 < m')
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : 0 < a') {lam : ℝ} (hlam : 0 ≤ lam) (c : ℝ) :
    ∫ x : ℝ, bandComponent l1 a' θ' m' x * lowerTail lam c x ≤ Real.exp (lam * a') := by
  have hint : Integrable fun x : ℝ => bandComponent l1 a' θ' m' x * lowerTail lam c x := by
    have hg : Integrable fun x : ℝ => Real.exp (lam * a') * bandComponent l1 a' θ' m' x :=
      (integrable_bandComponent hm hl1 ha).const_mul _
    refine hg.mono' (((contDiff_bandComponent l1 a' θ' m').continuous.measurable.mul
      (measurable_lowerTail lam c)).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (bandComponent_nonneg hθ.le hl1 ha x) (lowerTail_nonneg lam c x))]
    rcases le_or_gt x (-a') with hx | hx
    · rw [bandComponent_eq_zero_of_le hl1 ha hx, zero_mul]
      positivity
    · rw [mul_comm (Real.exp (lam * a'))]
      refine mul_le_mul_of_nonneg_left ?_ (bandComponent_nonneg hθ.le hl1 ha x)
      refine (lowerTail_le lam c x).trans (Real.exp_le_exp.mpr ?_)
      nlinarith
  have hdom : Integrable fun x : ℝ =>
      bandComponent l1 a' θ' m' x * Real.exp (lam * a') :=
    (integrable_bandComponent hm hl1 ha).mul_const _
  have hpt : ∀ x : ℝ, bandComponent l1 a' θ' m' x * lowerTail lam c x
      ≤ bandComponent l1 a' θ' m' x * Real.exp (lam * a') := by
    intro x
    rcases le_or_gt x (-a') with hx | hx
    · rw [bandComponent_eq_zero_of_le hl1 ha hx, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (bandComponent_nonneg hθ.le hl1 ha x)
      refine (lowerTail_le lam c x).trans (Real.exp_le_exp.mpr ?_)
      nlinarith
  refine (integral_mono hint hdom hpt).trans (le_of_eq ?_)
  rw [integral_mul_const, integral_bandComponent_eq_one hθ hm hl0 hl1 ha, one_mul]


/-- The pointwise, non-integral form of `integral_bandComponent_lowerTail_eq_zero`: a band
component supported at or above the level `l1 * a'` and the lower-tail weight below the
threshold `c ≤ l1 * a'` never overlap, so their product vanishes at every point. -/
lemma bandComponent_mul_lowerTail_eq_zero {a' θ' : ℝ} {m' : ℕ} (hm : 0 < m')
    (hl1 : l1 < 1) (ha : 0 < a') {lam c : ℝ} (hc : c ≤ l1 * a') (x : ℝ) :
    bandComponent l1 a' θ' m' x * lowerTail lam c x = 0 := by
  rcases le_or_gt (-(l1 * a')) x with hx | hx
  · rw [bandComponent_eq_zero_of_ge hm hl1 ha hx, zero_mul]
  · rw [lowerTail_eq_zero (by linarith), mul_zero]

/-- **The Step-1 lower isolation estimate.**  Below the `k`th band level only the
positive summand and the finitely many bands below it contribute. -/
theorem integral_lowerTail_bandLaw_le (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k)
    (hθ : ∀ k, 0 < θ k) (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k)
    (hm : ∀ k, 0 < m k) (hatop : Tendsto a atTop atTop) (hv : v ≠ 0)
    {lam : ℝ} (hlam : 0 ≤ lam) (hmono : Monotone a) (k : ℕ) :
    ∫ z, lowerTail lam (l1 * a k) z ∂(bandLaw w0 mu v l1 a w θ m)
      ≤ w0 * Real.exp (-(lam * mu) + lam ^ 2 * (v : ℝ) / 2)
        + ∑ j ∈ Finset.range k, w j * Real.exp (lam * a j) := by
  classical
  set h : ℝ → ℝ := lowerTail lam (l1 * a k) with hh
  have hkill : ∀ j : ℕ, k ≤ j → ∀ x : ℝ,
      bandComponent l1 (a j) (θ j) (m j) x * h x = 0 := by
    intro j hj x
    exact bandComponent_mul_lowerTail_eq_zero (hm j) hl1 (ha j)
      (mul_le_mul_of_nonneg_left (hmono hj) hl0.le) x
  have hint : ∀ n, Integrable (bandSummand w0 mu v l1 a w θ m h n) := by
    intro n
    cases n with
    | zero =>
      refine ((integrable_gauss_lowerTail (mu := mu) hv lam (l1 * a k)).const_mul w0).congr
        (Filter.Eventually.of_forall fun x => ?_)
      show w0 * (gaussianPDFReal mu v x * h x) = w0 * gaussianPDFReal mu v x * h x
      ring
    | succ j =>
      have hcpt : Integrable fun x : ℝ =>
          bandComponent l1 (a j) (θ j) (m j) x * h x := by
        have hg : Integrable fun x : ℝ =>
            Real.exp (lam * a j) * bandComponent l1 (a j) (θ j) (m j) x :=
          (integrable_bandComponent (hm j) hl1 (ha j)).const_mul _
        refine hg.mono' (((contDiff_bandComponent l1 (a j) (θ j) (m j)).continuous.measurable.mul
          (measurable_lowerTail lam (l1 * a k))).aestronglyMeasurable) ?_
        refine Filter.Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
          (bandComponent_nonneg (hθ j).le hl1 (ha j) x) (lowerTail_nonneg _ _ x))]
        rcases le_or_gt x (-(a j)) with hx | hx
        · rw [bandComponent_eq_zero_of_le hl1 (ha j) hx, zero_mul]
          positivity
        · rw [mul_comm (Real.exp (lam * a j))]
          refine mul_le_mul_of_nonneg_left ?_ (bandComponent_nonneg (hθ j).le hl1 (ha j) x)
          refine (lowerTail_le lam (l1 * a k) x).trans (Real.exp_le_exp.mpr ?_)
          nlinarith
      refine (hcpt.const_mul (w j)).congr (Filter.Eventually.of_forall fun x => ?_)
      show w j * (bandComponent l1 (a j) (θ j) (m j) x * h x)
        = w j * bandComponent l1 (a j) (θ j) (m j) x * h x
      ring
  have hFnn : ∀ n x, 0 ≤ bandSummand w0 mu v l1 a w θ m h n x := by
    intro n x
    cases n with
    | zero =>
      exact mul_nonneg (mul_nonneg hw0 (gaussianPDFReal_nonneg mu v x)) (lowerTail_nonneg _ _ x)
    | succ j =>
      exact mul_nonneg (mul_nonneg (hw j)
        (bandComponent_nonneg (hθ j).le hl1 (ha j) x)) (lowerTail_nonneg _ _ x)
  have hFint : ∀ j : ℕ, ∫ x, bandSummand w0 mu v l1 a w θ m h (j + 1) x
      = w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x := by
    intro j
    rw [show (fun x => bandSummand w0 mu v l1 a w θ m h (j + 1) x)
        = fun x => w j * (bandComponent l1 (a j) (θ j) (m j) x * h x) from by
      funext x; show w j * bandComponent l1 (a j) (θ j) (m j) x * h x = _; ring]
    exact integral_const_mul _ _
  have hFzero : ∀ n : ℕ, k + 1 ≤ n → ∫ x, ‖bandSummand w0 mu v l1 a w θ m h n x‖ = 0 := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have hjk : k ≤ j := by omega
    have : ∀ x : ℝ, ‖bandSummand w0 mu v l1 a w θ m h (j + 1) x‖ = 0 := by
      intro x
      show ‖w j * bandComponent l1 (a j) (θ j) (m j) x * h x‖ = 0
      rw [mul_assoc, hkill j hjk x, mul_zero, norm_zero]
    simp only [this, integral_zero]
  have hnorm : Summable fun n => ∫ x, ‖bandSummand w0 mu v l1 a w θ m h n x‖ := by
    refine summable_of_ne_finset_zero (s := Finset.range (k + 1)) fun n hn => ?_
    have hn' : k + 1 ≤ n := by
      by_contra hc
      exact hn (Finset.mem_range.mpr (not_le.mp hc))
    exact hFzero n hn' 
  have hsplit := integral_bandLaw (h := h) hw0 hw (fun k => (hθ k).le) hl0 hl1 ha hm hatop
    hint hnorm
  have hcsum : Summable fun j : ℕ => w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x := by
    refine summable_of_ne_finset_zero (s := Finset.range k) fun j hj => ?_
    have hjk : k ≤ j := by
      by_contra hc
      exact hj (Finset.mem_range.mpr (not_le.mp hc))
    have : (∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x) = 0 := by
      simp only [hkill j hjk, integral_zero]
    rw [this, mul_zero]
  have htailzero : (∑' i : ℕ, w (i + k) *
      ∫ x, bandComponent l1 (a (i + k)) (θ (i + k)) (m (i + k)) x * h x) = 0 := by
    have hz : ∀ i : ℕ, w (i + k) *
        ∫ x, bandComponent l1 (a (i + k)) (θ (i + k)) (m (i + k)) x * h x = 0 := by
      intro i
      have hzi : (∫ x, bandComponent l1 (a (i + k)) (θ (i + k)) (m (i + k)) x * h x) = 0 := by
        simp only [hkill _ (Nat.le_add_left k i), integral_zero]
      rw [hzi, mul_zero]
    simp only [hz, tsum_zero]
  have hhead : (∑' j : ℕ, w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x)
      = ∑ j ∈ Finset.range k, w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x := by
    rw [← hcsum.sum_add_tsum_nat_add k, htailzero, add_zero]
  have hbridge : (∑' j : ℕ, ∫ x, w j * bandComponent l1 (a j) (θ j) (m j) x * h x)
      = ∑' j : ℕ, w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x :=
    tsum_congr fun j => by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hgauss : (∫ x, w0 * gaussianPDFReal mu v x * h x)
      ≤ w0 * Real.exp (-(lam * mu) + lam ^ 2 * (v : ℝ) / 2) := by
    have hcm : (∫ x, w0 * gaussianPDFReal mu v x * h x)
        = w0 * ∫ x, gaussianPDFReal mu v x * h x := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hcm]
    exact mul_le_mul_of_nonneg_left
      (integral_gauss_lowerTail_le (mu := mu) hv lam (l1 * a k)) hw0
  have hheadle : (∑ j ∈ Finset.range k, w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x)
      ≤ ∑ j ∈ Finset.range k, w j * Real.exp (lam * a j) := by
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_left
      (integral_bandComponent_lowerTail_le (hθ j) (hm j) hl0 hl1 (ha j) hlam _) (hw j)
  rw [hsplit, hbridge, hhead]
  linarith [hgauss, hheadle]



/-- `k e^{-c A^k} → 0` for `A > 1` and `c > 0`. -/
lemma tendsto_nat_mul_exp_neg_pow {A c : ℝ} (hA : 1 < A) (hc : 0 < c) :
    Tendsto (fun k : ℕ => (k : ℝ) * Real.exp (-(c * A ^ k))) atTop (𝓝 0) := by
  set r : ℝ := Real.exp (-(c * (A - 1))) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    nlinarith
  have hgeom : Tendsto (fun k : ℕ => (k : ℝ) * r ^ k) atTop (𝓝 0) := by
    have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr0]
    have hs := (summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm).of_norm
    simpa using hs.tendsto_atTop_zero
  have hbig := hgeom.const_mul (Real.exp (-c))
  rw [mul_zero] at hbig
  refine squeeze_zero (fun k => by positivity) (fun k => ?_) hbig
  have hbern : 1 + (k : ℝ) * (A - 1) ≤ A ^ k := by
    have := one_add_mul_le_pow (a := A - 1) (by linarith) k
    rwa [show 1 + (A - 1) = A by ring] at this
  have hexp : Real.exp (-(c * A ^ k)) ≤ Real.exp (-c) * r ^ k := by
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  calc (k : ℝ) * Real.exp (-(c * A ^ k))
      ≤ (k : ℝ) * (Real.exp (-c) * r ^ k) :=
        mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg k)
    _ = Real.exp (-c) * ((k : ℝ) * r ^ k) := by ring

/-- **`eq:dgt4-band-lower-isolation` for the constructed law.** -/
theorem bandLowerIsolation_law (P : BandParameters) (hlam1 : 1 < P.lam0 * P.l1)
    (hparam : 1 - P.lam0 * P.l1 + (P.lam0 - 1) / P.A < 0)
    (m : ℕ → ℕ) (hm : ∀ k, 0 < m k) (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (htot : ∑' k, P.weight k ≤ 1) :
    BandLowerIsolation P (P.law m mu v) := by
  classical
  have hl0 : 0 < P.l1 := P.hl1.1
  have hl1 : P.l1 < 1 := P.hl1.2
  have hA1 : (1 : ℝ) < P.A := P.hA
  have hA0 : (0 : ℝ) < P.A := zero_lt_one.trans hA1
  have hlam0 : 0 < P.lam0 := P.hlam0
  have hlamgt : 1 < P.lam0 := by nlinarith
  set w0 : ℝ := 1 - ∑' k, P.weight k with hw0def
  have hw0 : 0 ≤ w0 := by simp only [hw0def]; linarith
  have hmonoP : Monotone P.level := fun i j hij => pow_le_pow_right₀ hA1.le hij
  set M : ℝ := Real.exp (-(P.lam0 * mu) + P.lam0 ^ 2 * (v : ℝ) / 2) with hM
  have hM0 : 0 < M := Real.exp_pos _
  set c2 : ℝ := P.lam0 * P.l1 - 1 - (P.lam0 - 1) / P.A with hc2
  have hc2pos : 0 < c2 := by rw [hc2]; linarith
  -- the two pieces of the bound
  have hE1 : Tendsto (fun k : ℕ =>
      w0 * M / P.c0 * Real.exp (-((P.lam0 * P.l1 - 1) * P.level k))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k : ℕ => Real.exp (-((P.lam0 * P.l1 - 1) * P.level k)))
        atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (P.level_tendsto.const_mul_atTop (by linarith : 0 < P.lam0 * P.l1 - 1)))
    have := hlim.const_mul (w0 * M / P.c0)
    rwa [mul_zero] at this
  have hE2 : Tendsto (fun k : ℕ => (k : ℝ) * Real.exp (-(c2 * P.level k))) atTop (𝓝 0) :=
    tendsto_nat_mul_exp_neg_pow hA1 hc2pos
  have hlim : Tendsto (fun k : ℕ =>
      w0 * M / P.c0 * Real.exp (-((P.lam0 * P.l1 - 1) * P.level k))
        + (k : ℝ) * Real.exp (-(c2 * P.level k))) atTop (𝓝 0) := by
    simpa using hE1.add hE2
  refine squeeze_zero (fun k => ?_) (fun k => ?_) hlim
  · exact div_nonneg (mul_nonneg (Real.exp_pos _).le
      (integral_nonneg fun z => lowerTail_nonneg _ _ z)) (P.weight_pos k).le
  · have hLk : 0 < P.level k := P.level_pos k
    have hwk : P.weight k = P.c0 * Real.exp (-(P.level k)) := rfl
    have hmain := integral_lowerTail_bandLaw_le (w0 := w0) (mu := mu) (v := v) (l1 := P.l1)
      (a := P.level) (w := P.weight) (θ := P.theta) (m := m) hw0
      (fun k => (P.weight_pos k).le) (fun k => lt_of_lt_of_le one_pos (P.htheta k).1)
      hl0 hl1 P.level_pos hm P.level_tendsto hv hlam0.le hmonoP k
    -- the finitely many bands below the level
    have hhead : (∑ j ∈ Finset.range k, P.weight j * Real.exp (P.lam0 * P.level j))
        ≤ (k : ℝ) * (P.c0 * Real.exp ((P.lam0 - 1) * (P.level k / P.A))) := by
      have hterm : ∀ j ∈ Finset.range k,
          P.weight j * Real.exp (P.lam0 * P.level j)
            ≤ P.c0 * Real.exp ((P.lam0 - 1) * (P.level k / P.A)) := by
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        have hlev : P.level j ≤ P.level k / P.A := by
          rw [le_div_iff₀ hA0]
          have : P.level j * P.A = P.level (j + 1) := by
            rw [BandParameters.level, BandParameters.level, pow_succ]
          rw [this]
          exact hmonoP (by omega)
        have hrw : P.weight j * Real.exp (P.lam0 * P.level j)
            = P.c0 * Real.exp ((P.lam0 - 1) * P.level j) := by
          rw [BandParameters.weight, mul_assoc, ← Real.exp_add]
          congr 2
          ring
        rw [hrw]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) P.hc0.le
        exact mul_le_mul_of_nonneg_left hlev (by linarith)
      calc (∑ j ∈ Finset.range k, P.weight j * Real.exp (P.lam0 * P.level j))
          ≤ ∑ _j ∈ Finset.range k, P.c0 * Real.exp ((P.lam0 - 1) * (P.level k / P.A)) :=
            Finset.sum_le_sum hterm
        _ = (k : ℝ) * (P.c0 * Real.exp ((P.lam0 - 1) * (P.level k / P.A))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hmain' : (∫ z, lowerTail P.lam0 (P.l1 * P.level k) z ∂(P.law m mu v))
        ≤ w0 * M + ∑ j ∈ Finset.range k, P.weight j * Real.exp (P.lam0 * P.level j) := hmain
    have hnum : Real.exp (-(P.lam0 * P.l1 * P.level k)) *
        ∫ z, lowerTail P.lam0 (P.l1 * P.level k) z ∂(P.law m mu v)
        ≤ Real.exp (-(P.lam0 * P.l1 * P.level k)) *
          (w0 * M + (k : ℝ) * (P.c0 * Real.exp ((P.lam0 - 1) * (P.level k / P.A)))) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      linarith [hmain', hhead]
    refine le_trans (div_le_div_of_nonneg_right hnum (P.weight_pos k).le) (le_of_eq ?_)
    rw [hwk, hc2]
    have he : Real.exp (-(P.level k)) ≠ 0 := Real.exp_ne_zero _
    have hc0 : P.c0 ≠ 0 := P.hc0.ne'
    have e1 : Real.exp (-((P.lam0 * P.l1 - 1) * P.level k))
        = Real.exp (-(P.lam0 * P.l1 * P.level k)) / Real.exp (-(P.level k)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    have e2 : Real.exp (-((P.lam0 * P.l1 - 1 - (P.lam0 - 1) / P.A) * P.level k))
        = Real.exp (-(P.lam0 * P.l1 * P.level k)) *
          Real.exp ((P.lam0 - 1) * (P.level k / P.A)) / Real.exp (-(P.level k)) := by
      rw [← Real.exp_add, ← Real.exp_sub]
      congr 1
      field_simp
      ring
    rw [e1, e2]
    field_simp


/-- **The whole Step-1 output of `thm:dgt4-many-limits` for the constructed law.** -/
theorem bandLawProfile_law (P : BandParameters) (hA : P.A⁻¹ ≤ P.l1)
    (hlam1 : 1 < P.lam0 * P.l1)
    (hparam : 1 - P.lam0 * P.l1 + (P.lam0 - 1) / P.A < 0)
    (m : ℕ → ℕ) (hm : ∀ k, 0 < m k) (hmtop : Tendsto (fun k => (m k : ℝ)) atTop atTop)
    (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (htot : ∑' k, P.weight k ≤ 1) :
    BandLawProfile P (P.law m mu v) :=
  ⟨bandProfile_law P hA m hm hmtop mu v hv htot,
    bandDensity_law P hA m hm mu v hv htot,
    bandUpperIsolation_law P hA m hm hmtop mu v hv htot,
    bandLowerIsolation_law P hlam1 hparam m hm mu v hv htot⟩


end Sandpile.Support
