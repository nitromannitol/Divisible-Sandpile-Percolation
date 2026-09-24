/-
The uniform lower-tail bound of `sandpile.tex:4180-4186`: a mean-zero law whose
variance is bounded below and whose exponential moment is bounded above falls
below a fixed negative level with a fixed probability, with both depending only
on those two bounds.

Everything is elementary.  The exponential moment bounds the second and fourth
moments, since `x^k` is at most a constant times `e^x` on the nonnegative reals.
The pointwise inequality `z^2 <= T|z| + z^4/T^2`, at the scale where the
fourth-moment term is half the variance, turns the variance lower bound into a
lower bound on the first absolute moment, and mean zero halves that into a lower
bound on the mean of the negative part.  The pointwise inequality
`Y <= m/2 + S 1_A + Y^2/S`, with `A` the event that `Y` exceeds `m/2`, converts
that mean into a probability.
-/
import Sandpile.Support.IncrementBall

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile

theorem sq_le_four_exp (x : ℝ) (hx : 0 ≤ x) : x ^ 2 ≤ 4 * Real.exp x := by
  have h1 : 1 + x / 2 ≤ Real.exp (x / 2) := Real.add_one_le_exp (x / 2) |>.trans_eq' (by ring)
  have h2 : Real.exp (x / 2) ^ 2 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h3 : (1 + x / 2) ^ 2 ≤ Real.exp (x / 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) h1 2
  rw [h2] at h3
  nlinarith

theorem pow_four_le_exp (x : ℝ) (hx : 0 ≤ x) : x ^ 4 ≤ 256 * Real.exp x := by
  have h1 : 1 + x / 4 ≤ Real.exp (x / 4) := Real.add_one_le_exp (x / 4) |>.trans_eq' (by ring)
  have h2 : Real.exp (x / 4) ^ 4 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h3 : (1 + x / 4) ^ 4 ≤ Real.exp (x / 4) ^ 4 :=
    pow_le_pow_left₀ (by linarith) h1 4
  rw [h2] at h3
  nlinarith [pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ x / 4) (by linarith : x / 4 ≤ 1 + x / 4) 4]

/-- **A uniform lower-tail bound from the variance and the exponential moment.**
The paper's "the exponential moment and variance assumptions give `a, q > 0`,
depending only on `ν₀, θ₀, K₀`, such that `P(ζ(0) ≤ -a) ≥ q`",
`sandpile.tex:4175-4181`.

The route is elementary.  The exponential moment bounds the second and fourth
moments.  The pointwise inequality `z² ≤ T|z| + z⁴/T²`, at the scale `T` where
the fourth-moment term is half the variance, turns the variance lower bound into
a lower bound on `E|z|`, and mean zero turns that into a lower bound on the mean
of the negative part.  A second pointwise inequality of the same kind, applied
to the negative part, converts that mean into a probability. -/
theorem exists_uniform_left_tail (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ a q : ℝ, 0 < a ∧ 0 < q ∧ q ≤ 1 ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ENNReal.ofReal q ≤ ν (Set.Iic (-a)) := by
  classical
  obtain ⟨C₂, hC₂def⟩ : ∃ x : ℝ, x = 4 * max K₀ 1 / θ₀ ^ 2 := ⟨_, rfl⟩
  obtain ⟨C₄, hC₄def⟩ : ∃ x : ℝ, x = 256 * max K₀ 1 / θ₀ ^ 4 := ⟨_, rfl⟩
  have hK1 : (1 : ℝ) ≤ max K₀ 1 := le_max_right _ _
  have hC₂ : 0 < C₂ := by rw [hC₂def]; positivity
  have hC₄ : 0 < C₄ := by rw [hC₄def]; positivity
  obtain ⟨T, hTdef⟩ : ∃ x : ℝ, x = Real.sqrt (2 * C₄ / ν₀ ^ 2) := ⟨_, rfl⟩
  have hT : 0 < T := by
    rw [hTdef]
    exact Real.sqrt_pos.mpr (by positivity)
  have hTsq : T ^ 2 = 2 * C₄ / ν₀ ^ 2 := by
    rw [hTdef]
    exact Real.sq_sqrt (by positivity)
  obtain ⟨μ, hμdef⟩ : ∃ x : ℝ, x = ν₀ ^ 2 / (4 * T) := ⟨_, rfl⟩
  have hμ : 0 < μ := by rw [hμdef]; positivity
  obtain ⟨S, hSdef⟩ : ∃ x : ℝ, x = 4 * C₂ / μ := ⟨_, rfl⟩
  have hS : 0 < S := by rw [hSdef]; positivity
  refine ⟨μ / 2, min 1 (μ / (4 * S)), by positivity,
    lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro ν hprob hmean hvar hexpint hexp
  haveI := hprob
  -- the second and fourth moments
  have hsqint : Integrable (fun z : ℝ => z ^ 2) ν := by
    refine Integrable.mono' (hexpint.const_mul (4 / θ₀ ^ 2))
      (measurable_id.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have h := sq_le_four_exp (θ₀ * |z|) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]
    have hz : (θ₀ * |z|) ^ 2 = θ₀ ^ 2 * z ^ 2 := by
      rw [mul_pow, sq_abs]
    rw [hz] at h
    have hθ2 : (0 : ℝ) < θ₀ ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hθ2]
    nlinarith
  have hfourint : Integrable (fun z : ℝ => z ^ 4) ν := by
    refine Integrable.mono' (hexpint.const_mul (256 / θ₀ ^ 4))
      (measurable_id.pow_const 4).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have h := pow_four_le_exp (θ₀ * |z|) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ z ^ 4)]
    have hz : (θ₀ * |z|) ^ 4 = θ₀ ^ 4 * z ^ 4 := by
      rw [mul_pow, show |z| ^ 4 = (|z| ^ 2) ^ 2 by ring, sq_abs]
      ring
    rw [hz] at h
    have hθ4 : (0 : ℝ) < θ₀ ^ 4 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hθ4]
    nlinarith
  have hsqle : ∫ z, z ^ 2 ∂ν ≤ C₂ := by
    have hbd : ∫ z, z ^ 2 ∂ν ≤ ∫ z, 4 / θ₀ ^ 2 * Real.exp (θ₀ * |z|) ∂ν := by
      refine integral_mono hsqint (hexpint.const_mul _) fun z => ?_
      have h := sq_le_four_exp (θ₀ * |z|) (by positivity)
      have hz : (θ₀ * |z|) ^ 2 = θ₀ ^ 2 * z ^ 2 := by rw [mul_pow, sq_abs]
      rw [hz] at h
      have hθ2 : (0 : ℝ) < θ₀ ^ 2 := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hθ2]
      nlinarith
    rw [integral_const_mul] at hbd
    have hθ2 : (0 : ℝ) < θ₀ ^ 2 := by positivity
    have : 4 / θ₀ ^ 2 * ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ C₂ := by
      rw [hC₂def]
      have hK : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ max K₀ 1 := le_trans hexp (le_max_left _ _)
      rw [div_mul_eq_mul_div, mul_comm]
      exact div_le_div_of_nonneg_right (by nlinarith) hθ2.le
    linarith
  have hfourle : ∫ z, z ^ 4 ∂ν ≤ C₄ := by
    have hbd : ∫ z, z ^ 4 ∂ν ≤ ∫ z, 256 / θ₀ ^ 4 * Real.exp (θ₀ * |z|) ∂ν := by
      refine integral_mono hfourint (hexpint.const_mul _) fun z => ?_
      have h := pow_four_le_exp (θ₀ * |z|) (by positivity)
      have hz : (θ₀ * |z|) ^ 4 = θ₀ ^ 4 * z ^ 4 := by
        rw [mul_pow, show |z| ^ 4 = (|z| ^ 2) ^ 2 by ring, sq_abs]
        ring
      rw [hz] at h
      have hθ4 : (0 : ℝ) < θ₀ ^ 4 := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hθ4]
      nlinarith
    rw [integral_const_mul] at hbd
    have hθ4 : (0 : ℝ) < θ₀ ^ 4 := by positivity
    have : 256 / θ₀ ^ 4 * ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ C₄ := by
      rw [hC₄def]
      have hK : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ max K₀ 1 := le_trans hexp (le_max_left _ _)
      rw [div_mul_eq_mul_div, mul_comm]
      exact div_le_div_of_nonneg_right (by nlinarith) hθ4.le
    linarith
  -- the variance lower bound as a second moment
  have hmemLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr (by simpa using hsqint)
  have hvarR : ν₀ ^ 2 ≤ ∫ z, z ^ 2 ∂ν := by
    have h1 : ENNReal.ofReal (ν₀ ^ 2) ≤ ENNReal.ofReal (variance (id : ℝ → ℝ) ν) := by
      rw [ProbabilityTheory.ofReal_variance hmemLp]
      exact hvar
    have h2 : ν₀ ^ 2 ≤ variance (id : ℝ → ℝ) ν :=
      (ENNReal.ofReal_le_ofReal_iff (variance_nonneg _ _)).mp h1
    have h3 : variance (id : ℝ → ℝ) ν = ∫ z, z ^ 2 ∂ν := by
      rw [ProbabilityTheory.variance_eq_integral measurable_id.aemeasurable]
      have hid : ∫ z, (id : ℝ → ℝ) z ∂ν = 0 := by simpa using hmean
      simp only [id] at hid ⊢
      rw [hid]
      simp
    rw [h3] at h2
    exact h2
  -- the first absolute moment
  have habsint : Integrable (fun z : ℝ => |z|) ν := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hsqint)
      measurable_id.abs.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_abs]
    have h1 : 0 ≤ (|z| - 1) ^ 2 := sq_nonneg _
    have h2 : |z| ^ 2 = z ^ 2 := sq_abs z
    nlinarith [h1, h2, sq_nonneg z]
  have hidint : Integrable (fun z : ℝ => z) ν :=
    Integrable.mono' habsint measurable_id.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => le_of_eq (Real.norm_eq_abs z))
  have hpt : ∀ z : ℝ, z ^ 2 ≤ T * |z| + z ^ 4 / T ^ 2 := by
    intro z
    have hz2 : |z| ^ 2 = z ^ 2 := sq_abs z
    have hz4 : |z| ^ 4 = z ^ 4 := by
      rw [show |z| ^ 4 = (|z| ^ 2) ^ 2 by ring, hz2]
      ring
    have hT2 : (0 : ℝ) < T ^ 2 := by positivity
    rcases le_or_gt |z| T with h | h
    · have h1 : z ^ 2 ≤ T * |z| := by
        rw [← hz2]
        nlinarith [abs_nonneg z]
      have h2 : (0 : ℝ) ≤ z ^ 4 / T ^ 2 := by positivity
      linarith
    · have h1 : z ^ 2 ≤ z ^ 4 / T ^ 2 := by
        rw [le_div_iff₀ hT2]
        have hTz : T ^ 2 ≤ |z| ^ 2 := by nlinarith [hT.le, h.le, abs_nonneg z]
        calc z ^ 2 * T ^ 2 ≤ z ^ 2 * |z| ^ 2 :=
              mul_le_mul_of_nonneg_left hTz (sq_nonneg z)
          _ = z ^ 4 := by rw [hz2]; ring
      have h2 : (0 : ℝ) ≤ T * |z| := by positivity
      linarith
  have habsl : ν₀ ^ 2 / (2 * T) ≤ ∫ z, |z| ∂ν := by
    have hbd : ∫ z, z ^ 2 ∂ν ≤ ∫ z, (T * |z| + z ^ 4 / T ^ 2) ∂ν :=
      integral_mono hsqint ((habsint.const_mul T).add (hfourint.div_const _)) hpt
    rw [integral_add (habsint.const_mul T) (hfourint.div_const _), integral_const_mul,
      integral_div] at hbd
    have hCT : C₄ / T ^ 2 = ν₀ ^ 2 / 2 := by
      rw [hTsq]
      field_simp
    have h4 : (∫ z, z ^ 4 ∂ν) / T ^ 2 ≤ C₄ / T ^ 2 :=
      div_le_div_of_nonneg_right hfourle (by positivity : (0:ℝ) ≤ T ^ 2)
    have h5 : ν₀ ^ 2 ≤ T * ∫ z, |z| ∂ν + ν₀ ^ 2 / 2 := by
      rw [← hCT]
      linarith
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * T)]
    calc ν₀ ^ 2 = 2 * (ν₀ ^ 2 / 2) := by ring
      _ ≤ 2 * (T * ∫ z, |z| ∂ν) := by linarith
      _ = (∫ z, |z| ∂ν) * (2 * T) := by ring
  -- the mean of the negative part
  have hnegint : Integrable (fun z : ℝ => max (-z) 0) ν := by
    refine Integrable.mono' habsint
      ((measurable_id.neg).max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs z) (abs_nonneg z)
  have hneg : μ ≤ ∫ z, max (-z) 0 ∂ν := by
    have hsplit : ∀ z : ℝ, |z| = z + 2 * max (-z) 0 := by
      intro z
      rcases le_or_gt 0 z with h | h
      · rw [abs_of_nonneg h, max_eq_right (by linarith)]
        ring
      · rw [abs_of_neg h, max_eq_left (by linarith)]
        ring
    have hI : ∫ z, |z| ∂ν = (∫ z, z ∂ν) + 2 * ∫ z, max (-z) 0 ∂ν := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
        integral_add hidint (hnegint.const_mul 2), integral_const_mul]
    rw [hI, hmean, zero_add] at habsl
    rw [hμdef]
    have h2 : ν₀ ^ 2 / (4 * T) = (ν₀ ^ 2 / (2 * T)) / 2 := by
      field_simp
      ring
    rw [h2]
    linarith
  -- turn the mean into a probability
  have hA : MeasurableSet {z : ℝ | μ / 2 < max (-z) 0} :=
    measurableSet_lt measurable_const (measurable_id.neg.max measurable_const)
  have hpt2 : ∀ z : ℝ, max (-z) 0
      ≤ μ / 2 + S * Set.indicator {z : ℝ | μ / 2 < max (-z) 0} (1 : ℝ → ℝ) z
        + (max (-z) 0) ^ 2 / S := by
    intro z
    have hY0 : (0 : ℝ) ≤ max (-z) 0 := le_max_right _ _
    have hS2 : (0 : ℝ) ≤ (max (-z) 0) ^ 2 / S := by positivity
    have hμ2 : (0 : ℝ) ≤ μ / 2 := by positivity
    by_cases hcase : μ / 2 < max (-z) 0
    · have hmem : z ∈ {z : ℝ | μ / 2 < max (-z) 0} := hcase
      have hind : Set.indicator {z : ℝ | μ / 2 < max (-z) 0} (1 : ℝ → ℝ) z = 1 := by
        rw [Set.indicator_of_mem hmem]
        rfl
      rw [hind, mul_one]
      rcases le_or_gt (max (-z) 0) S with h | h
      · linarith
      · have hYS : max (-z) 0 ≤ (max (-z) 0) ^ 2 / S := by
          rw [le_div_iff₀ hS]
          nlinarith
        linarith
    · have hmem : z ∉ {z : ℝ | μ / 2 < max (-z) 0} := hcase
      have hind : Set.indicator {z : ℝ | μ / 2 < max (-z) 0} (1 : ℝ → ℝ) z = 0 :=
        Set.indicator_of_notMem hmem _
      rw [hind, mul_zero, add_zero]
      push Not at hcase
      linarith
  have hindint : Integrable
      (Set.indicator {z : ℝ | μ / 2 < max (-z) 0} (1 : ℝ → ℝ)) ν :=
    (integrable_const (1 : ℝ)).indicator hA
  have hnegsqint : Integrable (fun z : ℝ => (max (-z) 0) ^ 2) ν := by
    refine Integrable.mono' hsqint
      (((measurable_id.neg).max measurable_const).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : max (-z) 0 ≤ |z| := max_le (neg_le_abs z) (abs_nonneg z)
    have h2 : (max (-z) 0) ^ 2 ≤ |z| ^ 2 := pow_le_pow_left₀ (le_max_right _ _) h1 2
    rwa [sq_abs] at h2
  have hprob2 : μ / (4 * S) ≤ ν.real {z : ℝ | μ / 2 < max (-z) 0} := by
    have hbd : ∫ z, max (-z) 0 ∂ν
        ≤ ∫ z, (μ / 2 + S * Set.indicator {z : ℝ | μ / 2 < max (-z) 0}
            (1 : ℝ → ℝ) z + (max (-z) 0) ^ 2 / S) ∂ν :=
      integral_mono hnegint
        (((integrable_const (μ / 2)).add (hindint.const_mul S)).add (hnegsqint.div_const S)) hpt2
    have e1 := integral_add (μ := ν)
      (f := fun z : ℝ => μ / 2 + S * Set.indicator {z : ℝ | μ / 2 < max (-z) 0} (1 : ℝ → ℝ) z)
      (g := fun z : ℝ => (max (-z) 0) ^ 2 / S)
      ((integrable_const (μ / 2)).add (hindint.const_mul S)) (hnegsqint.div_const S)
    have e2 := integral_add (μ := ν) (f := fun _ : ℝ => μ / 2)
      (g := fun z : ℝ => S * Set.indicator {z : ℝ | μ / 2 < max (-z) 0} (1 : ℝ → ℝ) z)
      (integrable_const (μ / 2)) (hindint.const_mul S)
    rw [e1, e2, integral_const, integral_const_mul, integral_div,
      probReal_univ, smul_eq_mul, one_mul, integral_indicator_one hA] at hbd
    have hsq2 : (∫ z, (max (-z) 0) ^ 2 ∂ν) / S ≤ C₂ / S := by
      refine div_le_div_of_nonneg_right ?_ hS.le
      refine le_trans (integral_mono hnegsqint hsqint fun z => ?_) hsqle
      have h1 : max (-z) 0 ≤ |z| := max_le (neg_le_abs z) (abs_nonneg z)
      have h2 : (max (-z) 0) ^ 2 ≤ |z| ^ 2 := pow_le_pow_left₀ (le_max_right _ _) h1 2
      rwa [sq_abs] at h2
    have hCS : C₂ / S = μ / 4 := by
      rw [hSdef]
      field_simp
    rw [hCS] at hsq2
    have hkey : μ / 4 ≤ S * ν.real {z : ℝ | μ / 2 < max (-z) 0} := by linarith
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * S)]
    calc μ = 4 * (μ / 4) := by ring
      _ ≤ 4 * (S * ν.real {z : ℝ | μ / 2 < max (-z) 0}) := by linarith
      _ = ν.real {z : ℝ | μ / 2 < max (-z) 0} * (4 * S) := by ring
  -- the event sits inside the half-line
  have hsub : {z : ℝ | μ / 2 < max (-z) 0} ⊆ Set.Iic (-(μ / 2)) := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [Set.mem_Iic]
    rcases max_cases (-z) 0 with ⟨he, -⟩ | ⟨he, -⟩
    · rw [he] at hz; linarith
    · rw [he] at hz; linarith [hμ]
  have hfinal : μ / (4 * S) ≤ ν.real (Set.Iic (-(μ / 2))) :=
    le_trans hprob2 (measureReal_mono hsub (measure_ne_top _ _))
  refine le_trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)) ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν (Set.Iic (-(μ / 2))))]
  exact ENNReal.ofReal_le_ofReal hfinal

end Sandpile
