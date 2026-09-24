/-
The centered, variance-one one-site law of Step 1 of `thm:dgt4-many-limits`
(`sandpile.tex:5903`, `sandpile.tex:5972-5977`).

The shift `μ` and the variance `v` of the construction enter only through the
Gaussian summand, so the two normalizations are two divisions:

* `μ = -(∑_k ω_k μ_k)/w_0` makes the mean zero, where `μ_k` is the `k`th band
  component's own mean;
* `v = (1 - ∑_k ω_k s_k)/w_0 - μ²` then makes the second moment, and hence the
  variance, equal to one, where `s_k` is the `k`th band component's own second
  moment.

The only thing to check is that this `v` is positive, which is the smallness
hypothesis below; scaling the weight constant `c_0` down makes it true, and
scaling `c_0` changes nothing else about the parameters, so all the admissible
inequalities of `BandParameters.exists_admissible` survive.
-/
import Sandpile.Support.Dgt4ABandLawVariance
import Sandpile.Support.Dgt4ABandLawTail
import Sandpile.Support.Dgt4ABandParameters

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

variable {w0 mu : ℝ} {v : ℝ≥0} {l1 : ℝ} {a w θ : ℕ → ℝ} {m : ℕ → ℕ}

/-- The law has a finite second moment, by domination against its exponential
moment. -/
theorem integrable_sq_bandLaw (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 < θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hv : v ≠ 0)
    (hsum : Summable fun k => w k * Real.exp (1 / 2 * a k)) :
    Integrable (fun z : ℝ => z ^ 2) (bandLaw w0 mu v l1 a w θ m) := by
  have hexp := integrable_exp_abs_bandLaw (mu := mu) (v := v) hw0 hw hθ hl0 hl1 ha hm hatop hv
    (c := 1 / 2) (by norm_num) hsum
  refine Integrable.mono' (hexp.const_mul 16) (continuous_pow 2).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z), ← sq_abs z,
    show (1 : ℝ) / 2 * |z| = |z| / 2 by ring]
  exact sq_le_exp_half |z| (abs_nonneg z)

/-- **The centered, variance-one one-site law.**  The smallness hypothesis is
exactly what makes the normalizing variance positive. -/
theorem exists_centered_law (P : BandParameters) (m : ℕ → ℕ) (hm : ∀ k, 0 < m k)
    (hlt : ∑' k, P.weight k < 1)
    (hsmall : (∑' k, P.weight k * bandMean P.l1 (P.level k) (P.theta k) (m k)) ^ 2
      < (1 - ∑' k, P.weight k) *
        (1 - ∑' k, P.weight k * bandSecondMoment P.l1 (P.level k) (P.theta k) (m k))) :
    ∃ (mu : ℝ) (v : ℝ≥0), v ≠ 0 ∧
      ∫ z : ℝ, z ∂(P.law m mu v) = 0 ∧
      variance (id : ℝ → ℝ) (P.law m mu v) = 1 := by
  classical
  have hl0 : 0 < P.l1 := P.hl1.1
  have hl1 : P.l1 < 1 := P.hl1.2
  have hθpos : ∀ k, 0 < P.theta k := fun k => lt_of_lt_of_le one_pos (P.htheta k).1
  set w0 : ℝ := 1 - ∑' k, P.weight k with hw0def
  have hw0pos : 0 < w0 := by simp only [hw0def]; linarith
  set S1 : ℝ := ∑' k, P.weight k * bandMean P.l1 (P.level k) (P.theta k) (m k) with hS1
  set S2 : ℝ := ∑' k, P.weight k * bandSecondMoment P.l1 (P.level k) (P.theta k) (m k) with hS2
  set mu : ℝ := -S1 / w0 with hmu
  set vr : ℝ := (1 - S2) / w0 - mu ^ 2 with hvr
  have hvrpos : 0 < vr := by
    have h1 : vr = ((1 - S2) * w0 - S1 ^ 2) / w0 ^ 2 := by
      rw [hvr, hmu]
      field_simp
    rw [h1]
    refine div_pos ?_ (by positivity)
    nlinarith [hsmall]
  set vn : ℝ≥0 := Real.toNNReal vr with hvn
  have hvcoe : ((vn : ℝ≥0) : ℝ) = vr := by
    rw [hvn]
    exact Real.coe_toNNReal vr hvrpos.le
  have hvne : vn ≠ 0 := by
    rw [hvn]
    exact (Real.toNNReal_pos.mpr hvrpos).ne'
  have hwa : Summable fun k => P.weight k * P.level k := by
    simpa only [mul_comm] using P.summable_level_weight
  have hwa2 : Summable fun k => P.weight k * P.level k ^ 2 := P.summable_level_sq_weight
  have hwexp : Summable fun k => P.weight k * Real.exp (1 / 2 * P.level k) :=
    P.summable_weight_exp (1 / 2) (by norm_num)
  -- the mean
  have hmean : ∫ z : ℝ, z ∂(P.law m mu vn) = w0 * mu + S1 :=
    integral_id_bandLaw hw0pos.le (fun k => (P.weight_pos k).le) hθpos hl0 hl1 P.level_pos hm
      P.level_tendsto hvne hwa
  have hmean0 : ∫ z : ℝ, z ∂(P.law m mu vn) = 0 := by
    rw [hmean, hmu]
    field_simp
    ring
  -- the second moment
  have hsqint : ∫ z : ℝ, z ^ 2 ∂(P.law m mu vn) = w0 * ((vn : ℝ) + mu ^ 2) + S2 :=
    integral_sq_bandLaw hw0pos.le (fun k => (P.weight_pos k).le) hθpos hl0 hl1 P.level_pos hm
      P.level_tendsto hvne hwa2
  have hsq1 : ∫ z : ℝ, z ^ 2 ∂(P.law m mu vn) = 1 := by
    rw [hsqint, hvcoe, hvr]
    field_simp
    ring
  -- the variance
  have hint2 : Integrable (fun z : ℝ => z ^ 2) (P.law m mu vn) :=
    integrable_sq_bandLaw hw0pos.le (fun k => (P.weight_pos k).le) hθpos hl0 hl1 P.level_pos hm
      P.level_tendsto hvne hwexp
  haveI : IsProbabilityMeasure (P.law m mu vn) :=
    isProbabilityMeasure_bandLaw hw0pos.le (fun k => (P.weight_pos k).le) hθpos hl0 hl1
      P.level_pos hm P.level_tendsto hvne P.summable_weight (by ring)
  have hmem : MemLp (id : ℝ → ℝ) 2 (P.law m mu vn) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hint2
  refine ⟨mu, vn, hvne, hmean0, ?_⟩
  have hvarsub := variance_eq_sub (μ := P.law m mu vn) (X := (id : ℝ → ℝ)) hmem
  simp only [Pi.pow_apply, id_eq] at hvarsub
  rw [hvarsub, hsq1, hmean0]
  ring

/-- Scaling the weight constant `c_0`, which changes nothing else about the
parameters. -/
def BandParameters.scaleWeight (P : BandParameters) (ε : ℝ) (hε : 0 < ε) : BandParameters where
  A := P.A
  c0 := ε * P.c0
  l1 := P.l1
  lam0 := P.lam0
  theta := P.theta
  hA := P.hA
  hc0 := mul_pos hε P.hc0
  hl1 := P.hl1
  hlam0 := P.hlam0
  htheta := P.htheta

@[simp] theorem BandParameters.scaleWeight_A (P : BandParameters) (ε : ℝ) (hε : 0 < ε) :
    (P.scaleWeight ε hε).A = P.A := rfl

@[simp] theorem BandParameters.scaleWeight_l1 (P : BandParameters) (ε : ℝ) (hε : 0 < ε) :
    (P.scaleWeight ε hε).l1 = P.l1 := rfl

@[simp] theorem BandParameters.scaleWeight_lam0 (P : BandParameters) (ε : ℝ) (hε : 0 < ε) :
    (P.scaleWeight ε hε).lam0 = P.lam0 := rfl

@[simp] theorem BandParameters.scaleWeight_theta (P : BandParameters) (ε : ℝ) (hε : 0 < ε) :
    (P.scaleWeight ε hε).theta = P.theta := rfl

@[simp] theorem BandParameters.scaleWeight_level (P : BandParameters) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) : (P.scaleWeight ε hε).level k = P.level k := rfl

@[simp] theorem BandParameters.scaleWeight_weight (P : BandParameters) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) : (P.scaleWeight ε hε).weight k = ε * P.weight k := by
  simp only [BandParameters.weight, BandParameters.scaleWeight, BandParameters.level]
  ring

/-- **Admissible band parameters whose weights are small enough to normalize the
variance.**  Scaling `c_0` leaves `A`, `ℓ_1`, `λ_0` and the exponents alone, so
every inequality of `BandParameters.exists_admissible` survives. -/
theorem BandParameters.exists_admissible_small (l0 : ℝ) (hl0 : 0 < l0) (hl01 : l0 < 1)
    (m : ℕ → ℕ) (_hm : ∀ k, 0 < m k) :
    ∃ P : BandParameters,
      l0 < P.l1 ∧ 1 / P.l1 < P.lam0 ∧ P.lam0 < 1 / l0 ∧
      1 / P.A < P.l1 ∧ 1 - P.lam0 * P.l1 + (P.lam0 - 1) / P.A < 0 ∧
      Summable P.weight ∧ (∑' k, P.weight k) < 1 ∧
      (∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
        ∃ kl : ℕ → ℕ, StrictMono kl ∧
          Tendsto (fun n => 1 + 1 / P.theta (kl n)) atTop (𝓝 κ)) ∧
      (∑' k, P.weight k * bandMean P.l1 (P.level k) (P.theta k) (m k)) ^ 2
        < (1 - ∑' k, P.weight k) *
          (1 - ∑' k, P.weight k * bandSecondMoment P.l1 (P.level k) (P.theta k) (m k)) := by
  classical
  obtain ⟨P, h1, h2, h3, h4, h5, h6, h7, -, h9⟩ :=
    BandParameters.exists_admissible l0 hl0 hl01
  have hθpos : ∀ k, 0 < P.theta k := fun k => lt_of_lt_of_le one_pos (P.htheta k).1
  set W : ℝ := ∑' k, P.weight k with hW
  set S1 : ℝ := ∑' k, P.weight k * bandMean P.l1 (P.level k) (P.theta k) (m k) with hS1
  set S2 : ℝ := ∑' k, P.weight k * bandSecondMoment P.l1 (P.level k) (P.theta k) (m k) with hS2
  have hWpos : 0 < W := by
    rw [hW]
    exact lt_of_lt_of_le (P.weight_pos 0) (h6.le_tsum 0 fun k _ => (P.weight_pos k).le)
  have hS2nn : 0 ≤ S2 := by
    rw [hS2]
    exact tsum_nonneg fun k => mul_nonneg (P.weight_pos k).le
      (bandSecondMoment_nonneg (hθpos k) P.hl1.2 (P.level_pos k))
  set B : ℝ := 1 + |S1| + S2 + W with hB
  have habs : (0 : ℝ) ≤ |S1| := abs_nonneg _
  have hB1 : (1 : ℝ) ≤ B := by rw [hB]; linarith
  have hBpos : (0 : ℝ) < B := by linarith
  set ε : ℝ := 1 / (4 * B) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hWB : W ≤ B := by rw [hB]; linarith
  have hS2B : S2 ≤ B := by rw [hB]; linarith
  have hS1B : |S1| ≤ B := by rw [hB]; linarith
  have hεW : ε * W ≤ 1 / 4 := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * B)]
    nlinarith
  have hεS2 : ε * S2 ≤ 1 / 4 := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * B)]
    nlinarith
  have hεS1 : |ε * S1| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_pos hεpos, hε, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : (0 : ℝ) < 4 * B)]
    nlinarith
  refine ⟨P.scaleWeight ε hεpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · simpa using h4
  · simpa using h5
  · have hfun : (P.scaleWeight ε hεpos).weight = fun k => ε * P.weight k := by
      funext k
      exact BandParameters.scaleWeight_weight P ε hεpos k
    rw [hfun]
    exact h6.mul_left ε
  · have hval : ∑' k, (P.scaleWeight ε hεpos).weight k = ε * W := by
      simp only [BandParameters.scaleWeight_weight]
      rw [tsum_mul_left, ← hW]
    rw [hval]
    linarith
  · exact h9
  · have hval1 : ∑' k, (P.scaleWeight ε hεpos).weight k *
        bandMean (P.scaleWeight ε hεpos).l1 ((P.scaleWeight ε hεpos).level k)
          ((P.scaleWeight ε hεpos).theta k) (m k) = ε * S1 := by
      simp only [BandParameters.scaleWeight_weight, BandParameters.scaleWeight_l1,
        BandParameters.scaleWeight_level, BandParameters.scaleWeight_theta]
      rw [show (fun k : ℕ => ε * P.weight k * bandMean P.l1 (P.level k) (P.theta k) (m k))
          = fun k : ℕ => ε * (P.weight k * bandMean P.l1 (P.level k) (P.theta k) (m k)) from by
        funext k; ring]
      rw [tsum_mul_left, ← hS1]
    have hval2 : ∑' k, (P.scaleWeight ε hεpos).weight k *
        bandSecondMoment (P.scaleWeight ε hεpos).l1 ((P.scaleWeight ε hεpos).level k)
          ((P.scaleWeight ε hεpos).theta k) (m k) = ε * S2 := by
      simp only [BandParameters.scaleWeight_weight, BandParameters.scaleWeight_l1,
        BandParameters.scaleWeight_level, BandParameters.scaleWeight_theta]
      rw [show (fun k : ℕ => ε * P.weight k *
            bandSecondMoment P.l1 (P.level k) (P.theta k) (m k))
          = fun k : ℕ => ε * (P.weight k * bandSecondMoment P.l1 (P.level k) (P.theta k) (m k))
          from by funext k; ring]
      rw [tsum_mul_left, ← hS2]
    have hvalW : ∑' k, (P.scaleWeight ε hεpos).weight k = ε * W := by
      simp only [BandParameters.scaleWeight_weight]
      rw [tsum_mul_left, ← hW]
    rw [hval1, hval2, hvalW]
    have hsq : (ε * S1) ^ 2 ≤ 1 / 16 := by
      have hnn : 0 ≤ |ε * S1| := abs_nonneg _
      nlinarith [sq_abs (ε * S1), hεS1, hnn]
    nlinarith [hεW, hεS2, hsq]

/-- **The whole output of Step 1 of `thm:dgt4-many-limits`** for the constructed
one-site law: the four analytic clauses of the frozen statement, the four band
estimates of `eq:dgt4-band-profile`, `eq:dgt4-band-density`,
`eq:dgt4-band-upper-isolation` and `eq:dgt4-band-lower-isolation`, the integrated
profile that Step 2 consumes, and the fact that every `κ ∈ [3/2,2]` is a
subsequential limit of `κ_k = 1 + 1/ϑ_k`. -/
theorem exists_step1_law (l0 : ℝ) (hl0 : 0 < l0) (hl01 : l0 < 1) :
    ∃ (P : BandParameters) (m : ℕ → ℕ) (mu : ℝ) (v : ℝ≥0),
      l0 < P.l1 ∧ (∀ k, 0 < m k) ∧ Tendsto (fun k => ((m k : ℕ) : ℝ)) atTop atTop ∧
      v ≠ 0 ∧
      IsProbabilityMeasure (P.law m mu v) ∧
      ∫ z : ℝ, z ∂(P.law m mu v) = 0 ∧
      variance (id : ℝ → ℝ) (P.law m mu v) = 1 ∧
      (∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
        P.law m mu v = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z)) ∧
      (∃ c C θ0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ0 ∧
        Integrable (fun z : ℝ => Real.exp (θ0 * |z|)) (P.law m mu v) ∧
        ∀ᶠ r : ℝ in atTop,
          c * r ≤ -Real.log ((P.law m mu v) (Iic (-r))).toReal ∧
            -Real.log ((P.law m mu v) (Iic (-r))).toReal ≤ C * r) ∧
      BandLawProfile P (P.law m mu v) ∧
      BandIntegratedProfile P (P.law m mu v) ∧
      (∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
        ∃ kl : ℕ → ℕ, StrictMono kl ∧
          Tendsto (fun n => 1 + 1 / P.theta (kl n)) atTop (𝓝 κ)) := by
  classical
  obtain ⟨P, h1, h2, h3, h4, h5, h6, h7, h9, hsmall⟩ :=
    BandParameters.exists_admissible_small l0 hl0 hl01 (fun k => k + 1)
      (fun k => Nat.succ_pos k)
  obtain ⟨mu, v, hv, hmean, hvar⟩ :=
    exists_centered_law P (fun k => k + 1) (fun k => Nat.succ_pos k) h7 hsmall
  have hl1pos : 0 < P.l1 := P.hl1.1
  have hA : P.A⁻¹ ≤ P.l1 := by
    rw [inv_eq_one_div]
    exact h4.le
  have hlam1 : 1 < P.lam0 * P.l1 := (div_lt_iff₀ hl1pos).mp h2
  have hmtop : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hθpos : ∀ k, 0 < P.theta k := fun k => lt_of_lt_of_le one_pos (P.htheta k).1
  refine ⟨P, fun k => k + 1, mu, v, h1, fun k => Nat.succ_pos k, hmtop, hv, ?_, hmean, hvar,
    ?_, exists_log_tail_law P _ (fun k => Nat.succ_pos k) mu v hv h7.le,
    bandLawProfile_law P hA hlam1 h5 _ (fun k => Nat.succ_pos k) hmtop mu v hv h7.le,
    bandIntegratedProfile_law P hA _ (fun k => Nat.succ_pos k) hmtop mu v hv h7.le, h9⟩
  · exact isProbabilityMeasure_bandLaw (by linarith) (fun k => (P.weight_pos k).le) hθpos
      hl1pos P.hl1.2 P.level_pos (fun k => Nat.succ_pos k) P.level_tendsto hv
      P.summable_weight (by ring)
  · exact exists_density_bandLaw (by linarith) hv
      (fun k => le_trans zero_le_one (P.htheta k).1) (fun k => (P.weight_pos k).le)
      hl1pos P.hl1.2 P.level_pos (fun k => Nat.succ_pos k) P.level_tendsto

end Sandpile.Support
