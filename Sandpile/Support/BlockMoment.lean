import LatticeProb.Prob.WeightedConc
import Sandpile.Support.Norms
import Sandpile.Support.UniformTail

/-!
# Exponential lower bounds for the block-tail moment generating function

These lemmas supply the exponential lower bound and second-moment argument used for the block
tail estimate of `sandpile.tex:2827-2881`. A fixed amount `q` of mass on a negative half-line
`Set.Iic (-a)` forces a quadratic lower bound `1 + q * a ^ 2 / 4 * s ^ 2` on the one-site moment
generating function `∫ z, Real.exp (-(s * z)) ∂ν`, uniformly over mean-zero laws `ν`; taking
logarithms and multiplying across independent coordinates upgrades this to a lower bound on the
moment generating function of a weighted sum. The file closes with two second-moment tail
estimates, `measure_lower_tail_of_moments` and `measure_neg_tail_of_exp_moments`, which convert
such moment bounds into lower bounds on tail probabilities.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile

/-- For `u ≥ 0`, the quadratic `1 + u + u ^ 2 / 4` lower-bounds `Real.exp u`, obtained by squaring
the elementary bound `1 + u / 2 ≤ Real.exp (u / 2)`. -/
theorem quadratic_le_exp_nonneg {u : ℝ} (hu : 0 ≤ u) :
    1 + u + u ^ 2 / 4 ≤ Real.exp u := by
  have h : 1 + u / 2 ≤ Real.exp (u / 2) := by
    linarith [Real.add_one_le_exp (u / 2)]
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + u / 2) h 2
  have heq : Real.exp (u / 2) ^ 2 = Real.exp u := by
    rw [sq, ← Real.exp_add, add_halves]
  rw [heq] at hsq
  nlinarith

/-- For a mean-zero law `ν` carrying at least mass `q` on `Set.Iic (-a)`, the moment generating
function `∫ z, Real.exp (-(s * z)) ∂ν` is at least the quadratic `1 + q * a ^ 2 / 4 * s ^ 2`, from
a pointwise lower bound on `Real.exp (-(s * z))` by a parabola matching it on `Set.Iic (-a)` and by
`Real.add_one_le_exp` elsewhere. -/
theorem integral_exp_neg_lower (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    {a q s : ℝ} (ha : 0 < a) (hs : 0 ≤ s)
    (htail : q ≤ ν.real (Set.Iic (-a)))
    (hexp : Integrable (fun z => Real.exp (-(s * z))) ν) :
    1 + q * a ^ 2 / 4 * s ^ 2 ≤ ∫ z, Real.exp (-(s * z)) ∂ν := by
  classical
  set A := Set.Iic (-a)
  have hA : MeasurableSet A := measurableSet_Iic
  have hi : Integrable (A.indicator (1 : ℝ → ℝ)) ν := (integrable_const 1).indicator hA
  have hpt (z : ℝ) : 1 - s * z + (s ^ 2 * a ^ 2 / 4) * A.indicator (1 : ℝ → ℝ) z
      ≤ Real.exp (-(s * z)) := by
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz]
      change 1 - s * z + (s ^ 2 * a ^ 2 / 4) * 1 ≤ _
      have hz' : z ≤ -a := hz
      have hu : 0 ≤ -(s * z) := by nlinarith
      have hsa : s * a ≤ -(s * z) := by nlinarith
      have hsq : (s * a) ^ 2 ≤ (-(s * z)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hs ha.le) hsa 2
      have := quadratic_le_exp_nonneg hu
      nlinarith
    · rw [Set.indicator_of_notMem hz]
      have := Real.add_one_le_exp (-(s * z))
      linarith
  have h := integral_mono
    (((integrable_const 1).sub (hint.const_mul s)).add (hi.const_mul (s ^ 2 * a ^ 2 / 4)))
    hexp hpt
  simp only [Pi.add_apply, Pi.sub_apply, id_eq] at h
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul,
    integral_const, integral_indicator_one hA, hmean] at h
  · simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, sub_zero] at h
    have htail' := mul_le_mul_of_nonneg_left htail (show 0 ≤ s ^ 2 * a ^ 2 / 4 by positivity)
    dsimp [A] at h
    nlinarith
  · exact integrable_const _
  · exact hint.const_mul s
  · exact (integrable_const 1).sub (hint.const_mul s)
  · exact hi.const_mul _

/-- For `0 ≤ v ≤ 1`, `v / 2 ≤ Real.log (1 + v)`, a quantitative version of
`Real.le_log_one_add_of_nonneg` valid on the unit interval. -/
theorem half_le_log_one_add {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    v / 2 ≤ Real.log (1 + v) := by
  refine le_trans ?_ (Real.le_log_one_add_of_nonneg hv)
  rw [le_div_iff₀ (by linarith : 0 < v + 2)]
  nlinarith

/-- Under the sub-Gaussian hypothesis `SubGaussianOn id c s₀ ν`, the exponential of the weighted
sum `s * ∑ i, ℓ i * ξ i` is integrable on the product measure `Measure.pi fun _ => ν`, being a
finite product of the one-coordinate integrable exponentials `Real.exp (s * ℓ i * ξ i)`. -/
theorem integrable_exp_weighted_sum {N : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {c s₀ : ℝ} (hSG : SubGaussianOn id c s₀ ν) (ℓ : Fin N → ℝ) (s : ℝ)
    (hs : ∀ i, |s * ℓ i| ≤ s₀) :
    Integrable (fun ξ => Real.exp (s * ∑ i, ℓ i * ξ i)) (Measure.pi fun _ : Fin N => ν) := by
  have hprod : Integrable (fun ξ : Fin N → ℝ => ∏ i, Real.exp (s * ℓ i * ξ i))
      (Measure.pi fun _ : Fin N => ν) :=
    Integrable.fintype_prod fun i => (hSG (s * ℓ i) (hs i)).1
  refine hprod.congr (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [← Real.exp_sum, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Taking logarithms in `integral_exp_neg_lower` and applying `half_le_log_one_add` to the
resulting quadratic, which lies in `[0, 1]` once `q * a ^ 2 * s ^ 2 ≤ 4`, gives the log-moment
bound `q * a ^ 2 / 8 * s ^ 2 ≤ Real.log (∫ z, Real.exp (-(s * z)) ∂ν)`. -/
theorem log_integral_exp_neg_lower (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    {a q s : ℝ} (ha : 0 < a) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (htail : q ≤ ν.real (Set.Iic (-a)))
    (hexp : Integrable (fun z => Real.exp (-(s * z))) ν)
    (hsmall : q * a ^ 2 * s ^ 2 ≤ 4) :
    q * a ^ 2 / 8 * s ^ 2 ≤ Real.log (∫ z, Real.exp (-(s * z)) ∂ν) := by
  have h0 : 0 ≤ q * a ^ 2 / 4 * s ^ 2 := by positivity
  have h := half_le_log_one_add h0 (by nlinarith : q * a ^ 2 / 4 * s ^ 2 ≤ 1)
  have hlog := Real.log_le_log (show 0 < 1 + q * a ^ 2 / 4 * s ^ 2 by positivity)
    (integral_exp_neg_lower ν hint hmean ha hs htail hexp)
  nlinarith

/-- For independent coordinates each satisfying the tail hypothesis of `integral_exp_neg_lower`,
the product moment generating function
`∫ ξ, Real.exp (-(θ * ∑ i, ℓ i * ξ i)) ∂(Measure.pi fun _ => ν)` is at least
`Real.exp (q * a ^ 2 / 8 * θ ^ 2 * ∑ i, ℓ i ^ 2)`, obtained by factoring the exponential of a sum
into a product over coordinates and multiplying the per-coordinate lower bounds from
`log_integral_exp_neg_lower`. -/
theorem integral_exp_neg_weighted_lower {N : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    {a q θ : ℝ} (ha : 0 < a) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (htail : q ≤ ν.real (Set.Iic (-a)))
    (ℓ : Fin N → ℝ) (hℓ : ∀ i, 0 ≤ ℓ i)
    (hsmall : ∀ i, q * a ^ 2 * (θ * ℓ i) ^ 2 ≤ 4)
    (hexp : ∀ i, Integrable (fun z => Real.exp (-(θ * ℓ i * z))) ν) :
    Real.exp (q * a ^ 2 / 8 * θ ^ 2 * ∑ i, ℓ i ^ 2) ≤
      ∫ ξ, Real.exp (-(θ * ∑ i, ℓ i * ξ i)) ∂(Measure.pi fun _ : Fin N => ν) := by
  have hfac (ξ : Fin N → ℝ) : Real.exp (-(θ * ∑ i, ℓ i * ξ i)) =
      ∏ i, Real.exp (-(θ * ℓ i * ξ i)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
    simp only [mul_assoc]
  have hi (i : Fin N) : Real.exp (q * a ^ 2 / 8 * (θ * ℓ i) ^ 2) ≤
      ∫ z, Real.exp (-(θ * ℓ i * z)) ∂ν := by
    have hlower := integral_exp_neg_lower ν hint hmean ha (mul_nonneg hθ (hℓ i)) htail (hexp i)
    have hpos : 0 < ∫ z, Real.exp (-(θ * ℓ i * z)) ∂ν := by
      have : 0 ≤ q * a ^ 2 / 4 * (θ * ℓ i) ^ 2 := by positivity
      linarith
    have hlog := log_integral_exp_neg_lower ν hint hmean ha hq (mul_nonneg hθ (hℓ i))
      htail (hexp i) (hsmall i)
    exact (Real.le_log_iff_exp_le hpos).mp hlog
  calc Real.exp (q * a ^ 2 / 8 * θ ^ 2 * ∑ i, ℓ i ^ 2)
      = ∏ i, Real.exp (q * a ^ 2 / 8 * (θ * ℓ i) ^ 2) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∏ i, ∫ z, Real.exp (-(θ * ℓ i * z)) ∂ν :=
      Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) (fun i _ => hi i)
    _ = ∫ ξ : Fin N → ℝ, ∏ i, Real.exp (-(θ * ℓ i * ξ i)) ∂(Measure.pi fun _ => ν) :=
      (integral_fintype_prod_eq_prod (fun i z => Real.exp (-(θ * ℓ i * z)))).symm
    _ = ∫ ξ, Real.exp (-(θ * ∑ i, ℓ i * ξ i)) ∂(Measure.pi fun _ : Fin N => ν) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ξ => (hfac ξ).symm)

/-- A second-moment lower bound for a tail, with explicit constants. -/
theorem measure_lower_tail_of_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hXm : Measurable X) (hX : Integrable X μ) (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : a ≤ ∫ ω, X ω ∂μ) (hm2 : (∫ ω, X ω ^ 2 ∂μ) ≤ b) :
    a ^ 2 / (16 * b) ≤ μ.real {ω | a / 2 < X ω} := by
  classical
  set A := {ω | a / 2 < X ω}
  set S := 4 * b / a
  have hS : 0 < S := by dsimp [S]; positivity
  have hA : MeasurableSet A := measurableSet_lt measurable_const hXm
  have hi : Integrable (A.indicator (1 : Ω → ℝ)) μ := (integrable_const 1).indicator hA
  have hpt (ω : Ω) : X ω ≤ a / 2 + S * A.indicator (1 : Ω → ℝ) ω + X ω ^ 2 / S := by
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      change X ω ≤ a / 2 + S * 1 + X ω ^ 2 / S
      by_cases hle : X ω ≤ S
      · have := div_nonneg (sq_nonneg (X ω)) hS.le
        linarith
      · have hsq : X ω ≤ X ω ^ 2 / S := by
          rw [le_div_iff₀ hS]
          have hx : S < X ω := lt_of_not_ge hle
          nlinarith
        linarith
    · rw [Set.indicator_of_notMem hω]
      have hx : X ω ≤ a / 2 := le_of_not_gt hω
      have := div_nonneg (sq_nonneg (X ω)) hS.le
      linarith
  have hbound := integral_mono hX
    (((integrable_const (a / 2)).add (hi.const_mul S)).add (hX2.div_const S)) hpt
  simp only [Pi.add_apply] at hbound
  rw [integral_add (f := fun ω => a / 2 + S * A.indicator (1 : Ω → ℝ) ω)
      ((integrable_const _).add (hi.const_mul _)) (hX2.div_const _),
    integral_add (integrable_const _) (hi.const_mul _), integral_const,
    integral_const_mul, integral_div, integral_indicator_one hA,
    probReal_univ, smul_eq_mul, one_mul] at hbound
  have hdiv : (∫ ω, X ω ^ 2 ∂μ) / S ≤ a / 4 := by
    have h := div_le_div_of_nonneg_right hm2 hS.le
    have he : b / S = a / 4 := by dsimp [S]; field_simp
    rwa [he] at h
  have hkey : a / (4 * S) ≤ μ.real A := by
    rw [div_le_iff₀ (by positivity : 0 < 4 * S)]
    nlinarith
  convert hkey using 1
  dsimp [S]
  field_simp
  norm_num

/-- Exponential first and second moments force a negative deviation. -/
theorem measure_neg_tail_of_exp_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Measurable Z)
    {a b θ Q : ℝ} (ha : 0 ≤ a) (hθ : 0 < θ) (hQ : 0 ≤ Q)
    (hi : Integrable (fun ω => Real.exp (-(θ * Z ω))) μ)
    (hi2 : Integrable (fun ω => Real.exp (-(2 * θ * Z ω))) μ)
    (hlower : Real.exp (a * θ ^ 2 * Q) ≤ ∫ ω, Real.exp (-(θ * Z ω)) ∂μ)
    (hupper : (∫ ω, Real.exp (-(2 * θ * Z ω)) ∂μ) ≤ Real.exp (b * θ ^ 2 * Q))
    (hlarge : 2 * Real.log 2 ≤ a * θ ^ 2 * Q) :
    Real.exp (-(b * θ ^ 2 * Q)) / 16 ≤ μ.real {ω | a * θ / 2 * Q < -Z ω} := by
  set X := fun ω => Real.exp (-(θ * Z ω))
  have hX2 (ω : Ω) : X ω ^ 2 = Real.exp (-(2 * θ * Z ω)) := by
    dsimp [X]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hXi2 : Integrable (fun ω => X ω ^ 2) μ :=
    hi2.congr (Filter.Eventually.of_forall fun ω => (hX2 ω).symm)
  have hXm2 : (∫ ω, X ω ^ 2 ∂μ) ≤ Real.exp (b * θ ^ 2 * Q) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hX2)]
    exact hupper
  have hprob := measure_lower_tail_of_moments μ X ((hZ.const_mul θ).neg.exp) hi hXi2
    (Real.exp_pos _) (Real.exp_pos _) hlower hXm2
  have hsub : {ω | Real.exp (a * θ ^ 2 * Q) / 2 < X ω}
      ⊆ {ω | a * θ / 2 * Q < -Z ω} := by
    intro ω hω
    change Real.exp (a * θ ^ 2 * Q) / 2 < Real.exp (-(θ * Z ω)) at hω
    have hhalf : 2 ≤ Real.exp (a * θ ^ 2 * Q / 2) := by
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    have hid : Real.exp (a * θ ^ 2 * Q / 2) ^ 2 = Real.exp (a * θ ^ 2 * Q) := by
      rw [sq, ← Real.exp_add, add_halves]
    have hthreshold : Real.exp (a * θ ^ 2 * Q / 2) ≤ Real.exp (a * θ ^ 2 * Q) / 2 := by
      nlinarith [sq_nonneg (Real.exp (a * θ ^ 2 * Q / 2) - 2)]
    have h := Real.exp_lt_exp.mp (hthreshold.trans_lt hω)
    change a * θ / 2 * Q < -Z ω
    nlinarith
  have hA : 1 ≤ Real.exp (a * θ ^ 2 * Q) := Real.one_le_exp_iff.mpr (by positivity)
  have hquot : Real.exp (-(b * θ ^ 2 * Q)) / 16 ≤
      Real.exp (a * θ ^ 2 * Q) ^ 2 / (16 * Real.exp (b * θ ^ 2 * Q)) := by
    rw [Real.exp_neg]
    have he : (Real.exp (b * θ ^ 2 * Q))⁻¹ / 16 = 1 / (16 * Real.exp (b * θ ^ 2 * Q)) := by ring
    rw [he]
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  exact hquot.trans (hprob.trans (measureReal_mono hsub (measure_ne_top _ _)))

end Sandpile
