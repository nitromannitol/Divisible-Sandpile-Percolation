import Sandpile.Support.MeanAValue

/-!
# The mean and variance asymptotic from the rescaled corollary

The last two clauses of `cor:dlt4-mean-asymptotic` (`sandpile.tex:2034-2052`)
from the first two.  The corollary asserts

  `E 𝒰_R(T,x) → E 𝒰(T,x)`,   `Var 𝒰_R(T,x) → T^{(4-d)/2} Var 𝒰(1,0)`,

and then, "consequently",

  `E u_t(0) ∼ E𝒰(1,0) t^{(4-d)/4}`,   `Var(u_t(0)) ∼ Var(𝒰(1,0)) t^{(4-d)/2}`.

The word "consequently" is the substitution `R = √t` at `T = 1`, `x = 0`.  By the
definition of the rescaled odometer at `sandpile.tex:1817-1821`,

  `𝒰_{√t}(1,0) = t^{-(4-d)/4} u_t(0)`,

since `⌊(√t)² · 1⌋ = t` and `(√t)^{-(2-d/2)} = t^{-(4-d)/4)}`; and `√t → ∞`.  So
the limit of the means along `R = √t` is exactly the asymptotic of `E u_t(0)`,
and the limit of the variances is exactly the asymptotic of `Var(u_t(0))`,
because the variance of a constant multiple is the square of the constant times
the variance.

Both asymptotics are ratios, so both need their limit constant to be nonzero;
the corollary supplies `Var 𝒰(1,0) > 0` itself, and `E𝒰(1,0) > 0` is the third
clause of `prop:continuum-value-selfsimilar` at `p = 1`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.Support

/-- The rescaled odometer at the parabolic scale `R = √t`, time one and the
origin is the rescaled odometer at time `t`. -/
theorem rescaledOdometer_sqrt (d : ℕ) (t : ℕ) (σ : Sandpile.Site d → ℝ) :
    Sandpile.Continuum.rescaledOdometer d (Real.sqrt t) 1 0 σ
      = (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * Sandpile.odometer σ t 0 := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  unfold Sandpile.Continuum.rescaledOdometer
  have hsq : Real.sqrt (t : ℝ) ^ 2 * 1 = (t : ℝ) := by
    rw [mul_one, Real.sq_sqrt ht0]
  have hidx : (fun i => ⌊Real.sqrt (t : ℝ) * (0 : Sandpile.Continuum.Space d) i⌋)
      = (0 : Sandpile.Site d) := by
    funext i
    simp
  have hexp : Real.sqrt (t : ℝ) ^ (-(2 - (d : ℝ) / 2)) = (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0]
    congr 1
    ring
  rw [hsq, Nat.floor_natCast, hidx, hexp]

/-- `√t → ∞` along the naturals. -/
theorem tendsto_sqrt_nat_atTop :
    Tendsto (fun t : ℕ => Real.sqrt t) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

/-- From a limit of `t^{-a} f t` to the asymptotic `f t ∼ L t^a`. -/
theorem tendsto_ratio_of_tendsto_rpow_neg_mul (a L : ℝ) (hL : L ≠ 0) (f : ℕ → ℝ)
    (h : Tendsto (fun t : ℕ => (t : ℝ) ^ (-a) * f t) atTop (𝓝 L)) :
    Tendsto (fun t : ℕ => f t / (L * (t : ℝ) ^ a)) atTop (𝓝 1) := by
  have hdiv : Tendsto (fun t : ℕ => ((t : ℝ) ^ (-a) * f t) / L) atTop (𝓝 (L / L)) :=
    h.div_const L
  rw [div_self hL] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ht
  have hne : (t : ℝ) ^ a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos htpos a)
  rw [Real.rpow_neg (le_of_lt htpos)]
  field_simp

/-- **The mean asymptotic from the convergence of the rescaled means.**  This is
the word "consequently" of `cor:dlt4-mean-asymptotic`, first display. -/
theorem tendsto_mean_ratio_of_rescaled (d : ℕ) (ν : Measure ℝ) (L : ℝ) (hL : L ≠ 0)
    (h : Tendsto (fun R : ℝ => ∫ σ, Sandpile.Continuum.rescaledOdometer d R 1 0 σ
        ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 L)) :
    Tendsto (fun t : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t /
        (L * (t : ℝ) ^ ((4 - (d : ℝ)) / 4))) atTop (𝓝 1) := by
  refine tendsto_ratio_of_tendsto_rpow_neg_mul ((4 - (d : ℝ)) / 4) L hL _ ?_
  have hcomp := h.comp tendsto_sqrt_nat_atTop
  refine hcomp.congr fun t => ?_
  simp only [Function.comp_apply, Sandpile.meanOdometer]
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun σ => rescaledOdometer_sqrt d t σ)

/-- **The variance asymptotic from the convergence of the rescaled variances.**
This is the word "consequently" of `cor:dlt4-mean-asymptotic`, second display:
the variance of `c · u_t(0)` is `c²` times the variance of `u_t(0)`, and
`(t^{-(4-d)/4})² = t^{-(4-d)/2}`. -/
theorem tendsto_variance_ratio_of_rescaled (d : ℕ) (ν : Measure ℝ) (V : ℝ) (hV : V ≠ 0)
    (h : Tendsto (fun R : ℝ => variance
        (fun σ => Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
        (Sandpile.centeredMassLaw d ν)) atTop (𝓝 V)) :
    Tendsto (fun t : ℕ =>
        variance (fun σ => Sandpile.odometer σ t 0) (Sandpile.centeredMassLaw d ν) /
        (V * (t : ℝ) ^ ((4 - (d : ℝ)) / 2))) atTop (𝓝 1) := by
  refine tendsto_ratio_of_tendsto_rpow_neg_mul ((4 - (d : ℝ)) / 2) V hV _ ?_
  have hcomp := h.comp tendsto_sqrt_nat_atTop
  refine hcomp.congr fun t => ?_
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hfun : (fun σ => Sandpile.Continuum.rescaledOdometer d (Real.sqrt t) 1 0 σ)
      = fun σ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * Sandpile.odometer σ t 0 := by
    funext σ
    exact rescaledOdometer_sqrt d t σ
  have hsq : ((t : ℝ) ^ (-((4 - (d : ℝ)) / 4))) ^ 2 = (t : ℝ) ^ (-((4 - (d : ℝ)) / 2)) := by
    rw [← Real.rpow_natCast ((t : ℝ) ^ (-((4 - (d : ℝ)) / 4))) 2, ← Real.rpow_mul ht0]
    congr 1
    push_cast
    ring
  simp only [Function.comp_apply, hfun]
  rw [variance_const_mul, hsq]

/-- The first clause of `cor:dlt4-mean-asymptotic` reduces to square integrability
of the odometer itself: the rescaled odometer is a constant multiple of it. -/
theorem memLp_rescaledOdometer (d : ℕ) (R T : ℝ) (x : Sandpile.Continuum.Space d)
    (P : Measure (Sandpile.Site d → ℝ))
    (h : MemLp (fun σ => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ fun i => ⌊R * x i⌋) 2 P) :
    MemLp (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ) 2 P := by
  unfold Sandpile.Continuum.rescaledOdometer
  exact h.const_mul _

/-- The scaling identity for the mean, `E𝒰(T,x) = T^{(4-d)/4} E𝒰(1,0)`, is the third
clause of `prop:continuum-value-selfsimilar` at `p = 1`. -/
theorem continuumValue_mean_scaling {ΩW ΩB : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩB]
    (d : ℕ) (PW : Measure ΩW)
    (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (PB : Measure ΩB) (T : ℝ) (x : Sandpile.Continuum.Space d)
    (h : ∫ ω, Sandpile.Continuum.continuumValue d Z B PB T x ω ^ (1 : ℝ) ∂PW
        = T ^ (1 * (4 - (d : ℝ)) / 4) *
          ∫ ω, Sandpile.Continuum.continuumValue d Z B PB 1 0 ω ^ (1 : ℝ) ∂PW) :
    ∫ ω, Sandpile.Continuum.continuumValue d Z B PB T x ω ∂PW
      = T ^ ((4 - (d : ℝ)) / 4) *
        ∫ ω, Sandpile.Continuum.continuumValue d Z B PB 1 0 ω ∂PW := by
  simpa [Real.rpow_one, one_mul] using h

/-- The variance of the rescaled odometer is the square of the scale factor times the
variance of the odometer, which is what turns clause seven of the corollary into the
variance asymptotic. -/
theorem variance_rescaledOdometer (d : ℕ) (R T : ℝ) (x : Sandpile.Continuum.Space d)
    (P : Measure (Sandpile.Site d → ℝ)) :
    variance (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ) P
      = (R ^ (-(2 - (d : ℝ) / 2))) ^ 2 *
        variance (fun σ => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ fun i => ⌊R * x i⌋) P := by
  unfold Sandpile.Continuum.rescaledOdometer
  exact variance_const_mul _ _ _

end Sandpile.Support
