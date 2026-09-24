/-
The square-integrability clauses of `cor:dlt4-mean-asymptotic`
(`sandpile.tex:2034-2052`).

The corollary's first two clauses are the `MemLp` statements that license the
expectations and variances below: the rescaled odometer
`𝒰_R(T,x) = R^{-(2-d/2)}u_{⌊R²T⌋}(⌊Rx⌋)` and the odometer `u_t(0)` are square
integrable under the centered mass law.  Both are the odometer's square
integrability (`Sandpile.Support.memLp_two_odometer`) with the constant and the
floor of the rescaling pulled out.
-/
import Sandpile.Support.TightD4Covariance
import Sandpile.Support.ContMeanGrowth
import Sandpile.Support.ExplMeanAsymptotic
import Sandpile.Support.MeanAValue

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

/-- **The rescaled odometer is square integrable.**  First clause of
`cor:dlt4-mean-asymptotic`. -/
theorem memLp_rescaledOdometer_centered (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (R T : ℝ) (x : Sandpile.Continuum.Space d) :
    MemLp (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ) 2
      (Sandpile.centeredMassLaw d ν) := by
  unfold Continuum.rescaledOdometer
  exact (Sandpile.Support.memLp_two_odometer ν hsq hd ⌊R ^ 2 * T⌋₊ fun i => ⌊R * x i⌋).const_mul _

/-- **The odometer is square integrable.**  Second clause of
`cor:dlt4-mean-asymptotic`. -/
theorem memLp_odometer_nat_centered (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (t : ℕ) :
    MemLp (fun σ => Sandpile.odometer σ t 0) 2 (Sandpile.centeredMassLaw d ν) :=
  Sandpile.Support.memLp_two_odometer ν hsq hd t 0

/-- **The mean ratio limit.**  Ninth clause of `cor:dlt4-mean-asymptotic`, from
`exists_growth_limit_of_ratio` at `a = (4-d)/4`. -/
theorem tendsto_mean_ratio (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (L : ℝ) (hL : 0 < L)
    (h : Tendsto (fun t : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t /
        (L * (t : ℝ) ^ ((4 - (d : ℝ)) / 4))) atTop (𝓝 1)) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun t : ℕ =>
      (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 M) :=
  Sandpile.Support.exists_growth_limit_of_ratio ((4 - (d : ℝ)) / 4) L hL _ h

/-- **The variance ratio limit.**  Tenth clause of `cor:dlt4-mean-asymptotic`, from
`exists_growth_limit_of_ratio` at `a = (4-d)/2`. -/
theorem tendsto_variance_ratio (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (L : ℝ) (hL : 0 < L)
    (h : Tendsto (fun t : ℕ =>
        variance (fun σ => Sandpile.odometer σ t 0) (Sandpile.centeredMassLaw d ν) /
        (L * (t : ℝ) ^ ((4 - (d : ℝ)) / 2))) atTop (𝓝 1)) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun t : ℕ =>
      (t : ℝ) ^ (-((4 - (d : ℝ)) / 2)) *
        variance (fun σ => Sandpile.odometer σ t 0) (Sandpile.centeredMassLaw d ν))
      atTop (𝓝 M) :=
  Sandpile.Support.exists_growth_limit_of_ratio ((4 - (d : ℝ)) / 2) L hL _ h

/-- **The two ratio clauses of `cor:dlt4-mean-asymptotic` from the two limit
identities.**  Ninth and tenth clauses from the fifth and seventh. -/
theorem dlt4_mean_asymptotic_ratios (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (L V : ℝ) (hL : L ≠ 0) (hV : V ≠ 0)
    (hMean : Tendsto (fun R : ℝ => ∫ σ,
        Sandpile.Continuum.rescaledOdometer d R 1 0 σ
        ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 L))
    (hVar : Tendsto (fun R : ℝ => variance
        (fun σ => Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
        (Sandpile.centeredMassLaw d ν)) atTop (𝓝 V)) :
    Tendsto (fun t : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t /
        (L * (t : ℝ) ^ ((4 - (d : ℝ)) / 4))) atTop (𝓝 1) ∧
      Tendsto (fun t : ℕ =>
        variance (fun σ => Sandpile.odometer σ t 0) (Sandpile.centeredMassLaw d ν) /
        (V * (t : ℝ) ^ ((4 - (d : ℝ)) / 2))) atTop (𝓝 1) :=
  ⟨tendsto_mean_ratio_of_rescaled d ν L hL hMean,
    tendsto_variance_ratio_of_rescaled d ν V hV hVar⟩

/-- **`cor:dlt4-mean-asymptotic` assembled from its two limit identities.**
Clauses one, two, nine and ten, granted the convergence of the rescaled means
and variances (clauses five and seven), which are the convergence in
distribution of the rescaled odometer together with the uniform integrability
of clause two. -/
theorem dlt4_mean_asymptotic_of_limits (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hsq : Integrable (fun z => z ^ 2) ν)
    (L V : ℝ) (hL : 0 < L) (hV : 0 < V)
    (hMean : Tendsto (fun R : ℝ => ∫ σ,
        Sandpile.Continuum.rescaledOdometer d R 1 0 σ
        ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 L))
    (hVar : Tendsto (fun R : ℝ => variance
        (fun σ => Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
        (Sandpile.centeredMassLaw d ν)) atTop (𝓝 V)) :
    (∀ R : ℝ, 1 ≤ R → MemLp (fun σ =>
        Sandpile.Continuum.rescaledOdometer d R 1 0 σ) 2
        (Sandpile.centeredMassLaw d ν)) ∧
      (∀ t : ℕ, MemLp (fun σ => Sandpile.odometer σ t 0) 2
        (Sandpile.centeredMassLaw d ν)) ∧
      Tendsto (fun t : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t /
          (L * (t : ℝ) ^ ((4 - (d : ℝ)) / 4))) atTop (𝓝 1) ∧
      Tendsto (fun t : ℕ =>
          variance (fun σ => Sandpile.odometer σ t 0) (Sandpile.centeredMassLaw d ν) /
          (V * (t : ℝ) ^ ((4 - (d : ℝ)) / 2))) atTop (𝓝 1) :=
  ⟨fun R _hR => memLp_rescaledOdometer_centered d hd ν hsq R 1 0,
    fun t => memLp_odometer_nat_centered d hd ν hsq t,
    tendsto_mean_ratio_of_rescaled d ν L (ne_of_gt hL) hMean,
    tendsto_variance_ratio_of_rescaled d ν V (ne_of_gt hV) hVar⟩

/-- Two-sided exponential integrability gives the second moment. -/
theorem memLp_two_of_integrable_exp_mul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hpos : Integrable (fun ω => Real.exp (θ * f ω)) P)
    (hneg : Integrable (fun ω => Real.exp (-θ * f ω)) P) :
    MemLp f 2 P := by
  have h2 : Integrable (fun ω => f ω ^ 2) P :=
    integrable_pow_of_integrable_exp_mul (ne_of_gt hθ) hpos hneg 2
  have hfmeas : AEMeasurable f P :=
    Real.aemeasurable_of_aemeasurable_exp_mul (ne_of_gt hθ)
      hpos.aestronglyMeasurable.aemeasurable
  exact (memLp_two_iff_integrable_sq hfmeas.aestronglyMeasurable).mpr h2

/-- An exponential moment in the absolute value, together with measurability,
gives the second moment. -/
theorem memLp_two_of_integrable_exp_abs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (θ : ℝ) (hθ : 0 < θ) (hf : AEMeasurable f P)
    (hint : Integrable (fun ω => Real.exp (θ * |f ω|)) P) :
    MemLp f 2 P := by
  exact memLp_two_of_integrable_exp_mul P f θ hθ
    (hint.mono' ((hf.const_mul θ).exp.aestronglyMeasurable) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self (f ω)) hθ.le)))
    (hint.mono' ((hf.const_mul (-θ)).exp.aestronglyMeasurable) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp.mpr (by nlinarith [neg_le_abs (f ω), abs_nonneg (f ω), hθ.le])))


/-- The exponential moment of the continuum value in the absolute value,
together with its measurability, gives its square integrability. -/
theorem memLp_continuumValue_of_exp_moment {ΩW ΩB : Type*} [MeasurableSpace ΩW]
    [MeasurableSpace ΩB] (d : ℕ) (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (PB : Measure ΩB) (PW : Measure ΩW)
    (θ : ℝ) (hθ : 0 < θ)
    (hmeas : AEMeasurable (fun ω =>
      Sandpile.Continuum.continuumValue d Z B PB 1 0 ω) PW)
    (hint : Integrable (fun ω => Real.exp (θ *
      |Sandpile.Continuum.continuumValue d Z B PB 1 0 ω|)) PW) :
    MemLp (fun ω =>
      Sandpile.Continuum.continuumValue d Z B PB 1 0 ω) 2 PW := by
  exact memLp_two_of_integrable_exp_abs PW (fun ω =>
    Sandpile.Continuum.continuumValue d Z B PB 1 0 ω) θ hθ hmeas hint

end Sandpile.Support
