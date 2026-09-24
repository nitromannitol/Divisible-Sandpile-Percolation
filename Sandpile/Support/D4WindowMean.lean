/-
The mean of the reflection window at superdiffusive times, the first half of
Step 3 of `prop:d4-superdiffusive-limit` (`sandpile.tex:3389-3392`):

  `E S_R(0) ≤ C n_R log(t_R + 2)/(t_R − n_R) ⟶ 0` .

The window mean is the growth of the mean odometer over the window
(`integral_reflectionSum`), the increments of that mean are nonincreasing
(`meanOdometerOf_window_le`), and the mean odometer itself is at most
`C log(t+2)` (`exists_crude_log_upper_four`).  Together these give the bound in
cleared-denominator form, with no side condition beyond `n ≤ t`.  At
`t_R = ⌊R^α⌋` and `n_R = ⌊R √t_R⌋` with `α > 2` the majorant vanishes, because
`log(t_R+2) ≥ 1` turns it into the second limit of
`eq:d4-superdiffusive-scale-separation`.
-/
import Sandpile.Support.D4Reflection
import Sandpile.Support.D4Mean
import Sandpile.Support.D4Scale
import Sandpile.Support.D4ScaleSepLimits

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

/-- **The window mean bound** `eq:d4-reflection-window-mean-bound` combined with
the logarithmic upper bound on the mean odometer, in cleared-denominator form:
`(t−n) E S(0) ≤ C n log(t+2)`. -/
theorem window_mean_bound_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (hint : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n t : ℕ, n ≤ t → ∀ x : Site 4,
      ((t - n : ℕ) : ℝ) * (∫ ζ, reflectionSum ζ n t x ∂(LatticeProb.iidLaw 4 ν))
        ≤ C * (n : ℝ) * Real.log ((t : ℝ) + 2) := by
  obtain ⟨C, hC, hlog⟩ :=
    exists_crude_log_upper_four hVS ν hprob hmean θ₀ K₀ hθ₀ hexpint hexp hint hpos
  refine ⟨C, hC, fun n t hn x => ?_⟩
  rw [integral_reflectionSum (by norm_num) ν hint hmean hpos x n t hn]
  refine (meanOdometerOf_window_le (by norm_num) ν hint hmean hpos n t hn).trans ?_
  have h1 := hlog (t - n)
  have hsub : ((t - n : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast Nat.sub_le t n
  have hmono : Real.log (((t - n : ℕ) : ℝ) + 2) ≤ Real.log ((t : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hstep : (∫ ζ, odometerOf ζ (t - n) 0 ∂(LatticeProb.iidLaw 4 ν))
      ≤ C * Real.log ((t : ℝ) + 2) := h1.trans (mul_le_mul_of_nonneg_left hmono hC.le)
  calc (n : ℝ) * ∫ ζ, odometerOf ζ (t - n) 0 ∂(LatticeProb.iidLaw 4 ν)
      ≤ (n : ℝ) * (C * Real.log ((t : ℝ) + 2)) := mul_le_mul_of_nonneg_left hstep hn0
    _ = C * (n : ℝ) * Real.log ((t : ℝ) + 2) := by ring

/-- **The window mean vanishes at superdiffusive times**
(`sandpile.tex:3389-3392`).  This is the first half of Step 3 of
`prop:d4-superdiffusive-limit`. -/
theorem tendsto_window_mean_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (hint : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν)
    (α : ℝ) (hα : 2 < α) (x : Site 4) :
    Tendsto (fun R : ℝ =>
        ∫ ζ, reflectionSum ζ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x
          ∂(LatticeProb.iidLaw 4 ν)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ :=
    window_mean_bound_four hVS ν hprob hmean θ₀ K₀ hθ₀ hexpint hexp hint hpos
  have hmaj : Tendsto (fun R : ℝ => C *
      ((⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2
        / ((⌊R ^ α⌋₊ : ℝ) - (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ)))) atTop (𝓝 0) := by
    simpa using (Sandpile.D4Super.tendsto_scale_sep_second α hα).const_mul C
  refine squeeze_zero' (Eventually.of_forall (fun R => ?_)) ?_ hmaj
  · exact integral_nonneg (fun ζ => reflectionSum_nonneg ζ _ _ x)
  filter_upwards [eventually_ge_atTop (2 : ℝ), Sandpile.D4Super.nR_le_half_floor α hα]
    with R hR hhalf
  set t : ℕ := ⌊R ^ α⌋₊ with hts
  set n : ℕ := ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ with hns
  have ht4 : (4 : ℝ) ≤ (t : ℝ) := Sandpile.D4Super.four_le_floor_rpow α hα R hR
  have hnt : n ≤ t := by
    have : (n : ℝ) ≤ (t : ℝ) := by linarith
    exact_mod_cast this
  have hcast : ((t - n : ℕ) : ℝ) = (t : ℝ) - (n : ℝ) := Nat.cast_sub hnt
  have hgap : (0 : ℝ) < (t : ℝ) - (n : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log ((t : ℝ) + 2) :=
    (log_time_bounds_four (by linarith : (3 : ℝ) ≤ (t : ℝ))).2.2.1
  have hbnd := hb n t hnt x
  rw [hcast] at hbnd
  have hsq : Real.log ((t : ℝ) + 2) ≤ Real.log ((t : ℝ) + 2) ^ 2 := by nlinarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [show C * ((n : ℝ) * Real.log ((t : ℝ) + 2) ^ 2 / ((t : ℝ) - (n : ℝ)))
      = C * (n : ℝ) * Real.log ((t : ℝ) + 2) ^ 2 / ((t : ℝ) - (n : ℝ)) by ring,
    le_div_iff₀ hgap, mul_comm _ ((t : ℝ) - (n : ℝ))]
  refine hbnd.trans ?_
  nlinarith [hsq, hn0, hC, mul_nonneg hC.le hn0]

end Sandpile
