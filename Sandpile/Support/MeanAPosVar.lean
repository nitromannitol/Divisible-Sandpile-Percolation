/-
The limiting variance is positive: `sandpile.tex:2024-2026` and the last clause
of `cor:dlt4-mean-asymptotic` (`sandpile.tex:2043`).

The paper's sentence is that `𝒰(1,0) ≥ max{Z(1,0),0}` and that `Z(1,0)` is a
nondegenerate centred Gaussian, so the value is not almost surely constant.
Three steps are needed.

* The law of `Z(1,0)` is the centred Gaussian of variance
  `Var(ζ(0))‖g_1^{BM}(0,·)‖²`, which is the law of the increment of the field
  between `(1,0)` and `(0,0)` because the field vanishes at time zero.
* That variance is positive: the `L²` pairing of the Green kernel with itself is
  the double time integral of the heat kernel on the diagonal
  (`integral_greenTimeBM_mul_prod`), the heat kernel on the diagonal is
  decreasing in time, and the time square has unit area, so the pairing is at
  least `p_2^{BM}(0,0) > 0`.
* A centred Gaussian of positive variance charges every half-line `(M,∞)`,
  because Lebesgue measure is absolutely continuous with respect to it.

With `𝒰(1,0) ≥ Z(1,0)` from `MeanAZeroTime`, a variable dominating an unbounded
variable has positive variance, which is `variance_pos_of_ae_le_unbounded`.
-/
import Sandpile.Support.MeanAGauss
import Sandpile.Support.MeanAZeroTime
import Sandpile.Support.MeanAPositive

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The heat kernel on the diagonal is decreasing in time. -/
theorem heatKernelBM_diag_antitone (hd : 1 ≤ d) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    heatKernelBM d t 0 0 ≤ heatKernelBM d s 0 0 := by
  have hdpos : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hzero : ‖(0 : Space d) - 0‖ ^ 2 = 0 := by simp
  unfold heatKernelBM
  rw [hzero]
  have he : ∀ r : ℝ, Real.exp (-(d : ℝ) * 0 / (2 * r)) = 1 := by
    intro r; norm_num
  rw [he, he, mul_one, mul_one]
  have hx : (0 : ℝ) < 4 * Real.pi * s / (2 * (d : ℝ)) := by
    have := Real.pi_pos
    positivity
  have hxy : 4 * Real.pi * s / (2 * (d : ℝ)) ≤ 4 * Real.pi * t / (2 * (d : ℝ)) := by
    have hpi := Real.pi_pos
    gcongr
  have hz : (-(d : ℝ) / 2) ≤ 0 := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  exact Real.rpow_le_rpow_of_nonpos hx hxy hz

/-- **The Green kernel of the unit time horizon is not null in `L²`.** -/
theorem integral_greenTimeBM_sq_pos (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    0 < ∫ w : Space d, greenTimeBM d 1 0 w ^ 2 := by
  have hkey : (fun w : Space d => greenTimeBM d 1 0 w ^ 2)
      = fun w : Space d => greenTimeBM d 1 0 w * greenTimeBM d 1 0 w := by
    funext w; ring
  rw [hkey, integral_greenTimeBM_mul_prod hd hd3 zero_le_one zero_le_one 0 0]
  set mu := (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict (Set.Ioo (0 : ℝ) 1))
    with hmu
  have hc : 0 < heatKernelBM d 2 0 0 := heatKernelBM_pos hd (by norm_num) 0 0
  have hrestr : mu = (volume.prod volume).restrict
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
    rw [hmu, Measure.prod_restrict]
  have hfin : mu Set.univ = 1 := by
    rw [hmu, ← Set.univ_prod_univ, Measure.prod_prod]
    simp
  haveI : IsProbabilityMeasure mu := ⟨hfin⟩
  have hae : ∀ᵐ p : ℝ × ℝ ∂mu, heatKernelBM d 2 0 0 ≤ heatKernelBM d (p.1 + p.2) 0 0 := by
    rw [hrestr]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    exact heatKernelBM_diag_antitone hd (by linarith [hp.1.1, hp.2.1])
      (by linarith [hp.1.2, hp.2.2])
  have hmono := integral_mono_ae (integrable_const (heatKernelBM d 2 0 0))
    (integrable_diagKernel hd hd3 (t := (1:ℝ)) (t' := (1:ℝ)) 0 0) hae
  rw [integral_const, measureReal_def, hfin] at hmono
  simp only [ENNReal.toReal_one, smul_eq_mul, one_mul] at hmono
  linarith

/-- **The law of the field at `(1,0)`.**  The field vanishes at time zero, so the
value at `(1,0)` is the increment from `(0,0)`. -/
theorem map_gaussianPotential_one_zero {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2) :
    PW.map (fun ω => gaussianPotential d ν2 W 1 0 ω)
      = gaussianReal 0 (Real.toNNReal (ν2 * ∫ w : Space d, greenTimeBM d 1 0 w ^ 2)) := by
  have hsub := map_gaussianPotential_sub PW W hW hd hd3 hν2 (t := (1:ℝ)) (s := (0:ℝ))
    zero_le_one le_rfl (0 : Space d) (0 : Space d)
  have hzero : (fun ω => gaussianPotential d ν2 W 1 0 ω - gaussianPotential d ν2 W 0 0 ω)
      =ᵐ[PW] fun ω => gaussianPotential d ν2 W 1 0 ω := by
    filter_upwards [gaussianPotential_zero_time PW W hW ν2 (0 : Space d)] with ω hω
    rw [hω, sub_zero]
  rw [Measure.map_congr hzero] at hsub
  have hg : ∀ w : Space d, greenTimeBM d 0 (0 : Space d) w = 0 := fun w =>
    congrFun (greenTimeBM_zero_time d (0 : Space d)) w
  simp only [hg, sub_zero] at hsub
  exact hsub

/-- **A centred Gaussian of positive variance charges every half-line.** -/
theorem gaussianReal_Ioi_ne_zero {v : ℝ≥0} (hv : v ≠ 0) (M : ℝ) :
    gaussianReal 0 v (Set.Ioi M) ≠ 0 := by
  intro h
  have hac : (volume : Measure ℝ) ≪ gaussianReal 0 v :=
    gaussianReal_absolutelyContinuous' 0 hv
  have hvol : (volume : Measure ℝ) (Set.Ioi M) = 0 := hac h
  rw [Real.volume_Ioi] at hvol
  exact ENNReal.top_ne_zero hvol

/-- **The field at `(1,0)` is unbounded above.** -/
theorem field_one_zero_unbounded {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 < ν2)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω)
    (M : ℝ) : PW {ω | M < Z 1 0 ω} ≠ 0 := by
  have hmeas : Measurable (fun ω => gaussianPotential d ν2 W 1 0 ω) := by
    have := hW.meas (fun y => greenTimeBM d 1 0 y) (memLp_greenTimeBM hd hd3 zero_le_one 0)
    exact this.const_mul _
  have hset : {ω | M < Z 1 0 ω} =ᵐ[PW] {ω | M < gaussianPotential d ν2 W 1 0 ω} := by
    filter_upwards [hZmod 1 0] with ω hω
    show (M < Z 1 0 ω) = (M < gaussianPotential d ν2 W 1 0 ω)
    rw [hω]
  rw [measure_congr hset]
  have hmap : PW {ω | M < gaussianPotential d ν2 W 1 0 ω}
      = gaussianReal 0 (Real.toNNReal (ν2 * ∫ w : Space d, greenTimeBM d 1 0 w ^ 2))
        (Set.Ioi M) := by
    rw [← map_gaussianPotential_one_zero PW W hW hd hd3 hν2.le,
      Measure.map_apply hmeas measurableSet_Ioi]
    rfl
  rw [hmap]
  refine gaussianReal_Ioi_ne_zero ?_ M
  have hpos : 0 < ν2 * ∫ w : Space d, greenTimeBM d 1 0 w ^ 2 :=
    mul_pos hν2 (integral_greenTimeBM_sq_pos hd hd3)
  simpa using (Real.toNNReal_pos.2 hpos).ne'

/-- **The limiting variance is positive**, the last clause of
`cor:dlt4-mean-asymptotic`. -/
theorem variance_continuumValue_pos {ΩW ΩB : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩB]
    (PW : Measure ΩW) [IsProbabilityMeasure PW] (PB : Measure ΩB)
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 < ν2)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (B : Space d → ℝ≥0 → ΩB → Space d)
    (hL2 : MemLp (fun ω => continuumValue d Z B PB 1 0 ω) 2 PW) :
    0 < variance (fun ω => continuumValue d Z B PB 1 0 ω) PW :=
  variance_pos_of_ae_le_unbounded PW _ (fun ω => Z 1 0 ω) hL2
    (ae_field_le_continuumValue PW PB W hW ν2 Z hZmod hZcont B 1 zero_le_one 0)
    (field_one_zero_unbounded PW W hW hd hd3 hν2 Z hZmod)

end Sandpile.Support
