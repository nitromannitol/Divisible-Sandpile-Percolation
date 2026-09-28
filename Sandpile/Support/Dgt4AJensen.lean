import Sandpile.Support.Dgt4ADeviationField
import Sandpile.Support.BlockIncrement
import Sandpile.Support.D4Smoothed

/-!
# The conditional Jensen step of the telescoping

The conditional Jensen step of the telescoping (`sandpile.tex:5074-5077`): `P^i` is an average
against the `i`-step heat kernel, so the second moment of `P^iD_n(0)` is at most the average of
the second moments of `D_n` over the sites the kernel charges, and by stationarity every one of
those equals the second moment of `D_n(0)`.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- Jensen's inequality for a finite convex combination. -/
theorem sq_sum_weighted_le {ι : Type*} (s : Finset ι) (p f : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    (∑ i ∈ s, p i * f i) ^ 2 ≤ ∑ i ∈ s, p i * f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (p i))
    (fun i => Real.sqrt (p i) * f i)
  have e1 : (∑ i ∈ s, Real.sqrt (p i) * (Real.sqrt (p i) * f i)) = ∑ i ∈ s, p i * f i :=
    Finset.sum_congr rfl fun i hi => by
      rw [← mul_assoc]
      congr 1
      exact Real.mul_self_sqrt (hp i hi)
  have e2 : (∑ i ∈ s, Real.sqrt (p i) ^ 2) = 1 := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hp i hi)
  have e3 : (∑ i ∈ s, (Real.sqrt (p i) * f i) ^ 2) = ∑ i ∈ s, p i * f i ^ 2 :=
    Finset.sum_congr rfl fun i hi => by
      rw [mul_pow, Real.sq_sqrt (hp i hi)]
  rw [e1, e2, e3, one_mul] at h
  exact h

/-- The scenery translation is measure preserving. -/
theorem measurePreserving_shiftField (ν : Measure ℝ) [IsProbabilityMeasure ν] (y : Site d) :
    MeasurePreserving (shiftField (d := d) y) (LatticeProb.iidLaw d ν)
      (LatticeProb.iidLaw d ν) :=
  ⟨measurable_shiftField y, massLaw_map_shiftField d ν y⟩

/-- Every site carries the same square integrability of the field. -/
theorem integrable_sceneryDeviationField_sq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (y : Site d)
    (hint : Integrable (fun ζ : Site d → ℝ => sceneryDeviation d ζ n ^ 2)
      (LatticeProb.iidLaw d ν)) :
    Integrable (fun ζ : Site d → ℝ => sceneryDeviationField d ζ n y ^ 2)
      (LatticeProb.iidLaw d ν) := by
  have h := LatticeProb.integrable_comp_mp (measurePreserving_shiftField (d := d) ν y)
    (fun ζ => sceneryDeviation d ζ n ^ 2)
    (((measurable_sceneryDeviation n).pow_const 2).aestronglyMeasurable) hint
  refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [sceneryDeviationField_shift]

/-- `sceneryDeviationField d · n z` is measurable in the scenery, being built from the
coordinate projection, `odometerOf` and the average of `odometerOf`, each measurable. -/
theorem measurable_sceneryDeviationField (n : ℕ) (z : Site d) :
    Measurable fun ζ : Site d → ℝ => sceneryDeviationField d ζ n z :=
  (measurable_pi_apply z).sub ((measurable_odometerOf n z).sub
    (by simpa using Sandpile.measurable_avg_iterate_odometerOf (d := d) 1 n z))

/-- The `i`-step average of the deviation field at the origin is measurable in the scenery, as
a finite sum over the box weighted by the heat kernel of the measurable functions
`sceneryDeviationField`. -/
theorem measurable_avgIterate_sceneryDeviationField (n i : ℕ) :
    Measurable fun ζ : Site d → ℝ =>
      (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0 := by
  have he : (fun ζ : Site d → ℝ => (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0)
      = fun ζ => ∑ z ∈ boxFinset (0 : Site d) i,
          heatKernel d i 0 z * sceneryDeviationField d ζ n z :=
    funext fun ζ => avg_iterate_eq_finsetSum _ _ _
  rw [he]
  exact Finset.measurable_sum _ fun z _ =>
    Measurable.const_mul (measurable_sceneryDeviationField n z) _

/-- The squared `i`-step average of the deviation field is integrable, by Jensen's inequality
`sq_sum_weighted_le` dominating it pointwise by the integrable heat-kernel-weighted sum of the
squared coordinate deviations. -/
theorem integrable_avgIterate_sceneryDeviationField_sq (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n i : ℕ)
    (hint : Integrable (fun ζ : Site d → ℝ => sceneryDeviation d ζ n ^ 2)
      (LatticeProb.iidLaw d ν)) :
    Integrable (fun ζ : Site d → ℝ =>
      (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0 ^ 2)
      (LatticeProb.iidLaw d ν) := by
  have hone : ∑ z ∈ boxFinset (0 : Site d) i, heatKernel d i 0 z = 1 :=
    sum_heatKernel_boxFinset hd i 0
  have hIsum : Integrable (fun ζ : Site d → ℝ => ∑ z ∈ boxFinset (0 : Site d) i,
      heatKernel d i 0 z * sceneryDeviationField d ζ n z ^ 2)
      (LatticeProb.iidLaw d ν) :=
    integrable_finsetSum _ fun z _ =>
      (integrable_sceneryDeviationField_sq ν n z hint).const_mul _
  refine Integrable.mono' hIsum
    ((measurable_avgIterate_sceneryDeviationField n i).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ζ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), avg_iterate_eq_finsetSum]
  exact sq_sum_weighted_le _ _ _ (fun z _ => heatKernel_nonneg _ _ _) hone

/-- `\E[(P^iD_n(0))^2]\leq\E[D_n^2]` (`sandpile.tex:5069-5072`). -/
theorem integral_avgIterate_sceneryDeviationField_sq_le (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n i : ℕ)
    (hint : Integrable (fun ζ : Site d → ℝ => sceneryDeviation d ζ n ^ 2)
      (LatticeProb.iidLaw d ν)) :
    (∫ ζ, (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0 ^ 2
        ∂(LatticeProb.iidLaw d ν))
      ≤ ∫ ζ, sceneryDeviation d ζ n ^ 2 ∂(LatticeProb.iidLaw d ν) := by
  have hone : ∑ z ∈ boxFinset (0 : Site d) i, heatKernel d i 0 z = 1 :=
    sum_heatKernel_boxFinset hd i 0
  have hptJ : ∀ ζ : Site d → ℝ,
      (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0 ^ 2
        ≤ ∑ z ∈ boxFinset (0 : Site d) i,
            heatKernel d i 0 z * sceneryDeviationField d ζ n z ^ 2 := by
    intro ζ
    rw [avg_iterate_eq_finsetSum]
    exact sq_sum_weighted_le _ _ _ (fun z _ => heatKernel_nonneg _ _ _) hone
  have hIsum : Integrable (fun ζ : Site d → ℝ => ∑ z ∈ boxFinset (0 : Site d) i,
      heatKernel d i 0 z * sceneryDeviationField d ζ n z ^ 2)
      (LatticeProb.iidLaw d ν) :=
    integrable_finsetSum _ fun z _ =>
      (integrable_sceneryDeviationField_sq ν n z hint).const_mul _
  have hIlhs : Integrable (fun ζ : Site d → ℝ =>
      (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0 ^ 2)
      (LatticeProb.iidLaw d ν) :=
    integrable_avgIterate_sceneryDeviationField_sq hd ν n i hint
  refine le_trans (integral_mono hIlhs hIsum hptJ) (le_of_eq ?_)
  rw [integral_finsetSum _ fun z _ =>
    (integrable_sceneryDeviationField_sq ν n z hint).const_mul _]
  have hz : ∀ z ∈ boxFinset (0 : Site d) i,
      (∫ ζ, heatKernel d i 0 z * sceneryDeviationField d ζ n z ^ 2
          ∂(LatticeProb.iidLaw d ν))
        = heatKernel d i 0 z * ∫ ζ, sceneryDeviation d ζ n ^ 2 ∂(LatticeProb.iidLaw d ν) := by
    intro z _
    rw [integral_const_mul, integral_sceneryDeviationField_sq ν n z]
  rw [Finset.sum_congr rfl hz, ← Finset.sum_mul, hone, one_mul]

end Sandpile
