/-
The junction between Step 1 and Step 2 of `lem:dgt4-linearization-from-survival`.

Step 1 (`Support/LinJacobianEarlyDisplay.lean`) proves that the sum over ALL
sites of the variances of the coordinate derivative, taken under the law of the
mass configuration, tends to zero.  Step 2
(`Support/LinTestedStep2.lean`) consumes the sum over the FINITE set of sites the
tested field reads, taken under the i.i.d. law of the field itself.  The scenery
map carries one to the other, and the finite sum is below the full sum because
every variance is nonnegative.
-/
import Sandpile.Support.LinJacobianEarlyDisplay
import Sandpile.Support.SceneryBridge
import Sandpile.Support.LinJacobianShift

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The variance of a functional of the field is the variance of the same
functional of the scenery. -/
theorem variance_field_eq_scenery (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    (G : (Site d → ℝ) → ℝ) (hG : Measurable G) :
    variance G (LatticeProb.iidLaw d ν)
      = variance (fun σ => G (scenery d σ)) (Sandpile.centeredMassLaw d ν) := by
  have hmap := map_scenery_centeredMassLaw d ν hd
  rw [← hmap, variance_map (by rw [hmap]; exact hG.aemeasurable)
    (measurable_scenery d).aemeasurable]
  rfl

/-- The summability over all sites of the variances of the coordinate derivative
of the tested field. -/
theorem summable_variance_odometerJacobian (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (n : ℕ) (s : Finset (Site d)) (a : Site d → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hsupp : ∀ x ∉ s, a x = 0) (hsq : Summable fun z : Site d => (a z) ^ 2) :
    Summable fun z : Site d => variance
      (fun σ => ∑ x ∈ s, a x * odometerJacobian (scenery d σ) n x z)
      (Sandpile.centeredMassLaw d ν) := by
  have hcongr : ∀ z : Site d,
      (fun σ : Site d → ℝ => ∑ x ∈ s, a x * odometerJacobian (scenery d σ) n x z)
        = fun σ : Site d → ℝ =>
            ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n (Finset.range n) x z := by
    intro z
    funext σ
    exact Finset.sum_congr rfl fun x _ => by rw [jacobianTimes_range hd]
  have h := summable_variance_sum_jacobianTimes (Sandpile.centeredMassLaw d ν) hd n s a ha
    hsupp hsq (Finset.range n)
  exact h.congr fun z => by rw [hcongr z]

/-- **The hypothesis `hVar` of Step 2 from the conclusion of Step 1.**  The
finite site sum under the i.i.d. law of the field is below the full site sum
under the law of the mass configuration, so it tends to zero with it. -/
theorem tendsto_finset_sum_variance_odometerJacobian {l : Filter ℝ} (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hd : 1 ≤ d) (n : ℝ → ℕ) (s : ℝ → Finset (Site d))
    (a : ℝ → Site d → ℝ) (ha : ∀ (R : ℝ) (x : Site d), 0 ≤ a R x)
    (hsupp : ∀ R : ℝ, ∀ x ∉ s R, a R x = 0)
    (hsq : ∀ R : ℝ, Summable fun z : Site d => (a R z) ^ 2)
    (V : ℝ → Finset (Site d))
    (htend : Tendsto (fun R : ℝ => ∑' z : Site d, variance
        (fun σ => ∑ x ∈ s R, a R x * odometerJacobian (scenery d σ) (n R) x z)
        (Sandpile.centeredMassLaw d ν)) l (𝓝 0)) :
    Tendsto (fun R : ℝ => ∑ v ∈ V R, variance
        (fun ζ => ∑ x ∈ s R, a R x * odometerJacobian ζ (n R) x v)
        (LatticeProb.iidLaw d ν)) l (𝓝 0) := by
  refine squeeze_zero (fun R => Finset.sum_nonneg fun v _ => variance_nonneg _ _)
    (fun R => ?_) htend
  have hmeas : ∀ v : Site d, Measurable
      fun ζ : Site d → ℝ => ∑ x ∈ s R, a R x * odometerJacobian ζ (n R) x v := fun v =>
    Finset.measurable_sum _ fun x _ => (measurable_odometerJacobian (n R) x v).const_mul (a R x)
  have hrw : ∀ v : Site d,
      variance (fun ζ => ∑ x ∈ s R, a R x * odometerJacobian ζ (n R) x v)
          (LatticeProb.iidLaw d ν)
        = variance (fun σ => ∑ x ∈ s R, a R x * odometerJacobian (scenery d σ) (n R) x v)
            (Sandpile.centeredMassLaw d ν) := fun v =>
    variance_field_eq_scenery ν hd _ (hmeas v)
  rw [Finset.sum_congr rfl fun v _ => hrw v]
  exact Summable.sum_le_tsum _ (fun z _ => variance_nonneg _ _)
    (summable_variance_odometerJacobian ν hd (n R) (s R) (a R) (ha R) (hsupp R) (hsq R))

end Sandpile
