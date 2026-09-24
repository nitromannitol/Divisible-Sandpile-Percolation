/-
Stationarity of the mean gradient of `lem:dgt4-linearization-from-survival`
(`sandpile.tex:5823-5827`):

  "By stationarity, `E[∂_{ζ(z)}F_R] = ∑_x a_R(x) c_R(z-x)`,"

with `c_R(w) = E[∂_{ζ(w)}u_{n_R}(0)]`.  The Jacobian of `eq:odometer-derivative`
commutes with translation of the scenery, and the i.i.d. law is invariant under
translation, so the mean gradient at a site is the mean gradient at the origin
of the displaced site, and the mean gradient of the tested field is the
convolution of the weights with `c_R`.
-/
import Sandpile.Support.LinTestedJacobian
import Sandpile.Support.Stationary

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The odometer Jacobian is a measurable function of the scenery. -/
theorem measurable_odometerJacobian (n : ℕ) (x z : Site d) :
    Measurable fun ζ : Site d → ℝ => odometerJacobian ζ n x z := by
  induction n generalizing x with
  | zero => simp [odometerJacobian]
  | succ m ih =>
      have havg : Measurable fun ζ : Site d → ℝ =>
          avg (fun y => odometerJacobian ζ m y z) x := by
        show Measurable fun ζ : Site d → ℝ =>
          (∑ i : Fin d, (odometerJacobian ζ m (x + unit i) z
            + odometerJacobian ζ m (x - unit i) z)) / (2 * (d : ℝ))
        exact (Finset.measurable_sum _ fun i _ => (ih _).add (ih _)).div_const _
      have hset : MeasurableSet {ζ : Site d → ℝ | 0 < odometerOf ζ (m + 1) x} :=
        measurableSet_lt measurable_const (measurable_odometerOf (m + 1) x)
      exact Measurable.ite hset (measurable_const.add havg) measurable_const

/-- The Jacobian commutes with translation of the scenery. -/
theorem odometerJacobian_shiftField (ζ : Site d → ℝ) (y : Site d) :
    ∀ (n : ℕ) (z w : Site d),
      odometerJacobian (shiftField y ζ) n z w = odometerJacobian ζ n (z + y) (w + y) := by
  intro n
  induction n with
  | zero => intro z w; rfl
  | succ m ih =>
      intro z w
      have hact : odometerOf (shiftField y ζ) (m + 1) z = odometerOf ζ (m + 1) (z + y) :=
        odometerOf_shiftField ζ y (m + 1) z
      have hnb : avg (fun u => odometerJacobian (shiftField y ζ) m u w) z
          = avg (fun u => odometerJacobian ζ m u (w + y)) (z + y) := by
        show (∑ i : Fin d, (odometerJacobian (shiftField y ζ) m (z + unit i) w
              + odometerJacobian (shiftField y ζ) m (z - unit i) w)) / (2 * (d : ℝ))
          = (∑ i : Fin d, (odometerJacobian ζ m (z + y + unit i) (w + y)
              + odometerJacobian ζ m (z + y - unit i) (w + y))) / (2 * (d : ℝ))
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have e1 : z + unit i + y = z + y + unit i := by abel
        have e2 : z - unit i + y = z + y - unit i := by abel
        rw [ih (z + unit i) w, ih (z - unit i) w, e1, e2]
      have heq : (z = w) ↔ (z + y = w + y) := by
        constructor
        · intro h; rw [h]
        · intro h; exact add_right_cancel h
      show (if 0 < odometerOf (shiftField y ζ) (m + 1) z then
          (if z = w then (1 : ℝ) else 0)
            + avg (fun u => odometerJacobian (shiftField y ζ) m u w) z else 0)
        = if 0 < odometerOf ζ (m + 1) (z + y) then
            (if z + y = w + y then (1 : ℝ) else 0)
              + avg (fun u => odometerJacobian ζ m u (w + y)) (z + y) else 0
      rw [hact, hnb]
      by_cases h : z = w
      · rw [if_pos h, if_pos (heq.1 h)]
      · rw [if_neg h, if_neg (fun hc => h (heq.2 hc))]

/-- **Stationarity of the mean gradient** (`sandpile.tex:5818-5822`):
`E[∂_{ζ(z)}u_n(x)] = c_n(z - x)` with `c_n(w) = E[∂_{ζ(w)}u_n(0)]`. -/
theorem integral_odometerJacobian_shift (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (x v : Site d) :
    ∫ ζ, odometerJacobian ζ n x v ∂(LatticeProb.iidLaw d ν)
      = ∫ ζ, odometerJacobian ζ n 0 (v - x) ∂(LatticeProb.iidLaw d ν) := by
  have hmeas : AEStronglyMeasurable
      (fun ζ : Site d → ℝ => odometerJacobian ζ n 0 (v - x))
      ((massLaw d ν).map (shiftField x)) := by
    rw [massLaw_map_shiftField]
    exact (measurable_odometerJacobian n 0 (v - x)).aestronglyMeasurable
  have h1 : ∫ ζ, odometerJacobian (shiftField x ζ) n 0 (v - x) ∂(massLaw d ν)
      = ∫ ζ, odometerJacobian ζ n 0 (v - x) ∂(massLaw d ν) := by
    rw [← integral_map (measurable_shiftField x).aemeasurable hmeas, massLaw_map_shiftField]
  rw [show LatticeProb.iidLaw d ν = massLaw d ν from rfl, ← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  show odometerJacobian ζ n x v = odometerJacobian (shiftField x ζ) n 0 (v - x)
  rw [odometerJacobian_shiftField ζ x n 0 (v - x), zero_add, sub_add_cancel]

/-- The mean gradient of the tested field is the convolution
`∑_x a_R(x) c_{n}(z - x)` of `sandpile.tex:5818-5822`. -/
theorem integral_meanGradient_testedField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ) (v : Site d)
    (hint : ∀ x : Site d, Integrable (fun ζ => odometerJacobian ζ n x v)
      (LatticeProb.iidLaw d ν)) :
    ∫ ζ, (∑ x ∈ s, a x * odometerJacobian ζ n x v) ∂(LatticeProb.iidLaw d ν)
      = ∑ x ∈ s, a x * ∫ ζ, odometerJacobian ζ n 0 (v - x) ∂(LatticeProb.iidLaw d ν) := by
  rw [integral_finsetSum s fun x _ => (hint x).const_mul (a x)]
  exact Finset.sum_congr rfl fun x _ => by
    rw [integral_const_mul, integral_odometerJacobian_shift ν n x v]

end Sandpile
