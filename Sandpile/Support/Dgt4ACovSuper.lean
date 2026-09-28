import Sandpile.Support.Dgt4ACondition
import Sandpile.Support.ExitGreen

/-!
# The Green covariance is superharmonic

In the normalisation where the one-site variance is one, the covariance of the Gaussian
Green field is `C(x) = ∑_z G(x, z) * G(0, z)`, and applying the neighbour-averaging operator
`avg` gives `C(x) - avg C (x) = G(0, x) ≥ 0`, so `C` is superharmonic. The proof rewrites the
neighbour average of the defining sum using the Green equation `avg_green`,
`(I - P) G(·, y)(x) = 1_{x = y}`, exchanging the finite average over `2d` neighbours with the
sum over `z`, which is justified by the square summability of `G(w, ·)` and `G(0, ·)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The Green covariance is an absolutely convergent sum. -/
theorem summable_green_mul (hd : 5 ≤ d) (x y : Site d) :
    Summable fun z : Site d => green d x z * green d y z := by
  have hmaj : Summable fun z : Site d => (green d x z ^ 2 + green d y z ^ 2) / 2 :=
    ((summable_green_sq hd x).add (summable_green_sq hd y)).div_const 2
  refine Summable.of_nonneg_of_le (fun z => mul_nonneg (green_nonneg _ _) (green_nonneg _ _))
    (fun z => ?_) hmaj
  nlinarith [sq_nonneg (green d x z - green d y z)]

/-- The neighbour average commutes with the sum defining the Green covariance. -/
theorem avg_tsum_green_mul (hd : 5 ≤ d) (x : Site d) :
    Sandpile.avg (fun w => ∑' z : Site d, green d w z * green d 0 z) x
      = ∑' z : Site d, Sandpile.avg (fun w => green d w z) x * green d 0 z := by
  classical
  simp only [Sandpile.avg, LatticeProb.walkOp, LatticeProb.nbrSum]
  have hpt : ∀ z : Site d,
      (∑ i : Fin d, (green d (x + unit i) z + green d (x - unit i) z)) / (2 * (d : ℝ))
          * green d 0 z
        = (∑ i : Fin d, (green d (x + unit i) z * green d 0 z
            + green d (x - unit i) z * green d 0 z)) / (2 * (d : ℝ)) := by
    intro z
    rw [div_mul_eq_mul_div, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hpt]
  rw [tsum_div_const]
  congr 1
  rw [Summable.tsum_finsetSum (fun i _ => (summable_green_mul hd (x + unit i) 0).add
    (summable_green_mul hd (x - unit i) 0))]
  exact Finset.sum_congr rfl fun i _ =>
    ((summable_green_mul hd (x + unit i) 0).tsum_add
      (summable_green_mul hd (x - unit i) 0)).symm

/-- `(I-P)\Cov(V_\infty(\cdot),V_\infty(0))(x)=\Var(\zeta(0))G(0,x)\geq0`
(`sandpile.tex:5110-5112`), in the normalisation where the variance is one. -/
theorem greenCovariance_sub_avg (hd : 5 ≤ d) (x : Site d) :
    (∑' z : Site d, green d x z * green d 0 z)
        - Sandpile.avg (fun w => ∑' z : Site d, green d w z * green d 0 z) x
      = green d 0 x := by
  classical
  rw [avg_tsum_green_mul hd x]
  have hval : ∀ z : Site d, Sandpile.avg (fun w => green d w z) x * green d 0 z
      = green d x z * green d 0 z - (if x = z then (1 : ℝ) else 0) * green d 0 z := by
    intro z
    rw [avg_green (by omega) x z]
    ring
  have hind : Summable fun z : Site d => (if x = z then (1 : ℝ) else 0) * green d 0 z := by
    refine summable_of_ne_finset_zero (s := {x}) fun z hz => ?_
    have hxz : x ≠ z := fun h => hz (by simp [h])
    simp [hxz]
  simp only [hval]
  rw [Summable.tsum_sub (summable_green_mul hd x 0) hind]
  have hsingle : (∑' z : Site d, (if x = z then (1 : ℝ) else 0) * green d 0 z)
      = green d 0 x := by
    rw [tsum_eq_single x fun z hz => by
      have hxz : ¬ (x = z) := fun h => hz h.symm
      simp [hxz]]
    simp
  rw [hsingle]
  ring

/-- The Green covariance is superharmonic. -/
theorem avg_greenCovariance_le (hd : 5 ≤ d) (x : Site d) :
    Sandpile.avg (fun w => ∑' z : Site d, green d w z * green d 0 z) x
      ≤ ∑' z : Site d, green d x z * green d 0 z := by
  have h := greenCovariance_sub_avg hd x
  have hg : 0 ≤ green d 0 x := green_nonneg 0 x
  linarith

end Sandpile
