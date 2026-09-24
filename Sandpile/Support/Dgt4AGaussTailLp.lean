/-
The heat-kernel tail `\sum_{r\geq j}p_r(0,z)` of `eq:dgt4-tail-kernel` as a square-summable
family of coefficients, and the identity that identifies it with the `j`-step average of the
Green coefficient families: `P^jG(\cdot,z)(0)=\sum_{r\geq j}p_r(0,z)`
(`sandpile.tex:5063-5065`).
-/
import Sandpile.Support.Dgt4ATailKernelEq
import Sandpile.Support.Dgt4ATailKernelSq
import Sandpile.Support.LinGaussField
import Sandpile.Support.BlockIncrement

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The heat-kernel tail at the origin, as a square-summable family of coefficients. -/
noncomputable def tailKernelLp (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    {j : ℕ} (hj : 1 ≤ j) : lp (fun _ : Site d => ℝ) 2 :=
  ⟨fun z => Sandpile.External.tailKernel d j z, by
    refine (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).2 ?_
    refine (summable_tailKernel_sq hGH hd hj).congr fun z => ?_
    rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, sq_abs]⟩

theorem coeFn_tailKernelLp (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    {j : ℕ} (hj : 1 ≤ j) :
    ((tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2) : Site d → ℝ)
      = fun z => Sandpile.External.tailKernel d j z := rfl

/-- `P^jG(\cdot,z)(0)=\sum_{r\geq j}p_r(0,z)` (`sandpile.tex:5058-5060`), as a finite sum. -/
theorem sum_heatKernel_mul_green_eq_tailKernel (hd : 3 ≤ d) (j : ℕ) (z : Site d) :
    ∑ x ∈ boxFinset (0 : Site d) j, heatKernel d j 0 x * green d x z
      = Sandpile.External.tailKernel d j z := by
  rw [← avg_iterate_eq_finsetSum (fun y => green d y z) j 0,
    avg_iterate_green_eq_tailKernel hd j z, tsum_heatKernel_add_eq_tailKernel]

/-- **The `j`-step average of the Green coefficient families is the tail kernel.** -/
theorem sum_smul_greenLp_eq_tailKernelLp (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    {j : ℕ} (hj : 1 ≤ j) :
    ∑ x ∈ boxFinset (0 : Site d) j, heatKernel d j 0 x • greenLp d hd x
      = tailKernelLp hGH hd hj := by
  refine lp.ext (funext fun z => ?_)
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, lp.coeFn_smul, smul_eq_mul, coeFn_greenLp,
    coeFn_tailKernelLp]
  exact sum_heatKernel_mul_green_eq_tailKernel (by omega) j z

/-- The squared norm of the tail-kernel family is `\sum_z(\sum_{r\geq j}p_r(0,z))^2`. -/
theorem norm_tailKernelLp_sq (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    {j : ℕ} (hj : 1 ≤ j) :
    ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ ^ 2
      = ∑' z : Site d, Sandpile.External.tailKernel d j z ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  refine tsum_congr fun z => ?_
  simp only [coeFn_tailKernelLp, RCLike.inner_apply, conj_trivial]
  ring

end Sandpile
