import Sandpile.Support.D4DefectParity
import Sandpile.Support.D4PotentialKernel

/-!
# Square summability of the four-dimensional potential kernel

The squared `ℓ²` bound for the tail of the paired heat kernel at time one,
together with the finite support of the time-zero term, shows that each
potential-kernel slice belongs to `ℓ²`.
-/

open scoped ENNReal

namespace Sandpile

/-- In dimension four, a potential-kernel slice is square-summable. -/
theorem memℓp_potentialKernel_four (hHK : Sandpile.External.HeatKernelBounds)
    (x : Site 4) : Memℓp (fun y => potentialKernel 4 x y) 2 := by
  obtain ⟨C, -, hbound⟩ := exists_heatKernel_tail_l2_four_all hHK
  let tail : Site 4 → ℝ := fun y =>
    ∑' j : ℕ, (heatKernel 4 (1 + j) x y - heatKernel 4 (1 + j) 0 y)
  have hfinite : (∑' y, ENNReal.ofReal (tail y ^ 2)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact hbound 1 (by norm_num) x
  have htail : Summable (fun y => tail y ^ 2) := by
    have h := ENNReal.summable_toNNReal_of_tsum_ne_top hfinite
    have hr := NNReal.summable_coe.mpr h
    simpa only [Function.comp_def, ENNReal.coe_toNNReal_eq_toReal,
      ENNReal.toReal_ofReal (sq_nonneg _)] using hr
  have htail' : Memℓp tail 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs] using htail
  have hzero : Memℓp (fun y => heatKernel 4 0 x y - heatKernel 4 0 0 y) 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs] using
      (summable_heatKernel_sub_sq 0 0 x (0 : Site 4))
  have heq : (fun y => potentialKernel 4 x y) =
      (fun y => heatKernel 4 0 x y - heatKernel 4 0 0 y) + tail := by
    funext y
    have hs := (summable_potentialKernel (by norm_num) x y).tsum_eq_zero_add
    change (∑' j : ℕ, (heatKernel 4 j x y - heatKernel 4 j 0 y)) = _
    simpa only [Pi.add_apply, tail, Nat.add_comm] using hs
  rw [heq]
  exact hzero.add htail'

end Sandpile
