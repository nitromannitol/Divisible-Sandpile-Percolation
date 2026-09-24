/-
The semigroup identity for the Green function: the `j`-step heat kernel convolved with the
Green function is the tail of the heat kernel from step `j` on,
`\sum_z p_j(0,z)G(z,z')=\sum_{r\geq j}p_r(0,z')`.  It is the identification of the `j`-step
average of the Green function with the tail kernel of `eq:dgt4-tail-kernel`
(`sandpile.tex:1303-1306`).
-/
import Sandpile.Support.Iterate
import Sandpile.Support.ExitGreen

open MeasureTheory Filter Topology Set

set_option maxHeartbeats 800000

namespace Sandpile

variable {d : ℕ}

/-- **The heat kernel convolved with the Green function is the heat-kernel tail**:
`\sum_z p_j(0,z)G(z,z')=\sum_{r\geq j}p_r(0,z')`. -/
theorem tsum_heatKernel_mul_green (hd : 3 ≤ d) (j : ℕ) (z' : Site d) :
    ∑' z : Site d, heatKernel d j 0 z * green d z z'
      = ∑' r : ℕ, heatKernel d (j + r) 0 z' := by
  have hinner : ∀ r : ℕ, (∑' z : Site d, heatKernel d j 0 z * heatKernel d r z z')
      = heatKernel d (j + r) 0 z' :=
    fun r => tsum_heatKernel_mul_heatKernel j r 0 z'
  have hsumz : ∀ r : ℕ, Summable (fun z : Site d => heatKernel d j 0 z * heatKernel d r z z') :=
    fun r => summable_heatKernel_mul j 0 (fun z => heatKernel d r z z')
  have hsum : Summable (fun p : ℕ × Site d => heatKernel d j 0 p.2 * heatKernel d p.1 p.2 z') := by
    rw [summable_prod_of_nonneg (fun p => mul_nonneg (heatKernel_nonneg _ _ _) (heatKernel_nonneg _ _ _))]
    refine ⟨hsumz, ?_⟩
    have : (fun r : ℕ => ∑' z : Site d, heatKernel d j 0 z * heatKernel d r z z')
        = fun r => heatKernel d (j + r) 0 z' := funext hinner
    rw [this]
    exact (summable_heatKernel_transient hd (0 : Site d) z').comp_injective
      (fun a b hab => Nat.add_left_cancel hab)
  have hstep : ∀ z : Site d, heatKernel d j 0 z * green d z z'
      = ∑' r : ℕ, heatKernel d j 0 z * heatKernel d r z z' :=
    fun z => (Summable.tsum_mul_left _ (summable_heatKernel_transient hd z z')).symm
  simp_rw [hstep]
  rw [Summable.tsum_comm hsum]
  exact tsum_congr hinner

end Sandpile
