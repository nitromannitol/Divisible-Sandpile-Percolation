/-
Two further properties of the walk kernels used by the tightness chain: a
transition probability is at most one, and the doubled Green kernel at two
different times is the double time sum of transition probabilities.
-/
import Sandpile.Support.TightSmallPower

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- A transition probability is at most one. -/
theorem heatKernel_le_one (hd : 1 ≤ d) : ∀ (k : ℕ) (x y : Site d),
    heatKernel d k x y ≤ 1 := by
  intro k x y
  have hsum : Summable (fun z : Site d => heatKernel d k x z) := by
    simpa using summable_heatKernel_mul k x (fun _ => (1 : ℝ))
  have h1 : heatKernel d k x y ≤ ∑' z : Site d, heatKernel d k x z :=
    hsum.le_tsum y (fun z _ => heatKernel_nonneg k x z)
  rw [tsum_heatKernel hd k x] at h1
  exact h1

/-- The doubled Green kernel at two times is the double time sum of transition
probabilities. -/
theorem tsum_greenTime_mul_greenTime' (n m : ℕ) (x y : Site d) :
    ∑' z : Site d, greenTime d n x z * greenTime d m y z
      = ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range m, heatKernel d (a + b) x y := by
  have h1 : ∀ z : Site d, greenTime d n x z * greenTime d m y z
      = ∑ a ∈ Finset.range n, heatKernel d a x z * greenTime d m z y := by
    intro z
    rw [greenTime_symm m y z]
    show (∑ a ∈ Finset.range n, heatKernel d a x z) * greenTime d m z y = _
    rw [Finset.sum_mul]
  rw [tsum_congr h1,
    Summable.tsum_finsetSum fun a (_ : a ∈ Finset.range n) => summable_heatKernel_mul a x _]
  exact Finset.sum_congr rfl fun a _ => tsum_heatKernel_mul_greenTime a m x y

end Sandpile
