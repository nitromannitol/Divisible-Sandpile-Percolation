import Sandpile.Support.LinTestedStep2
import Sandpile.Support.GreenHigh
import Sandpile.Support.LinGreenTail

/-!
# The tested Green weight is bounded by the tested Green function

The bound proved here is on the Green weights `∑_x a_R(x)G(x,z)`; the coefficient of the
convex-linear bound is the time-`n_R` weight `∑_x a_R(x)g_{n_R}(x,z)`, which is below it site
by site because `g_t ≤ G` and the tested weights are nonnegative. Summing the squared pointwise
bound over a finite set and comparing to the full tail sum then transfers the uniform `ℓ²`
bound on the Green weights to the time-`n_R` weights.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The time-`t` Green kernel is below the Green function at every base point. -/
theorem greenTime_le_green_base (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (N : ℕ) (x v : Site d) : greenTime d N x v ≤ green d x v := by
  have h1 : greenTime d N x v = greenTime d N 0 (v - x) := by
    simpa using (greenTime_add_right N 0 (v - x) x)
  rw [h1, green_shift]
  exact greenTime_le_green hGH hd N (v - x)

/-- **`eq:dgt4-tested-green-bound` for the coefficient of the convex-linear
bound.**  The time-`n_R` weight is below the Green weight, so the uniform `ℓ²`
bound on the Green weights bounds the sum the convex-linear bound consumes. -/
theorem sum_testedGreenWeight_sq_le (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (s : Finset (Site d)) (a : Site d → ℝ) (ha : ∀ x, 0 ≤ a x) (N : ℕ)
    (t : Finset (Site d))
    (hsum : Summable fun z : Site d => (∑ x ∈ s, a x * green d x z) ^ 2) :
    ∑ v ∈ t, testedGreenWeight s a N v ^ 2
      ≤ ∑' z : Site d, (∑ x ∈ s, a x * green d x z) ^ 2 := by
  have h0 : ∀ v : Site d, 0 ≤ testedGreenWeight s a N v := fun v =>
    Finset.sum_nonneg fun x _ => mul_nonneg (ha x) (greenTime_nonneg N x v)
  have hle : ∀ v : Site d,
      testedGreenWeight s a N v ^ 2 ≤ (∑ x ∈ s, a x * green d x v) ^ 2 := by
    intro v
    refine pow_le_pow_left₀ (h0 v) ?_ 2
    exact Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (greenTime_le_green_base hGH hd N x v) (ha x)
  calc ∑ v ∈ t, testedGreenWeight s a N v ^ 2
      ≤ ∑ v ∈ t, (∑ x ∈ s, a x * green d x v) ^ 2 :=
        Finset.sum_le_sum fun v _ => hle v
    _ ≤ ∑' z : Site d, (∑ x ∈ s, a x * green d x z) ^ 2 :=
        Summable.sum_le_tsum t (fun z _ => sq_nonneg _) hsum

end Sandpile
