import Sandpile.Support.LinJacobianTimes
import Sandpile.Support.LinLateVar
import Sandpile.Support.TightSmallPower

/-!
# The late-time bound on the coordinate derivative of the tested field

Dropping the survival factor `S_{n,i} ≤ 1` turns the time-restricted coordinate derivative
`∑ x ∈ s, a x * jacobianTimes ζ n t x z` into a sum of heat kernels `∑ i ∈ t, (P^i a) z`, using
that the weighted sum of heat kernels over a finite set of sites carrying a weight `a` equals the
iterated average `avg^[i] a`, by symmetry of the kernel. Combined with a Cauchy-Schwarz bound on
the sum of squares of iterated averages, this gives the pointwise and `L²` late-time estimates on
the time-restricted derivative: the sum over sites of its square is at most `t.card ^ 2` times
`∑_z a(z) ^ 2`.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The weighted sum of heat kernels over the sites carrying a weight is the
iterated average, by symmetry of the kernel. -/
theorem sum_mul_heatKernel_eq_avg_iterate (s : Finset (Site d)) (a : Site d → ℝ)
    (hsupp : ∀ x ∉ s, a x = 0) (j : ℕ) (z : Site d) :
    ∑ x ∈ s, a x * heatKernel d j x z = (avg^[j] a) z := by
  classical
  rw [avg_iterate j a z, tsum_eq_sum (s := s) fun y hy => by rw [hsupp y hy, mul_zero]]
  exact (Finset.sum_congr rfl fun y _ => by
    rw [heatKernel_symm j z y, mul_comm]).symm

/-- The pointwise late bound of `sandpile.tex:5757-5760`:
`0 ≤ D^{>}_{R,z} ≤ ∑_{i late}(P^i a_R)(z)`. -/
theorem sum_a_jacobianTimes_le [NeZero d] (hd : 1 ≤ d) (s : Finset (Site d)) (a : Site d → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hsupp : ∀ x ∉ s, a x = 0) (ζ : Site d → ℝ) (n : ℕ) (t : Finset ℕ)
    (z : Site d) :
    ∑ x ∈ s, a x * jacobianTimes ζ n t x z ≤ ∑ j ∈ t, (avg^[j] a) z := by
  classical
  calc ∑ x ∈ s, a x * jacobianTimes ζ n t x z
      ≤ ∑ x ∈ s, a x * ∑ j ∈ t, heatKernel d j x z :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (jacobianTimes_le_sum_heatKernel hd ζ n t x z) (ha x)
    _ = ∑ x ∈ s, ∑ j ∈ t, a x * heatKernel d j x z :=
        Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _
    _ = ∑ j ∈ t, ∑ x ∈ s, a x * heatKernel d j x z := Finset.sum_comm
    _ = ∑ j ∈ t, (avg^[j] a) z :=
        Finset.sum_congr rfl fun j _ => sum_mul_heatKernel_eq_avg_iterate s a hsupp j z

/-- The time-restricted coordinate derivative `∑ x ∈ s, a x * jacobianTimes ζ n t x z` is
nonnegative when the weight `a` is. -/
theorem sum_a_jacobianTimes_nonneg (s : Finset (Site d)) (a : Site d → ℝ)
    (ha : ∀ x, 0 ≤ a x) (ζ : Site d → ℝ) (n : ℕ) (t : Finset ℕ) (z : Site d) :
    0 ≤ ∑ x ∈ s, a x * jacobianTimes ζ n t x z :=
  Finset.sum_nonneg fun x _ => mul_nonneg (ha x) (jacobianTimes_nonneg ζ n t x z)

/-- The summability of the squares of the summed iterated averages. -/
theorem summable_sq_sum_iterate_avg (hd : 1 ≤ d) {a : Site d → ℝ}
    (ha : Summable fun z => (a z) ^ 2) (t : Finset ℕ) :
    Summable fun z : Site d => (∑ i ∈ t, (avg^[i] a) z) ^ 2 := by
  classical
  have hsum : ∀ m : ℕ, Summable fun z : Site d => ((avg^[m] a) z) ^ 2 := by
    intro m
    induction m with
    | zero => simpa using ha
    | succ m ihm =>
        rw [Function.iterate_succ_apply']
        exact summable_sq_avg hd ihm
  have hmajsum : Summable fun z : Site d => (t.card : ℝ) * ∑ i ∈ t, ((avg^[i] a) z) ^ 2 :=
    (summable_sum fun i _ => hsum i).mul_left _
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun _ => sq_sum_le_card_mul_sum_sq)
    hmajsum

/-- **`eq:dgt4-late-derivative-variance`** (`sandpile.tex:5750-5762`) at the
time-restricted coordinate derivative: the sum over sites of its square is at
most the square of the number of late times times `∑_z a_R(z)²`. -/
theorem tsum_sq_sum_a_jacobianTimes_le [NeZero d] (hd : 1 ≤ d) (s : Finset (Site d))
    (a : Site d → ℝ) (ha : ∀ x, 0 ≤ a x) (hsupp : ∀ x ∉ s, a x = 0)
    (hsq : Summable fun z : Site d => (a z) ^ 2) (ζ : Site d → ℝ) (n : ℕ) (t : Finset ℕ) :
    ∑' z : Site d, (∑ x ∈ s, a x * jacobianTimes ζ n t x z) ^ 2
      ≤ (t.card : ℝ) ^ 2 * ∑' z : Site d, (a z) ^ 2 := by
  classical
  have hle : ∀ z : Site d, (∑ x ∈ s, a x * jacobianTimes ζ n t x z) ^ 2
      ≤ (∑ i ∈ t, (avg^[i] a) z) ^ 2 := fun z =>
    pow_le_pow_left₀ (sum_a_jacobianTimes_nonneg s a ha ζ n t z)
      (sum_a_jacobianTimes_le hd s a ha hsupp ζ n t z) 2
  have hmaj : Summable fun z : Site d => (∑ i ∈ t, (avg^[i] a) z) ^ 2 :=
    summable_sq_sum_iterate_avg hd hsq t
  have hlhs : Summable fun z : Site d => (∑ x ∈ s, a x * jacobianTimes ζ n t x z) ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle hmaj
  exact (Summable.tsum_le_tsum hle hlhs hmaj).trans (tsum_sq_sum_iterate_avg_le hd hsq t)

end Sandpile
