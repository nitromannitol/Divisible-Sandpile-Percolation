/-
The late-time bound of Step 1 of `lem:dgt4-linearization-from-survival`
(`eq:dgt4-late-derivative-variance`, `sandpile.tex:5755-5767`).

The paper splits the coordinate derivative of the tested odometer at the time
`n_R - \delta R^2` and bounds the late part pointwise by

  "`0 ≤ D^{>}_{R,z} ≤ ∑_{n_R-\delta R^2 < i < n_R}(P^i a_R)(z)`",

and then, "since the sum has at most `\delta R^2+2` terms, the Cauchy-Schwarz inequality,
the contraction bound `∑_z (P^i a_R)(z)^2 ≤ ∑_z a_R(z)^2`, and `eq:dgt4-tested-cell-l2`
give `∑_z (D^{>}_{R,z})^2 ≤ (\delta R^2+2)^2 ∑_z a_R(z)^2`."

That chain is exactly the inequality below, with the finite set of late times abstract:
Cauchy-Schwarz at each site, the exchange of the sum over sites with the finite sum over
times, and `Sandpile.tsum_sq_avg_iterate_le` applied to each time.  The factor
`(\delta R^2+2)^2` is the square of the number of late times.
-/
import Sandpile.Support.LinContract

namespace Sandpile

variable {d : ℕ}

/-- **The late-time `ℓ²` bound**, `eq:dgt4-late-derivative-variance`: the sum over sites of
the square of a sum of `s.card` iterated averages of `a` is at most `s.card²` times the sum
of the squares of `a`. -/
theorem tsum_sq_sum_iterate_avg_le (hd : 1 ≤ d) {a : Site d → ℝ}
    (ha : Summable fun z => (a z) ^ 2) (s : Finset ℕ) :
    ∑' z : Site d, (∑ i ∈ s, (avg^[i] a) z) ^ 2
      ≤ (s.card : ℝ) ^ 2 * ∑' z : Site d, (a z) ^ 2 := by
  have hsum : ∀ m : ℕ, Summable fun z : Site d => ((avg^[m] a) z) ^ 2 := by
    intro m
    induction m with
    | zero => simpa using ha
    | succ m ihm =>
        rw [Function.iterate_succ_apply']
        exact summable_sq_avg hd ihm
  have hmajsum : Summable fun z : Site d => (s.card : ℝ) * ∑ i ∈ s, ((avg^[i] a) z) ^ 2 :=
    (summable_sum fun i _ => hsum i).mul_left _
  have hpt : ∀ z : Site d, (∑ i ∈ s, (avg^[i] a) z) ^ 2
      ≤ (s.card : ℝ) * ∑ i ∈ s, ((avg^[i] a) z) ^ 2 := fun _ => sq_sum_le_card_mul_sum_sq
  have hlhs : Summable fun z : Site d => (∑ i ∈ s, (avg^[i] a) z) ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpt hmajsum
  have hswap : ∑' z : Site d, ((s.card : ℝ) * ∑ i ∈ s, ((avg^[i] a) z) ^ 2)
      = (s.card : ℝ) * ∑ i ∈ s, ∑' z : Site d, ((avg^[i] a) z) ^ 2 := by
    rw [tsum_mul_left, Summable.tsum_finsetSum fun i _ => hsum i]
  have hbound : ∑ i ∈ s, ∑' z : Site d, ((avg^[i] a) z) ^ 2
      ≤ (s.card : ℝ) * ∑' z : Site d, (a z) ^ 2 := by
    calc ∑ i ∈ s, ∑' z : Site d, ((avg^[i] a) z) ^ 2
        ≤ ∑ _i ∈ s, ∑' z : Site d, (a z) ^ 2 :=
          Finset.sum_le_sum fun i _ => tsum_sq_avg_iterate_le hd ha i
      _ = (s.card : ℝ) * ∑' z : Site d, (a z) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc ∑' z : Site d, (∑ i ∈ s, (avg^[i] a) z) ^ 2
      ≤ ∑' z : Site d, ((s.card : ℝ) * ∑ i ∈ s, ((avg^[i] a) z) ^ 2) :=
        Summable.tsum_le_tsum hpt hlhs hmajsum
    _ = (s.card : ℝ) * ∑ i ∈ s, ∑' z : Site d, ((avg^[i] a) z) ^ 2 := hswap
    _ ≤ (s.card : ℝ) * ((s.card : ℝ) * ∑' z : Site d, (a z) ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ = (s.card : ℝ) ^ 2 * ∑' z : Site d, (a z) ^ 2 := by ring

end Sandpile
