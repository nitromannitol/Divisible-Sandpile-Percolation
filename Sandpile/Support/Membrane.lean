import Sandpile.Support.Kernel

/-!
# The membrane field agrees with its Green-function form

The membrane field of `sandpile.tex`, `eq:membrane-recursion`, is defined elsewhere by its
recursion `V_{n+1} = ζ + P V_n`. The paper also writes it in Green form,
`eq:linear-green-field`, `V_n(x) = ∑_{k<n} ∑_y p_k(x,y) ζ(y) = ∑_y g_n(x,y) ζ(y)`, and that is
the form every estimate in the paper uses. The two agree; `membrane_eq_greenTime` proves it,
by induction using the one-step recursion for the finite-time Green kernel
(`greenTime_succ_avg`). The sums are honest `tsum`s rather than sums over a box: `g_n(x, ·)` is
supported in the box of radius `n` about `x`, so every series here is summable whatever the
scenery, by `summable_greenTime_mul`.
-/

namespace Sandpile

variable {d : ℕ}

/-- A finite sum of summable families is summable. -/
theorem summable_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Site d → ℝ}
    (h : ∀ i ∈ s, Summable (f i)) : Summable fun z => ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The one-step recursion for the finite-time Green kernel, read backwards from
the starting point rather than forwards from the endpoint. -/
theorem greenTime_succ_avg (m : ℕ) (y z : Site d) :
    greenTime d (m + 1) y z = heatKernel d 0 y z +
      (∑ i : Fin d, (greenTime d m (y + unit i) z + greenTime d m (y - unit i) z)) / (2 * d) := by
  show (∑ k ∈ Finset.range (m + 1), heatKernel d k y z) = heatKernel d 0 y z +
      (∑ i : Fin d, (greenTime d m (y + unit i) z + greenTime d m (y - unit i) z)) / (2 * d)
  rw [Finset.sum_range_succ' (fun k => heatKernel d k y z) m, add_comm]
  congr 1
  have hstep : ∀ k : ℕ, heatKernel d (k + 1) y z =
      (∑ i : Fin d, (heatKernel d k (y + unit i) z + heatKernel d k (y - unit i) z)) / (2 * d) :=
    fun _ => rfl
  simp_rw [hstep]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib

/-- `p_0(y, ·)` tested against a field is summable. -/
theorem summable_heatKernel_zero_mul (y : Site d) (ζ : Site d → ℝ) :
    Summable fun z : Site d => heatKernel d 0 y z * ζ z := by
  refine summable_of_ne_finset_zero (s := {y}) fun z hz => ?_
  have hzy : z ≠ y := by simpa using hz
  simp [heatKernel, LatticeProb.LocalCLT.heatKernel, Ne.symm hzy]

/-- `p_0(y, ·)` tested against a field returns the field's value at `y`. -/
theorem tsum_heatKernel_zero_mul (y : Site d) (ζ : Site d → ℝ) :
    ∑' z : Site d, heatKernel d 0 y z * ζ z = ζ y := by
  rw [tsum_eq_single y]
  · simp [heatKernel, LatticeProb.LocalCLT.heatKernel]
  · intro z hz
    simp [heatKernel, LatticeProb.LocalCLT.heatKernel, Ne.symm hz]

/-- The membrane field in Green form: `V_n(x) = ∑_y g_n(x,y) ζ(y)`
(`eq:linear-green-field`). -/
theorem membrane_eq_greenTime (ζ : Site d → ℝ) :
    ∀ (m : ℕ) (y : Site d), membrane ζ m y = ∑' z : Site d, greenTime d m y z * ζ z := by
  intro m
  induction m with
  | zero => intro y; simp [membrane, greenTime, LatticeProb.greenTime]
  | succ n ih =>
      intro y
      have hsum : ∀ w : Site d, Summable fun z : Site d => greenTime d n w z * ζ z :=
        fun w => summable_greenTime_mul n w ζ
      have key : ∀ z : Site d,
          greenTime d (n + 1) y z * ζ z = heatKernel d 0 y z * ζ z +
            (∑ i : Fin d, (greenTime d n (y + unit i) z * ζ z +
              greenTime d n (y - unit i) z * ζ z)) / (2 * d) := by
        intro z
        have hmul : (∑ i : Fin d,
              (greenTime d n (y + unit i) z + greenTime d n (y - unit i) z)) * ζ z =
            ∑ i : Fin d, (greenTime d n (y + unit i) z * ζ z +
              greenTime d n (y - unit i) z * ζ z) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [greenTime_succ_avg, add_mul, div_mul_eq_mul_div, hmul]
      rw [tsum_congr key]
      rw [Summable.tsum_add (summable_heatKernel_zero_mul y ζ) ?_]
      · rw [tsum_heatKernel_zero_mul]
        show ζ y + avg (membrane ζ n) y = _
        congr 1
        unfold avg LatticeProb.walkOp nbrSum
        rw [tsum_div_const]
        congr 1
        rw [Summable.tsum_finsetSum (fun i _ => (hsum (y + unit i)).add (hsum (y - unit i)))]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Summable.tsum_add (hsum (y + unit i)) (hsum (y - unit i)), ih, ih]
      · refine Summable.div_const ?_ _
        exact summable_finsetSum _ fun i _ => (hsum (y + unit i)).add (hsum (y - unit i))

end Sandpile
