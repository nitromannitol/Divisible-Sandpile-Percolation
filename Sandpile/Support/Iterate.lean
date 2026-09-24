/-
The algebra of the averaging operator and the heat kernel.

`sandpile.tex` writes `P^m u_n(0) = \sum_z p_m(0,z) u_n(z)` and, in the proof of
`lem:dgt4-smoothed-odometer-tail`, `\sum_z p_m(0,z) g_n(z,y) = \sum_{j<n}
p_{m+j}(0,y)`.  Both are identities about the shared recursion: the iterate of
the averaging operator IS the heat kernel, and the heat kernel is a semigroup.
Every sum here is finitely supported, since `p_k(x, ·)` vanishes outside the box
of radius `k` about `x`, so no summability hypothesis is ever needed.
-/
import Sandpile.Support.Kernel

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- A field summed against the heat kernel is a finite sum over the box. -/
theorem tsum_heatKernel_mul_eq_sum (k : ℕ) (x : Site d) (f : Site d → ℝ) :
    ∑' z : Site d, heatKernel d k x z * f z
      = ∑ z ∈ boxFinset x k, heatKernel d k x z * f z := by
  refine tsum_eq_sum fun z hz => ?_
  have hp : heatKernel d k x z = 0 := by
    by_contra hne
    exact hz (mem_boxFinset (heatKernel_support k x hne))
  simp [hp]

theorem summable_heatKernel_mul (k : ℕ) (x : Site d) (f : Site d → ℝ) :
    Summable fun z : Site d => heatKernel d k x z * f z := by
  refine summable_of_ne_finset_zero (s := boxFinset x k) fun z hz => ?_
  have hp : heatKernel d k x z = 0 := by
    by_contra hne
    exact hz (mem_boxFinset (heatKernel_support k x hne))
  simp [hp]

/-- The heat kernel is a probability kernel. -/
theorem tsum_heatKernel (hd : 1 ≤ d) : ∀ (k : ℕ) (x : Site d),
    ∑' y : Site d, heatKernel d k x y = 1 := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  intro k
  induction k with
  | zero =>
      intro x
      have hcongr : ∀ y : Site d, heatKernel d 0 x y = if y = x then (1 : ℝ) else 0 := by
        intro y
        show (if x = y then (1 : ℝ) else 0) = _
        by_cases h : x = y
        · simp [h]
        · rw [if_neg h, if_neg (fun hc : y = x => h hc.symm)]
      rw [tsum_congr hcongr, tsum_ite_eq]
  | succ n ih =>
      intro x
      have hstep : ∀ y : Site d, heatKernel d (n + 1) x y
          = (∑ i : Fin d, (heatKernel d n (x + unit i) y
              + heatKernel d n (x - unit i) y)) / (2 * (d : ℝ)) := fun y => rfl
      have hs1 : ∀ w : Site d, Summable fun y : Site d => heatKernel d n w y := by
        intro w
        have := summable_heatKernel_mul n w (fun _ => (1 : ℝ))
        simpa using this
      have hsum : ∀ i : Fin d, Summable fun y : Site d =>
          heatKernel d n (x + unit i) y + heatKernel d n (x - unit i) y :=
        fun i => (hs1 (x + unit i)).add (hs1 (x - unit i))
      calc ∑' y : Site d, heatKernel d (n + 1) x y
          = ∑' y : Site d, (∑ i : Fin d, (heatKernel d n (x + unit i) y
              + heatKernel d n (x - unit i) y)) / (2 * (d : ℝ)) := tsum_congr hstep
        _ = (∑' y : Site d, ∑ i : Fin d, (heatKernel d n (x + unit i) y
              + heatKernel d n (x - unit i) y)) / (2 * (d : ℝ)) := by
              rw [tsum_div_const]
        _ = (∑ i : Fin d, ∑' y : Site d, (heatKernel d n (x + unit i) y
              + heatKernel d n (x - unit i) y)) / (2 * (d : ℝ)) := by
              rw [Summable.tsum_finsetSum fun i _ => hsum i]
        _ = 1 := by
              have hone : ∀ i : Fin d, (∑' y : Site d, (heatKernel d n (x + unit i) y
                  + heatKernel d n (x - unit i) y)) = 2 := by
                intro i
                rw [Summable.tsum_add (hs1 (x + unit i)) (hs1 (x - unit i)),
                  ih (x + unit i), ih (x - unit i)]
                norm_num
              rw [Finset.sum_congr rfl fun i _ => hone i]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp

/-- The heat kernel is a semigroup: Chapman-Kolmogorov. -/
theorem tsum_heatKernel_mul_heatKernel : ∀ (a b : ℕ) (x y : Site d),
    ∑' z : Site d, heatKernel d a x z * heatKernel d b z y = heatKernel d (a + b) x y := by
  intro a
  induction a with
  | zero =>
      intro b x y
      have hcongr : ∀ z : Site d, heatKernel d 0 x z * heatKernel d b z y
          = if z = x then heatKernel d b z y else 0 := by
        intro z
        show (if x = z then (1 : ℝ) else 0) * heatKernel d b z y = _
        by_cases h : x = z
        · simp [h]
        · rw [if_neg h, if_neg (fun hc : z = x => h hc.symm), zero_mul]
      rw [tsum_congr hcongr, tsum_ite_eq]
      simp
  | succ n ih =>
      intro b x y
      have hstep : ∀ z : Site d, heatKernel d (n + 1) x z * heatKernel d b z y
          = (∑ i : Fin d, (heatKernel d n (x + unit i) z * heatKernel d b z y
              + heatKernel d n (x - unit i) z * heatKernel d b z y)) / (2 * (d : ℝ)) := by
        intro z
        show ((∑ i : Fin d, (heatKernel d n (x + unit i) z
            + heatKernel d n (x - unit i) z)) / (2 * (d : ℝ))) * heatKernel d b z y = _
        rw [div_mul_eq_mul_div, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      have hsum : ∀ i : Fin d, Summable fun z : Site d =>
          heatKernel d n (x + unit i) z * heatKernel d b z y
            + heatKernel d n (x - unit i) z * heatKernel d b z y :=
        fun i => (summable_heatKernel_mul n (x + unit i) _).add
          (summable_heatKernel_mul n (x - unit i) _)
      have hval : ∀ i : Fin d, (∑' z : Site d,
          (heatKernel d n (x + unit i) z * heatKernel d b z y
            + heatKernel d n (x - unit i) z * heatKernel d b z y))
          = heatKernel d (n + b) (x + unit i) y + heatKernel d (n + b) (x - unit i) y := by
        intro i
        rw [Summable.tsum_add (summable_heatKernel_mul n (x + unit i) _)
          (summable_heatKernel_mul n (x - unit i) _), ih b (x + unit i) y, ih b (x - unit i) y]
      calc ∑' z : Site d, heatKernel d (n + 1) x z * heatKernel d b z y
          = ∑' z : Site d, (∑ i : Fin d,
              (heatKernel d n (x + unit i) z * heatKernel d b z y
                + heatKernel d n (x - unit i) z * heatKernel d b z y)) / (2 * (d : ℝ)) :=
            tsum_congr hstep
        _ = (∑ i : Fin d, ∑' z : Site d,
              (heatKernel d n (x + unit i) z * heatKernel d b z y
                + heatKernel d n (x - unit i) z * heatKernel d b z y)) / (2 * (d : ℝ)) := by
              rw [tsum_div_const, Summable.tsum_finsetSum fun i _ => hsum i]
        _ = (∑ i : Fin d, (heatKernel d (n + b) (x + unit i) y
              + heatKernel d (n + b) (x - unit i) y)) / (2 * (d : ℝ)) := by
              rw [Finset.sum_congr rfl fun i _ => hval i]
        _ = heatKernel d (n + 1 + b) x y := by
              rw [show n + 1 + b = n + b + 1 by omega]
              rfl

/-- The iterate of the averaging operator is the heat kernel. -/
theorem avg_iterate (m : ℕ) (f : Site d → ℝ) (x : Site d) :
    (avg^[m] f) x = ∑' z : Site d, heatKernel d m x z * f z := by
  induction m generalizing x with
  | zero =>
      have hcongr : ∀ z : Site d, heatKernel d 0 x z * f z = if z = x then f z else 0 := by
        intro z
        show (if x = z then (1 : ℝ) else 0) * f z = _
        by_cases h : x = z
        · simp [h]
        · rw [if_neg h, if_neg (fun hc : z = x => h hc.symm), zero_mul]
      rw [Function.iterate_zero_apply, tsum_congr hcongr, tsum_ite_eq]
  | succ n ih =>
      have hrec : (avg^[n + 1] f) x = avg (avg^[n] f) x := by
        rw [Function.iterate_succ_apply']
      rw [hrec]
      show (∑ i : Fin d, ((avg^[n] f) (x + unit i) + (avg^[n] f) (x - unit i))) / (2 * (d : ℝ))
        = _
      have hsum : ∀ i : Fin d, Summable fun z : Site d =>
          heatKernel d n (x + unit i) z * f z + heatKernel d n (x - unit i) z * f z :=
        fun i => (summable_heatKernel_mul n (x + unit i) f).add
          (summable_heatKernel_mul n (x - unit i) f)
      have hstep : ∀ z : Site d, heatKernel d (n + 1) x z * f z
          = (∑ i : Fin d, (heatKernel d n (x + unit i) z * f z
              + heatKernel d n (x - unit i) z * f z)) / (2 * (d : ℝ)) := by
        intro z
        show ((∑ i : Fin d, (heatKernel d n (x + unit i) z
            + heatKernel d n (x - unit i) z)) / (2 * (d : ℝ))) * f z = _
        rw [div_mul_eq_mul_div, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [tsum_congr hstep, tsum_div_const, Summable.tsum_finsetSum fun i _ => hsum i]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Summable.tsum_add (summable_heatKernel_mul n (x + unit i) f)
        (summable_heatKernel_mul n (x - unit i) f), ih (x + unit i), ih (x - unit i)]

/-- The averaged Green kernel of `lem:dgt4-smoothed-odometer-tail`:
`\sum_z p_m(0,z) g_n(z,y) = \sum_{j<n} p_{m+j}(0,y)`. -/
theorem tsum_heatKernel_mul_greenTime (m n : ℕ) (x y : Site d) :
    ∑' z : Site d, heatKernel d m x z * greenTime d n z y
      = ∑ j ∈ Finset.range n, heatKernel d (m + j) x y := by
  have hexp : ∀ z : Site d, heatKernel d m x z * greenTime d n z y
      = ∑ j ∈ Finset.range n, heatKernel d m x z * heatKernel d j z y := by
    intro z
    show heatKernel d m x z * (∑ j ∈ Finset.range n, heatKernel d j z y)
        = ∑ j ∈ Finset.range n, heatKernel d m x z * heatKernel d j z y
    rw [Finset.mul_sum]
  rw [tsum_congr hexp,
    Summable.tsum_finsetSum fun j (_ : j ∈ Finset.range n) => summable_heatKernel_mul m x _]
  exact Finset.sum_congr rfl fun j _ => tsum_heatKernel_mul_heatKernel m j x y

end Sandpile
