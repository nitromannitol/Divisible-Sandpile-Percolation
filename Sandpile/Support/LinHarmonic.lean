import Mathlib

/-!
# Harmonic-sum/logarithm comparison and a Cesàro smallness estimate

The partial harmonic sum `∑_{i=0}^{j} 1/(n-i)` is sandwiched between `log n - log (n - j)` and
`1/(n - j) + (log n - log (n - j))`, both bounds obtained from `log x ≤ x - 1` applied to the
ratios `(a+1)/a` and `(a-1)/a` and summed by telescoping; combined, they show the harmonic segment
differs from `-log (1 - j/n)` by at most the single term `1/(n - j)`. This file also proves a
Cesàro smallness estimate: a sequence tending to zero has partial sums that are eventually smaller
than any fixed positive multiple of the number of terms.
-/

open Finset
open scoped Topology

namespace Sandpile

/-- The partial harmonic sum `∑_{i=0}^{j} 1/(n-i)` is at least `log n - log (n - j)`. -/
theorem harm_tele_lower (n j : ℕ) (hj : j < n) :
    Real.log ((n : ℝ)) - Real.log ((n : ℝ) - (j : ℝ)) ≤
      ∑ i ∈ Finset.range (j + 1), (1 : ℝ) / ((n : ℝ) - (i : ℝ)) := by
  have hjn : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj
  set g : ℕ → ℝ := fun i => Real.log ((n : ℝ) - (i : ℝ) + 1) with hg
  have hpos : ∀ i ∈ Finset.range (j + 1), (0 : ℝ) < (n : ℝ) - (i : ℝ) := by
    intro i hi
    have : (i : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    linarith
  have hterm : ∀ i ∈ Finset.range (j + 1), g i - g (i + 1) ≤ (1 : ℝ) / ((n : ℝ) - (i : ℝ)) := by
    intro i hi
    have ha : (0 : ℝ) < (n : ℝ) - (i : ℝ) := hpos i hi
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have h1 : g (i + 1) = Real.log ((n : ℝ) - (i : ℝ)) := by
      rw [hg]; simp only []; rw [hcast]; ring_nf
    have h2 : g i - g (i + 1)
        = Real.log (((n : ℝ) - (i : ℝ) + 1) / ((n : ℝ) - (i : ℝ))) := by
      rw [h1, hg, Real.log_div (by positivity) (by positivity)]
    rw [h2]
    have := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < ((n : ℝ) - (i : ℝ) + 1) / ((n : ℝ) - (i : ℝ)) by positivity)
    have heq : ((n : ℝ) - (i : ℝ) + 1) / ((n : ℝ) - (i : ℝ)) - 1
        = 1 / ((n : ℝ) - (i : ℝ)) := by field_simp; ring
    linarith [this, heq.le, heq.ge]
  have hsum : ∑ i ∈ Finset.range (j + 1), (g i - g (i + 1)) = g 0 - g (j + 1) :=
    Finset.sum_range_sub' g (j + 1)
  have hg0 : g 0 = Real.log ((n : ℝ) + 1) := by rw [hg]; simp
  have hgj : g (j + 1) = Real.log ((n : ℝ) - (j : ℝ)) := by
    rw [hg]; simp only []; push_cast; ring_nf
  have hmono : Real.log ((n : ℝ)) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  calc Real.log ((n : ℝ)) - Real.log ((n : ℝ) - (j : ℝ))
      ≤ g 0 - g (j + 1) := by rw [hg0, hgj]; linarith
    _ = ∑ i ∈ Finset.range (j + 1), (g i - g (i + 1)) := hsum.symm
    _ ≤ ∑ i ∈ Finset.range (j + 1), (1 : ℝ) / ((n : ℝ) - (i : ℝ)) :=
        Finset.sum_le_sum hterm

/-- The partial harmonic sum `∑_{i=0}^{j} 1/(n-i)` is at most `1/(n - j) + (log n - log (n - j))`,
the matching upper bound to `harm_tele_lower`. -/
theorem harm_tele_upper (n j : ℕ) (hj : j < n) :
    ∑ i ∈ Finset.range (j + 1), (1 : ℝ) / ((n : ℝ) - (i : ℝ)) ≤
      1 / ((n : ℝ) - (j : ℝ)) + (Real.log ((n : ℝ)) - Real.log ((n : ℝ) - (j : ℝ))) := by
  have hjn : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj
  set h : ℕ → ℝ := fun i => Real.log ((n : ℝ) - (i : ℝ)) with hh
  have hterm : ∀ i ∈ Finset.range j, (1 : ℝ) / ((n : ℝ) - (i : ℝ)) ≤ h i - h (i + 1) := by
    intro i hi
    have hij : (i : ℝ) + 1 ≤ (j : ℝ) := by
      have : i + 1 ≤ j := Finset.mem_range.mp hi
      exact_mod_cast this
    have ha : (0 : ℝ) < (n : ℝ) - (i : ℝ) := by linarith
    have ha1 : (0 : ℝ) < (n : ℝ) - (i : ℝ) - 1 := by linarith
    have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have h1 : h (i + 1) = Real.log ((n : ℝ) - (i : ℝ) - 1) := by
      rw [hh]; simp only []; rw [hcast]; ring_nf
    have h2 : h i - h (i + 1)
        = -Real.log (((n : ℝ) - (i : ℝ) - 1) / ((n : ℝ) - (i : ℝ))) := by
      rw [h1, hh, Real.log_div (by positivity) (by positivity)]
      ring
    rw [h2]
    have hlog := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < ((n : ℝ) - (i : ℝ) - 1) / ((n : ℝ) - (i : ℝ)) by positivity)
    have heq : ((n : ℝ) - (i : ℝ) - 1) / ((n : ℝ) - (i : ℝ)) - 1
        = -(1 / ((n : ℝ) - (i : ℝ))) := by field_simp; ring
    linarith [hlog, heq.le, heq.ge]
  have hsum : ∑ i ∈ Finset.range j, (h i - h (i + 1)) = h 0 - h j :=
    Finset.sum_range_sub' h j
  have hh0 : h 0 = Real.log ((n : ℝ)) := by rw [hh]; simp
  have hhj : h j = Real.log ((n : ℝ) - (j : ℝ)) := by rw [hh]
  rw [Finset.sum_range_succ]
  have hle : ∑ i ∈ Finset.range j, (1 : ℝ) / ((n : ℝ) - (i : ℝ))
      ≤ ∑ i ∈ Finset.range j, (h i - h (i + 1)) := Finset.sum_le_sum hterm
  rw [hsum, hh0, hhj] at hle
  linarith

/-- Combining `harm_tele_lower` and `harm_tele_upper`: the partial harmonic sum
`∑_{i=0}^{j} 1/(n-i)` differs from `-log (1 - j/n)` by at most the single term `1/(n - j)`. -/
theorem abs_harm_log (n j : ℕ) (hj : j < n) (hn : 0 < n) :
    |(∑ i ∈ Finset.range (j + 1), (1 : ℝ) / ((n : ℝ) - (i : ℝ)))
        + Real.log (1 - (j : ℝ) / (n : ℝ))| ≤ 1 / ((n : ℝ) - (j : ℝ)) := by
  have hjn : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log (1 - (j : ℝ) / (n : ℝ))
      = Real.log ((n : ℝ) - (j : ℝ)) - Real.log ((n : ℝ)) := by
    have h1 : (1 : ℝ) - (j : ℝ) / (n : ℝ) = ((n : ℝ) - (j : ℝ)) / (n : ℝ) := by
      field_simp
    rw [h1, Real.log_div (by linarith) (by linarith)]
  rw [hlog, abs_le]
  constructor
  · have := harm_tele_lower n j hj
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) - (j : ℝ)) := by positivity
    linarith
  · have := harm_tele_upper n j hj
    linarith

open Filter Topology in
/-- **A Cesàro smallness estimate.** If `f` tends to `0`, then for every `η > 0` the partial
sums `∑_{k=0}^{n} f k` are eventually at most `η * n`. -/
theorem cesaro_small (f : ℕ → ℝ)
    (hf : Filter.Tendsto f Filter.atTop (nhds 0)) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop, ∑ k ∈ Finset.range (n + 1), f k ≤ η * (n : ℝ) := by
  have hhalf : (0 : ℝ) < η / 2 := by linarith
  have hc : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f i)
      Filter.atTop (nhds 0) := hf.cesaro
  have h1 : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f i < η / 2 := hc.eventually_lt_const hhalf
  have h2 : ∀ᶠ n : ℕ in Filter.atTop, f n < η / 2 := hf.eventually_lt_const hhalf
  have h3 : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ (n : ℝ) :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => by exact_mod_cast hn⟩
  filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hkey : ∑ i ∈ Finset.range n, f i < η / 2 * (n : ℝ) := by
    have h := mul_lt_mul_of_pos_left hn1 hnpos
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnpos), one_mul] at h
    linarith
  rw [Finset.sum_range_succ]
  nlinarith [hn2, hkey, hn3]

end Sandpile
