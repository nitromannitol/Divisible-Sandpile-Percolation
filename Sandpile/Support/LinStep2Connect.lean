import Sandpile.Support.LinStep2Averaged

/-! # Step 2 Window Connectors

The connectors between the hypothesis `eq:dgt4-uniform-contact-thresholds` and the window
form Step 2 consumes (`sandpile.tex:5472-5479`, `sandpile.tex:5531-5565`).

The hypothesis bounds a SUM of two nonnegative quantities uniformly over the window
`\lceil\varepsilon n_R\rceil\leq m\leq n_R`.  Step 2 uses the two separately: the first
summand is the relative error in the weights and the second is the threshold-replacement
error.  `window_of_thresholds` splits them, over the times `m=n_R-r` with `r\leq j` that the
path actually visits; `ceil_le_sub_of_window` is the observation that those times lie in the
window, because `r\leq j\leq(1-\varepsilon)n_R` makes `n_R-r` an integer at least
`\varepsilon n_R`.

`weight_le_half` is the remaining smallness the product-to-exponential step needs: the
weights are at most `2G(0,0)\kappa/(n_R-r)\leq2G(0,0)\kappa/(\varepsilon n_R)`, hence at
most `1/2` once `4G(0,0)\kappa\leq\varepsilon n_R`.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The times `n_R-r` a path of at most `(1-\varepsilon)n_R` steps visits lie in the window
`\lceil\varepsilon n_R\rceil\leq m\leq n_R`. -/
theorem ceil_le_sub_of_window (n j r : ℕ) (hj : j < n) (hr : r ≤ j) (ε : ℝ)
    (_hε0 : 0 < ε) (hjn : (j : ℝ) ≤ (1 - ε) * (n : ℝ)) :
    ⌈ε * (n : ℝ)⌉₊ ≤ n - r := by
  have hrn : r ≤ n := le_of_lt (lt_of_le_of_lt hr hj)
  have hrR : (r : ℝ) ≤ (j : ℝ) := by exact_mod_cast hr
  have hge : ε * (n : ℝ) ≤ ((n - r : ℕ) : ℝ) := by
    rw [cast_nat_sub_eq n r hrn]
    nlinarith [hjn, hrR]
  exact Nat.ceil_le.mpr hge

/-- **The two summands of `eq:dgt4-uniform-contact-thresholds`, separately.**  Both are
nonnegative, so a bound on their sum over the window is a bound on each along the path. -/
theorem window_of_thresholds (n j : ℕ) (hj : j < n) (ε : ℝ) (hε0 : 0 < ε)
    (hjn : (j : ℝ) ≤ (1 - ε) * (n : ℝ)) (η : ℝ) (A B : ℕ → ℝ)
    (hA : ∀ m, 0 ≤ A m) (hB : ∀ m, 0 ≤ B m)
    (h : ∀ m : ℕ, ⌈ε * (n : ℝ)⌉₊ ≤ m → m ≤ n → A m + B m ≤ η) :
    (∀ r, r ≤ j → A (n - r) ≤ η) ∧ (∀ r, r ≤ j → B (n - r) ≤ η) := by
  have hkey : ∀ r, r ≤ j → A (n - r) + B (n - r) ≤ η := by
    intro r hr
    exact h (n - r) (ceil_le_sub_of_window n j r hj hr ε hε0 hjn) (by omega)
  exact ⟨fun r hr => by linarith [hkey r hr, hB (n - r)],
    fun r hr => by linarith [hkey r hr, hA (n - r)]⟩

/-- The weights are at most `1/2` once `4G(0,0)\kappa\leq\varepsilon n_R`, which is what the
logarithm expansion of `sandpile.tex:5556` needs. -/
theorem weight_le_half (n j : ℕ) (hj : j < n) (ε Gk : ℝ) (_hε0 : 0 < ε) (hGk : 0 < Gk)
    (hjn : (j : ℝ) ≤ (1 - ε) * (n : ℝ)) (hn : 4 * Gk ≤ ε * (n : ℝ))
    (pi : ℕ → ℝ) (hpiu : ∀ r ∈ Finset.range (j + 1), pi r ≤ 2 * Gk / ((n - r : ℕ) : ℝ)) :
    ∀ r ∈ Finset.range (j + 1), pi r ≤ 1 / 2 := by
  intro r hr
  have hrj : r ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hrn : r ≤ n := le_of_lt (lt_of_le_of_lt hrj hj)
  have hrR : (r : ℝ) ≤ (j : ℝ) := by exact_mod_cast hrj
  have hge : ε * (n : ℝ) ≤ ((n - r : ℕ) : ℝ) := by
    rw [cast_nat_sub_eq n r hrn]
    nlinarith [hjn, hrR]
  have hpos : (0 : ℝ) < ((n - r : ℕ) : ℝ) := by linarith [hn, hGk]
  have hdiv : 2 * Gk / ((n - r : ℕ) : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
    linarith [hn, hge]
  exact le_trans (hpiu r hr) hdiv

end Sandpile
