/-
The two ends of Step 2 of `lem:dgt4-path-survival`: the survival probability lies in
`[0,1]`, and the split of `R^{-2}\sum_{j<n_R}` at `(1-\varepsilon)n_R`
(`sandpile.tex:5571-5583`).

The paper's last paragraph of Step 2 reads: "Thus each summand in
\eqref{eq:dgt4-averaged-positive-path-limit} tends to zero uniformly for
`j\leq(1-\varepsilon)n_R`.  The remaining indices contribute at most
`\varepsilon T+o(1)` after multiplication by `R^{-2}`.  Letting first `R\to\infty` and
then `\varepsilon\downarrow0` proves \eqref{eq:dgt4-averaged-positive-path-limit}."

`tendsto_inv_sq_sum_of_uniform` is exactly that reduction, with no probability in it: a
family `F R j` with values in `[0,1]` whose early indices are eventually uniformly small has
`R^{-2}\sum_{j<n_R}F R j\to0`.  The two halves of the split are
`sum_range_split_le`, which bounds the sum by `m c+(n-m)` using the value bound `1` on the
late indices, and `inv_sq_sum_range_le`, which turns that into `Tc+\varepsilon T` using
`n_R\leq R^2T` and `(1-\varepsilon)n_R\leq m`.  The two `\varepsilon`-choices of the
paper's "first `R`, then `\varepsilon`" are made at once: for a target `\eta` the proof
takes `\varepsilon=\min\{1/2,\eta/(4T)\}` and the uniform bound `c=\eta/(4T)`.
-/
import Sandpile.Support.LinStep2Integral

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The split of a sum over `range n` at `m`: the early indices are bounded by `c`, the late
ones by the value bound `1`. -/
theorem sum_range_split_le (n m : ℕ) (hmn : m ≤ n) (f : ℕ → ℝ) (c : ℝ)
    (hsmall : ∀ j ∈ Finset.range m, f j ≤ c) (hf1 : ∀ j, f j ≤ 1) :
    ∑ j ∈ Finset.range n, f j ≤ (m : ℝ) * c + ((n : ℝ) - (m : ℝ)) := by
  have hsplit : ∑ j ∈ Finset.Ico 0 m, f j + ∑ j ∈ Finset.Ico m n, f j
      = ∑ j ∈ Finset.Ico 0 n, f j := Finset.sum_Ico_consecutive f (Nat.zero_le m) hmn
  simp only [← Finset.range_eq_Ico] at hsplit
  have h1 : ∑ j ∈ Finset.range m, f j ≤ (m : ℝ) * c := by
    calc ∑ j ∈ Finset.range m, f j ≤ ∑ _j ∈ Finset.range m, c := Finset.sum_le_sum hsmall
      _ = (m : ℝ) * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h2 : ∑ j ∈ Finset.Ico m n, f j ≤ (n : ℝ) - (m : ℝ) := by
    calc ∑ j ∈ Finset.Ico m n, f j ≤ ∑ _j ∈ Finset.Ico m n, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => hf1 j
      _ = ((n - m : ℕ) : ℝ) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
      _ = (n : ℝ) - (m : ℝ) := by rw [Nat.cast_sub hmn]
  linarith [hsplit, h1, h2]

/-- **The split of `R^{-2}\sum_{j<n_R}` at `(1-\varepsilon)n_R`** (`sandpile.tex:5573-5576`).
With `n_R\leq R^2T` and `(1-\varepsilon)n_R\leq m`, the early indices contribute at most
`Tc` and the late ones at most `\varepsilon T`. -/
theorem inv_sq_sum_range_le (R T ε c : ℝ) (hR : 0 < R) (hT : 0 < T) (hε0 : 0 < ε)
    (hc : 0 ≤ c) (n m : ℕ) (hn : (n : ℝ) ≤ R ^ 2 * T) (hm : m ≤ n)
    (hmlb : (1 - ε) * (n : ℝ) ≤ (m : ℝ))
    (f : ℕ → ℝ) (hsmall : ∀ j ∈ Finset.range m, f j ≤ c) (hf1 : ∀ j, f j ≤ 1) :
    (R ^ 2)⁻¹ * ∑ j ∈ Finset.range n, f j ≤ T * c + ε * T := by
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
  have hstep := sum_range_split_le n m hm f c hsmall hf1
  have hsum : ∑ j ∈ Finset.range n, f j ≤ (n : ℝ) * c + ε * (n : ℝ) := by
    have h1 : (m : ℝ) * c ≤ (n : ℝ) * c := mul_le_mul_of_nonneg_right hmn hc
    have h2 : (n : ℝ) - (m : ℝ) ≤ ε * (n : ℝ) := by nlinarith [hmlb]
    linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hkey : (n : ℝ) * c + ε * (n : ℝ) ≤ R ^ 2 * (T * c + ε * T) := by
    nlinarith [hn, hc, hε0.le, hn0]
  calc (R ^ 2)⁻¹ * ∑ j ∈ Finset.range n, f j
      ≤ (R ^ 2)⁻¹ * ((n : ℝ) * c + ε * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hR2))
    _ ≤ (R ^ 2)⁻¹ * (R ^ 2 * (T * c + ε * T)) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt (inv_pos.mpr hR2))
    _ = T * c + ε * T := by field_simp

/-- **The reduction of `eq:dgt4-averaged-positive-path-limit` to uniform smallness on
`j\leq(1-\varepsilon)n_R`** (`sandpile.tex:5570-5578`).  A family with values in `[0,1]`
whose early indices are eventually uniformly small has `R^{-2}\sum_{j<n_R}F R j\to0`. -/
theorem tendsto_inv_sq_sum_of_uniform (T : ℝ) (hT : 0 < T) (F : ℝ → ℕ → ℝ)
    (hF0 : ∀ R j, 0 ≤ F R j) (hF1 : ∀ R j, F R j ≤ 1)
    (hunif : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ c : ℝ, 0 < c → ∀ᶠ R : ℝ in atTop,
      ∀ j : ℕ, j ≤ ⌊(1 - ε) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)⌋₊ → F R j ≤ c) :
    Tendsto (fun R : ℝ => (R ^ 2)⁻¹ * ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊, F R j)
      atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro η hη
  set ε : ℝ := min (1 / 2) (η / (4 * T)) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hεT : ε * T ≤ η / 4 := by
    have h := min_le_right (1 / 2 : ℝ) (η / (4 * T))
    have : ε * T ≤ (η / (4 * T)) * T := mul_le_mul_of_nonneg_right h hT.le
    calc ε * T ≤ (η / (4 * T)) * T := this
      _ = η / 4 := by field_simp
  set c : ℝ := η / (4 * T) with hcdef
  have hc0 : 0 < c := by positivity
  have hTc : T * c ≤ η / 4 := by
    rw [hcdef]
    field_simp
    norm_num
  filter_upwards [hunif ε ⟨hε0, hε1⟩ c hc0, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / T)] with R hsmall hR0 hR1 hRT
  have hRT' : (1 : ℝ) ≤ R * T := by
    have h := mul_le_mul_of_nonneg_right hRT hT.le
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt hT)] at h
  have hRT1 : (1 : ℝ) ≤ R ^ 2 * T := by
    nlinarith [hRT', hR1, hT.le,
      mul_nonneg (mul_nonneg hR0.le hT.le) (by linarith : (0 : ℝ) ≤ R - 1)]
  set n : ℕ := ⌊R ^ 2 * T⌋₊ with hndef
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hRT1)
  have hnle : (n : ℝ) ≤ R ^ 2 * T := Nat.floor_le (by positivity)
  set m : ℕ := ⌊(1 - ε) * (n : ℝ)⌋₊ + 1 with hmdef
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hfloorlt : ⌊(1 - ε) * (n : ℝ)⌋₊ < n := by
    rw [Nat.floor_lt (by nlinarith [hε1, hn0R])]
    nlinarith [hε0, hn0R]
  have hm : m ≤ n := hfloorlt
  have hmlb : (1 - ε) * (n : ℝ) ≤ (m : ℝ) := by
    have := Nat.lt_floor_add_one ((1 - ε) * (n : ℝ))
    rw [hmdef]
    push_cast
    linarith
  have hkey := inv_sq_sum_range_le R T ε c hR0 hT hε0 hc0.le n m hnle hm hmlb (F R)
    (fun j hj => hsmall j (by
      have := Finset.mem_range.mp hj
      omega)) (fun j => hF1 R j)
  have hnn : 0 ≤ (R ^ 2)⁻¹ * ∑ j ∈ Finset.range n, F R j := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ => hF0 R j
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  linarith [hkey, hTc, hεT]

/-- The survival probability is nonnegative. -/
theorem survivalProb_nonneg (ν : Measure ℝ) [IsProbabilityMeasure ν] (n j : ℕ)
    (X : ℕ → Site d) :
    0 ≤ ∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
        (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν) := by
  rw [integral_survival_eq_measureReal ν n j X]
  exact measureReal_nonneg

/-- The survival probability is at most one. -/
theorem survivalProb_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (n j : ℕ)
    (X : ℕ → Site d) :
    (∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
        (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) ≤ 1 := by
  rw [integral_survival_eq_measureReal ν n j X]
  exact measureReal_le_one

end Sandpile
