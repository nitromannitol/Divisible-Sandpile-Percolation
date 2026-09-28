import Sandpile.External.BerryEsseen
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Geometric row sums

The correlation matrix of the membrane fields at the geometric scales
`n_j = N q^j` has off-diagonal entries bounded by `K r^{|j-k|}` with
`r = q^{-1/4}`, so its rows carry off-diagonal mass at most `4 K r`.  Only the
elementary geometric estimates are here; the identification of `r` is in
`Sandpile/Support/CriticalScales.lean`.
-/

namespace Sandpile

/-- `∑_{i<n} r^i ≤ (1-r)⁻¹`. -/
theorem geom_range_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ (1 - r)⁻¹ := by
  have hs : Summable (fun i : ℕ => r ^ i) := summable_geometric_of_lt_one h0 h1
  have hle : ∑ i ∈ Finset.range n, r ^ i ≤ ∑' i : ℕ, r ^ i :=
    Summable.sum_le_tsum _ (fun i _ => by positivity) hs
  rwa [tsum_geometric_of_lt_one h0 h1] at hle

/-- `∑_{i<n} r^{i+1} ≤ 2r` when `0 ≤ r ≤ 1/2`. -/
theorem geom_succ_le {r : ℝ} (h0 : 0 ≤ r) (h : r ≤ 1 / 2) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ (i + 1) ≤ 2 * r := by
  have h1 : r < 1 := by linarith
  have hpow : ∀ i : ℕ, r ^ (i + 1) = r * r ^ i := fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => hpow i), ← Finset.mul_sum]
  have hg := geom_range_le h0 h1 n
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.range n) => pow_nonneg h0 i)]

/-- `∑_{k<n} r^{n-k} ≤ 2r`. -/
theorem geom_down_le {r : ℝ} (h0 : 0 ≤ r) (h : r ≤ 1 / 2) (n : ℕ) :
    ∑ k ∈ Finset.range n, r ^ (n - k) ≤ 2 * r := by
  have hrefl := Finset.sum_range_reflect (fun i => r ^ (i + 1)) n
  have heq : ∑ k ∈ Finset.range n, r ^ (n - k)
      = ∑ j ∈ Finset.range n, r ^ (n - 1 - j + 1) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have : n - 1 - k + 1 = n - k := by
      have := Finset.mem_range.mp hk; omega
    rw [this]
  rw [heq, hrefl]
  exact geom_succ_le h0 h n

end Sandpile

namespace Sandpile

/-- The lower half of an off-diagonal geometric row. -/
theorem sum_geom_below_le {m : ℕ} {r : ℝ} (h0 : 0 ≤ r) (h : r ≤ 1 / 2) (J : ℕ) (hJ : J < m) :
    ∑ k : Fin m, (if (k : ℕ) < J then r ^ (J - (k : ℕ)) else 0) ≤ 2 * r := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < J then r ^ (J - k) else 0) m]
  have hsub : Finset.range J ⊆ Finset.range m := by
    intro k hk
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) (le_of_lt hJ))
  have hzero : ∀ k ∈ Finset.range m, k ∉ Finset.range J →
      (if k < J then r ^ (J - k) else 0) = 0 := by
    intro k _ hk
    rw [if_neg (by simpa using hk)]
  rw [← Finset.sum_subset hsub hzero]
  refine le_trans (le_of_eq ?_) (geom_down_le h0 h J)
  exact Finset.sum_congr rfl fun k hk => by rw [if_pos (Finset.mem_range.mp hk)]

/-- The upper half of an off-diagonal geometric row. -/
theorem sum_geom_above_le {m : ℕ} {r : ℝ} (h0 : 0 ≤ r) (h : r ≤ 1 / 2) (J : ℕ) :
    ∑ k : Fin m, (if J < (k : ℕ) then r ^ ((k : ℕ) - J) else 0) ≤ 2 * r := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if J < k then r ^ (k - J) else 0) m]
  have hsub : Finset.Ico (J + 1) m ⊆ Finset.range m := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hzero : ∀ k ∈ Finset.range m, k ∉ Finset.Ico (J + 1) m →
      (if J < k then r ^ (k - J) else 0) = 0 := by
    intro k hk hk2
    have hkm := Finset.mem_range.mp hk
    have : ¬ (J < k) := by
      by_contra hc
      exact hk2 (Finset.mem_Ico.mpr ⟨by omega, hkm⟩)
    rw [if_neg this]
  rw [← Finset.sum_subset hsub hzero]
  have heq : ∑ k ∈ Finset.Ico (J + 1) m, (if J < k then r ^ (k - J) else 0)
      = ∑ i ∈ Finset.range (m - (J + 1)), r ^ (i + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_pos (by omega)]
    congr 1
    omega
  rw [heq]
  exact geom_succ_le h0 h _

/-- **The off-diagonal mass of a geometric row.** -/
theorem sum_geom_offdiag_le {m : ℕ} {r : ℝ} (h0 : 0 ≤ r) (h : r ≤ 1 / 2) (j : Fin m) :
    ∑ k : Fin m,
        (if j = k then (0 : ℝ) else r ^ (max (k : ℕ) (j : ℕ) - min (k : ℕ) (j : ℕ)))
      ≤ 4 * r := by
  have hstep : ∀ k : Fin m,
      (if j = k then (0 : ℝ) else r ^ (max (k : ℕ) (j : ℕ) - min (k : ℕ) (j : ℕ)))
        ≤ (if (k : ℕ) < (j : ℕ) then r ^ ((j : ℕ) - (k : ℕ)) else 0)
          + (if (j : ℕ) < (k : ℕ) then r ^ ((k : ℕ) - (j : ℕ)) else 0) := by
    intro k
    rcases lt_trichotomy (k : ℕ) (j : ℕ) with hlt | heq | hgt
    · rw [if_neg (fun hc => by rw [hc] at hlt; omega), if_pos hlt, if_neg (by omega),
        max_eq_right hlt.le, min_eq_left hlt.le]
      simp
    · rw [if_pos (Fin.ext heq.symm), if_neg (by omega), if_neg (by omega)]
      norm_num
    · rw [if_neg (fun hc => by rw [hc] at hgt; omega), if_neg (by omega), if_pos hgt,
        max_eq_left hgt.le, min_eq_right hgt.le]
      simp
  refine le_trans (Finset.sum_le_sum fun k _ => hstep k) ?_
  rw [Finset.sum_add_distrib]
  have h1 := sum_geom_below_le (m := m) h0 h (j : ℕ) j.isLt
  have h2 := sum_geom_above_le (m := m) h0 h (j : ℕ)
  linarith

end Sandpile
