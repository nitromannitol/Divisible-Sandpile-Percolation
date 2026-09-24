/-
The harmonic bookkeeping of Step 2 of `lem:dgt4-path-survival` and the time weight of
`prop:dgt4-linearization`.

`eq:dgt4-path-contact-replacement` (`sandpile.tex:5532-5550`) bounds the probability that one
of the contact events differs from its threshold event by
`[max_m m P(…)] ∑_{m=⌈εn_R⌉}^{n_R} 1/m`.  Turning the uniform bound `m P(…) ≤ η` into that
product is `sum_le_of_mul_le`, and reindexing the sum over the times `r ≤ j` as a sum over
the levels `m = n_R - r` is `sum_inv_range_sub_eq`; `sum_inv_Icc_le` of
`Support/LinProduct.lean` then supplies `1 + \log(n/k)`.

`weight_mem_Icc` is the hypothesis `q_{R,j} ∈ [0,1]` that
`lem:dgt4-linearization-from-survival` asks of the time weight
`q_{R,j} = (1 - j/(R^2T))^κ` of `prop:dgt4-linearization`.

`eventually_uniform_window_of_tendsto` is the observation that the uniformity of
`eq:dgt4-uniform-contact-thresholds` over the window `⌈ε n_R⌉ ≤ m ≤ n_R` is free once the
underlying quantity tends to zero in `m`: the left end of the window tends to infinity.
-/
import Sandpile.Support.LinProduct
import Sandpile.Support.LinThresholdNull

open Filter Topology MeasureTheory

namespace Sandpile

/-- The last-visit harmonic sum reindexed: `∑_{r≤j} 1/(n-r) = ∑_{m=n-j}^{n} 1/m`. -/
theorem sum_inv_range_sub_eq (n j : ℕ) (hj : j ≤ n) :
    ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹
      = ∑ m ∈ Finset.Icc (n - j) n, ((m : ℝ))⁻¹ := by
  have hIcc : Finset.Icc (n - j) n = Finset.Ico (n - j) (n + 1) := (Finset.Ico_add_one_right_eq_Icc _ _).symm
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hlen : n + 1 - (n - j) = j + 1 := by omega
  rw [hlen, ← Finset.sum_range_reflect (fun i => (((n - j + i : ℕ)) : ℝ)⁻¹) (j + 1)]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  have harg : n - r = n - j + (j + 1 - 1 - r) := by omega
  rw [harg]

/-- From the uniform bound `m · f(r) ≤ η` with `m = n - r` to the harmonic sum bound. -/
theorem sum_le_of_mul_le (n j : ℕ) (eta : ℝ) (f : ℕ → ℝ)
    (hpos : ∀ r ∈ Finset.range (j + 1), (0 : ℝ) < ((n - r : ℕ) : ℝ))
    (hb : ∀ r ∈ Finset.range (j + 1), ((n - r : ℕ) : ℝ) * f r ≤ eta) :
    ∑ r ∈ Finset.range (j + 1), f r
      ≤ eta * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hp := hpos r hr
  have hbb := hb r hr
  rw [inv_eq_one_div, mul_one_div, le_div_iff₀ hp]
  linarith

/-- The time weight `(1 - j/(R^2T))^κ` of `prop:dgt4-linearization` lies in `[0,1]` for
every `j` below `n_R`. -/
theorem weight_mem_Icc (T : ℝ) (hT : 0 < T) (kappa : ℝ) (hk : 0 < kappa) (R : ℝ) (hR : 0 < R)
    (j : ℕ) (hj : j < ⌊R ^ 2 * T⌋₊) :
    (1 - (j : ℝ) / (R ^ 2 * T)) ^ kappa ∈ Set.Icc (0 : ℝ) 1 := by
  have hRT : (0:ℝ) < R ^ 2 * T := by positivity
  have hfl : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le hRT.le
  have hjlt : ((j : ℕ) : ℝ) < R ^ 2 * T := by
    have h1 : ((j : ℕ) : ℝ) < ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by exact_mod_cast hj
    linarith
  have hbase0 : (0:ℝ) ≤ 1 - (j : ℝ) / (R ^ 2 * T) := by
    have h2 : (j : ℝ) / (R ^ 2 * T) ≤ 1 := (div_le_one hRT).mpr hjlt.le
    linarith
  have hbase1 : 1 - (j : ℝ) / (R ^ 2 * T) ≤ 1 := by
    have h3 : (0:ℝ) ≤ (j : ℝ) / (R ^ 2 * T) := div_nonneg (Nat.cast_nonneg j) hRT.le
    linarith
  exact ⟨Real.rpow_nonneg hbase0 kappa, Real.rpow_le_one hbase0 hbase1 hk.le⟩

/-- A nonnegative sequence tending to zero is uniformly small on the window
`⌈ε n_R⌉ ≤ m ≤ n_R`: the uniformity of `eq:dgt4-uniform-contact-thresholds` is free. -/
theorem eventually_uniform_window_of_tendsto (T : ℝ) (hT : 0 < T) (F : ℕ → ℝ)
    (hF : Tendsto F atTop (𝓝 0)) (eps : ℝ) (heps : 0 < eps) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ R : ℝ in atTop, ∀ m : ℕ,
      ⌈eps * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ → F m ≤ eta := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hF.eventually (eventually_lt_nhds heta))
  have hsq : Tendsto (fun R : ℝ => R ^ 2 * T) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).atTop_mul_const hT
  have hfl : Tendsto (fun R : ℝ => ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp hsq)
  have hmul : Tendsto (fun R : ℝ => eps * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)) atTop atTop :=
    hfl.const_mul_atTop heps
  have hev : ∀ᶠ R : ℝ in atTop, (N : ℝ) ≤ eps * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) :=
    hmul.eventually_ge_atTop (N : ℝ)
  filter_upwards [hev] with R hR
  intro m hm1 _
  have hNm : N ≤ m := by
    have h1 : (N : ℝ) ≤ ((⌈eps * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) :=
      le_trans hR (Nat.le_ceil _)
    have h2 : N ≤ ⌈eps * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)⌉₊ := by exact_mod_cast h1
    exact le_trans h2 hm1
  exact le_of_lt (hN m hNm)

/-- **`eq:dgt4-path-contact-replacement`** (`sandpile.tex:5527-5545`) in its abstract form:
when the symmetric difference at time `r` has probability at most `η/(n-r)`, the two
intersections over `0 ≤ r ≤ j` differ in probability by at most `η ∑_{r≤j} 1/(n-r)`. -/
theorem abs_measureReal_iInter_sub_le_harmonic {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsFiniteMeasure mu] (n j : ℕ) (A B : ℕ → Set alpha) (eta : ℝ)
    (hpos : ∀ r ∈ Finset.range (j + 1), (0 : ℝ) < ((n - r : ℕ) : ℝ))
    (hb : ∀ r ∈ Finset.range (j + 1),
      ((n - r : ℕ) : ℝ) * mu.real (symmDiff (A r) (B r)) ≤ eta) :
    |mu.real (⋂ r ∈ Finset.range (j + 1), A r) - mu.real (⋂ r ∈ Finset.range (j + 1), B r)|
      ≤ eta * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ := by
  exact le_trans (abs_measureReal_iInter_sub_le_all mu (Finset.range (j + 1)) A B)
    (sum_le_of_mul_le n j eta (fun r => mu.real (symmDiff (A r) (B r))) hpos hb)

end Sandpile
