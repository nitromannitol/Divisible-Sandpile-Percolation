import Sandpile.Support.CriticalScaleBound

/-!
# Geometric scale counting

Counting the geometric scales, and the passage from the persistence ratio to a
power of the threshold.

`sandpile.tex:1738-1743` takes `m` maximal with `n_{m-1} ≤ t`, so that
`q^m > t/N ≥ L^a` and `m ≍ log L`.  The two logarithmic bounds on `m` and the
inequality `κ^m ≤ L^{-a|log κ|/log q}` are the only analytic content, and
neither uses anything about the sandpile.
-/

namespace Sandpile


/-- The number of geometric scales below `t`: the least `m` with `N q^m > t`. -/
theorem exists_scaleCount {N q t : ℕ} (hq : 2 ≤ q) (hNt : 1 ≤ N) (hNle : N ≤ t) :
    ∃ m : ℕ, 1 ≤ m ∧ (∀ j < m, N * q ^ j ≤ t) ∧ t < N * q ^ m := by
  classical
  have hex : ∃ j : ℕ, ¬ (N * q ^ j ≤ t) := by
    refine ⟨t + 1, ?_⟩
    have h1 : 2 ^ (t + 1) ≤ q ^ (t + 1) := Nat.pow_le_pow_left hq _
    have h2 : t + 1 < 2 ^ (t + 1) := Nat.lt_two_pow_self
    have h3 : q ^ (t + 1) ≤ N * q ^ (t + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  refine ⟨Nat.find hex, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · exfalso
      have := Nat.find_spec hex
      rw [h0] at this
      simp at this
      omega
    · exact hpos
  · intro j hj
    have := Nat.find_min hex hj
    omega
  · have := Nat.find_spec hex
    omega


/-- If `N ≤ t * L ^ (-a)` and `t < N * q ^ m`, then `a * log L / log q ≤ m`: substituting the
bound on `N` forces `L ^ a < q ^ m`, and taking logarithms gives the stated lower bound on
`m`. -/
theorem scaleCount_log_lower {N q t m : ℕ} (hq : 2 ≤ q) (_hN : 1 ≤ N) (ht : 1 ≤ t)
    (hgt : t < N * q ^ m) {a L : ℝ} (_ha : 0 < a) (hL : 2 ≤ L)
    (hNbound : (N : ℝ) ≤ (t : ℝ) * L ^ (-a)) :
    a * Real.log L / Real.log (q : ℝ) ≤ (m : ℝ) := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hL0 : (0 : ℝ) < L := by linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hqm : (0 : ℝ) < (q : ℝ) ^ m := by positivity
  have hgtR : (t : ℝ) < (N : ℝ) * (q : ℝ) ^ m := by exact_mod_cast hgt
  have hchain : (t : ℝ) < ((t : ℝ) * L ^ (-a)) * (q : ℝ) ^ m := by
    have := mul_le_mul_of_nonneg_right hNbound hqm.le
    linarith
  have hLa : (0 : ℝ) < L ^ a := Real.rpow_pos_of_pos hL0 a
  have hinv : L ^ (-a) = (L ^ a)⁻¹ := by rw [Real.rpow_neg hL0.le]
  rw [hinv] at hchain
  have hkey : L ^ a < (q : ℝ) ^ m := by
    rw [mul_comm (t : ℝ) ((L ^ a)⁻¹), mul_assoc] at hchain
    have h2 : (t : ℝ) * (L ^ a) < (t : ℝ) * (q : ℝ) ^ m := by
      have h3 := mul_lt_mul_of_pos_left hchain hLa
      calc (t : ℝ) * (L ^ a) = (L ^ a) * (t : ℝ) := by ring
        _ < (L ^ a) * ((L ^ a)⁻¹ * ((t : ℝ) * (q : ℝ) ^ m)) := h3
        _ = (t : ℝ) * (q : ℝ) ^ m := by field_simp
    exact lt_of_mul_lt_mul_left (by linarith [h2]) ht0.le
  have hlog : Real.log (L ^ a) < Real.log ((q : ℝ) ^ m) := Real.log_lt_log hLa hkey
  rw [Real.log_rpow hL0, Real.log_pow] at hlog
  rw [div_le_iff₀ hlq]
  linarith

/-- If `N * q ^ (m - 1) ≤ t` (with `N ≥ 1`, `m ≥ 1`), then `m ≤ 1 + log t / log q`, obtained
by dropping the factor `N` and taking logarithms of `q ^ (m - 1) ≤ t`. -/
theorem scaleCount_log_upper {N q t m : ℕ} (hq : 2 ≤ q) (hN : 1 ≤ N) (hm : 1 ≤ m)
    (_ht : 1 ≤ t) (hle : N * q ^ (m - 1) ≤ t) :
    (m : ℝ) ≤ 1 + Real.log (t : ℝ) / Real.log (q : ℝ) := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hpow : q ^ (m - 1) ≤ t := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hle
  have hpowR : ((q : ℝ)) ^ (m - 1) ≤ (t : ℝ) := by exact_mod_cast hpow
  have hqp : (0 : ℝ) < (q : ℝ) ^ (m - 1) := by positivity
  have hlog : Real.log ((q : ℝ) ^ (m - 1)) ≤ Real.log (t : ℝ) := Real.log_le_log hqp hpowR
  rw [Real.log_pow] at hlog
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := hm
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast] at hlog
  have hstep : (m : ℝ) - 1 ≤ Real.log (t : ℝ) / Real.log (q : ℝ) := by
    rw [le_div_iff₀ hlq]
    exact hlog
  linarith


/-- Converts the logarithmic lower bound `A * log L / log q ≤ m` on `m` into a power-law decay
bound on `κ ^ m` for `κ ∈ (0, 1)`: `κ ^ m ≤ L ^ (-(A * (-log κ) / log q))`, by writing both
sides as exponentials and comparing exponents. -/
theorem pow_le_rpow_of_scales {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) {q : ℕ} (hq : 2 ≤ q)
    {A L : ℝ} (hA : 0 < A) (hL : 1 ≤ L) {m : ℕ}
    (hm : A * Real.log L / Real.log (q : ℝ) ≤ (m : ℝ)) :
    κ ^ m ≤ L ^ (-(A * (-Real.log κ) / Real.log (q : ℝ))) := by
  have hq0 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlq : 0 < Real.log (q : ℝ) := Real.log_pos hq0
  have hlL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hlκ : Real.log κ < 0 := Real.log_neg hκ0 hκ1
  have hleft : κ ^ m = Real.exp ((m : ℝ) * Real.log κ) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hright : L ^ (-(A * (-Real.log κ) / Real.log (q : ℝ)))
      = Real.exp ((-(A * (-Real.log κ) / Real.log (q : ℝ))) * Real.log L) := by
    rw [Real.rpow_def_of_pos hL0]
    ring_nf
  rw [hleft, hright, Real.exp_le_exp]
  have hkey : (m : ℝ) * Real.log κ
      ≤ (A * Real.log L / Real.log (q : ℝ)) * Real.log κ :=
    mul_le_mul_of_nonpos_right hm hlκ.le
  have harith : (A * Real.log L / Real.log (q : ℝ)) * Real.log κ
      = (-(A * (-Real.log κ) / Real.log (q : ℝ))) * Real.log L := by
    field_simp
  linarith


end Sandpile
