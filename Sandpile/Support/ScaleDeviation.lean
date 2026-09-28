import Sandpile.Support.ScaleThreshold

/-!
# The membrane standard deviation lower bound

The standard deviation of the membrane field from below, and one power identity.
`sandpile.tex:1747-1749` reads the normalized threshold `h/√Var(V_{n_j}(0))` off the lower half of
`eq:Qt-table` and the variance floor of the scenery, which is exactly `membraneSd_lower` here. The
second lemma, `rpow_quarter_mul_sqrt`, is the identity `m^{1/4} · √m = m^{3/4}` that turns the
Berry-Esseen factor and the `ℓ²`-`ℓ³` factor into the paper's `m^{3/4}`.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

/-- The power identity `m^{1/4} · √m = m^{3/4}` that turns the Berry-Esseen factor and the
`ℓ²`-`ℓ³` factor into the paper's `m^{3/4}`. -/
theorem rpow_quarter_mul_sqrt (m : ℕ) :
    (m : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (m : ℝ) = (m : ℝ) ^ ((3 : ℝ) / 4) := by
  have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add' h0 (by norm_num)]
  norm_num

/-- A lower bound on `membraneSd`, the membrane field's standard deviation, from a variance floor
`ν₀ ^ 2 ≤ variance ν` on the one-site law and a lower bound `cQ * n ^ ((4-d)/2) ≤ greenSq d n` on
the Green square sum: this is the normalized-threshold computation of `sandpile.tex:1747-1749`. -/
theorem membraneSd_lower (ν : Measure ℝ) {ν₀ cQ : ℝ} (hν₀ : 0 < ν₀) (hc : 0 < cQ)
    (hvar : ν₀ ^ 2 ≤ variance (id : ℝ → ℝ) ν) {n : ℕ}
    (hQ : cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2)) ≤ greenSq d n) :
    ν₀ * Real.sqrt cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4)) ≤ membraneSd d ν n := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4) := Real.rpow_nonneg hn0 _
  have hlhs : (0 : ℝ) ≤ ν₀ * Real.sqrt cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4)) := by
    positivity
  have hsq : ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4)) ^ 2
      = (n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4)) 2, ← Real.rpow_mul hn0]
    congr 1
    push_cast
    ring
  have hcq : Real.sqrt cQ * Real.sqrt cQ = cQ := Real.mul_self_sqrt hc.le
  have hQ0 : (0 : ℝ) ≤ greenSq d n := greenSq_nonneg d n
  have hVar0 : (0 : ℝ) ≤ variance (id : ℝ → ℝ) ν := le_trans (sq_nonneg ν₀) hvar
  rw [membraneSd, Real.le_sqrt hlhs (by positivity)]
  have hrp : (0 : ℝ) ≤ (n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2) := Real.rpow_nonneg hn0 _
  have hexp : (ν₀ * Real.sqrt cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4))) ^ 2
      = ν₀ ^ 2 * (cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2))) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hc.le, hsq]
    ring
  rw [hexp]
  calc ν₀ ^ 2 * (cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2)))
      ≤ ν₀ ^ 2 * greenSq d n := mul_le_mul_of_nonneg_left hQ (sq_nonneg ν₀)
    _ ≤ variance (id : ℝ → ℝ) ν * greenSq d n := mul_le_mul_of_nonneg_right hvar hQ0

end Sandpile
