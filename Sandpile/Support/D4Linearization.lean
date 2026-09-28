import LatticeProb.Walk.ExteriorDirichlet
import Sandpile.Support.RefinedIncrement
import Sandpile.Support.D4Difference

/-!
# Backward Decomposition of the Pointwise Linearization

The backward decomposition of `prop:d4-pointwise-linearization`.

`sandpile.tex:3078-3098` writes, for `2 ≤ t - n < t`,

    u_t - E u_t(0) - V_t = P^n (u_{t-n} - E u_{t-n}(0) - V_{t-n})
                            + ∑_{k<n} P^k (r_{t-1-k} - E r_{t-1-k}(0)) ,

where `r_s = (-ζ - P u_s)_+`. The identity is the recursion `u_{s+1} =
ζ + P u_s + r_s`, which is `a₊ = a + (-a)₊` applied to `a = ζ + P u_s`,
iterated backwards against `V_t = ∑_{k<n} P^k ζ + P^n V_{t-n}`. This file
carries that algebra; the two tails it is fed to are in the files that follow.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- `r_s := (-ζ - P u_s)_+` of `sandpile.tex:3079-3081`. -/
noncomputable def reflectionTerm (ζ : Site d → ℝ) (s : ℕ) (x : Site d) : ℝ :=
  max 0 (-(ζ x) - avg (odometerOf ζ s) x)

/-- `reflectionTerm` is nonnegative, since it is defined as a maximum with `0`. -/
theorem reflectionTerm_nonneg (ζ : Site d → ℝ) (s : ℕ) (x : Site d) :
    0 ≤ reflectionTerm ζ s x := le_max_left _ _

/-- `u_{s+1} = ζ + P u_s + r_s`, from `a₊ = a + (-a)₊`. -/
theorem odometerOf_succ_eq_add_reflection (ζ : Site d → ℝ) (s : ℕ) (x : Site d) :
    odometerOf ζ (s + 1) x = ζ x + avg (odometerOf ζ s) x + reflectionTerm ζ s x := by
  show max 0 (ζ x + avg (odometerOf ζ s) x) = _
  unfold reflectionTerm
  rcases le_total 0 (ζ x + avg (odometerOf ζ s) x) with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- `D_t := u_t - V_t`, the difference decomposed in `eq:d4-proof-two-terms`. -/
noncomputable def diffField (ζ : Site d → ℝ) (t : ℕ) (x : Site d) : ℝ :=
  odometerOf ζ t x - membrane ζ t x

/-- `diffField ζ 0 x = 0`, since both `odometerOf ζ 0 x` and `membrane ζ 0 x` unfold to
`0` at time `0`. -/
theorem diffField_zero (ζ : Site d → ℝ) (x : Site d) : diffField ζ 0 x = 0 := by
  simp [diffField, odometerOf, membrane]

/-- The difference obeys the recursion with the scenery removed:
`D_{s+1} = P D_s + r_s`. -/
theorem diffField_succ (ζ : Site d → ℝ) (s : ℕ) (x : Site d) :
    diffField ζ (s + 1) x = avg (diffField ζ s) x + reflectionTerm ζ s x := by
  have hsub : avg (diffField ζ s) x = avg (odometerOf ζ s) x - avg (membrane ζ s) x :=
    LatticeProb.walkOp_sub (odometerOf ζ s) (membrane ζ s) x
  show odometerOf ζ (s + 1) x - membrane ζ (s + 1) x = _
  rw [odometerOf_succ_eq_add_reflection, hsub]
  show _ - (ζ x + avg (membrane ζ s) x) = _
  ring

/-- **The backward decomposition.**  For `n ≤ t`,
`D_t = P^n D_{t-n} + ∑_{k<n} P^k r_{t-1-k}`. -/
theorem diffField_decomp (ζ : Site d → ℝ) :
    ∀ (n t : ℕ), n ≤ t → ∀ x : Site d,
      diffField ζ t x = (avg^[n] (diffField ζ (t - n))) x +
        ∑ k ∈ Finset.range n, (avg^[k] (reflectionTerm ζ (t - 1 - k))) x := by
  intro n
  induction n with
  | zero => intro t _ x; simp
  | succ n ih =>
      intro t hn x
      have hIH := ih t (by omega) x
      have hidx : t - n = (t - (n + 1)) + 1 := by omega
      have hfun : diffField ζ (t - n)
          = fun y => avg (diffField ζ (t - (n + 1))) y + reflectionTerm ζ (t - (n + 1)) y := by
        funext y
        rw [hidx]
        exact diffField_succ ζ (t - (n + 1)) y
      have hsplit : (avg^[n] (diffField ζ (t - n))) x
          = (avg^[n + 1] (diffField ζ (t - (n + 1)))) x
            + (avg^[n] (reflectionTerm ζ (t - (n + 1)))) x := by
        rw [hfun, avg_iterate_add n (avg (diffField ζ (t - (n + 1))))
          (reflectionTerm ζ (t - (n + 1))) x,
          Function.iterate_succ_apply avg n (diffField ζ (t - (n + 1)))]
      have hlast : t - 1 - n = t - (n + 1) := by omega
      rw [Finset.sum_range_succ, hlast]
      rw [hIH, hsplit]
      ring

end Sandpile
