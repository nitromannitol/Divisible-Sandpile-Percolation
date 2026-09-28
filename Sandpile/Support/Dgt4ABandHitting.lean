import Mathlib

/-!
# The hitting time and profile coordinate of Step 2

The hitting time `τ_k` of Step 2 of `thm:dgt4-many-limits` (`sandpile.tex:6106-6135`). `τ_k` is
the first time the mean height reaches `a_k - (1 - ℓ_1) a_k / 2`. The paper bounds it by summing
the one-step lower bound `E u_{n+1}(0) - E u_n(0) ≥ c ω_k a_k`, which holds before `τ_k`
(`le_of_increments`, `hitting_le`), and bounds the overshoot at `τ_k` by the crude one-step upper
bound `eq:dgt4-one-step-mean-increment` (`hitting_value_le`). Neither step uses anything about
the sandpile, so both are stated here for an arbitrary nondecreasing sequence starting at zero,
and `z_{k,n} ≤ 1/2` is recorded (`bandProfileCoord_le_half_iff`) as the reading of the hitting
condition in the profile coordinate `bandProfileCoord`.
-/

open Filter Topology

noncomputable section

namespace Sandpile.Support

/-- Before the hitting time the sequence grows at least linearly. -/
theorem le_of_increments (u : ℕ → ℝ) (q h : ℝ) (hu0 : u 0 = 0) (hmono : Monotone u)
    (hinc : ∀ n : ℕ, u n < h → q ≤ u (n + 1) - u n) :
    ∀ n : ℕ, u n < h → (n : ℝ) * q ≤ u n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [hu0]
  | succ j ih =>
    intro hn
    have hj : u j < h := lt_of_le_of_lt (hmono (Nat.le_succ j)) hn
    have h1 := ih hj
    have h2 := hinc j hj
    push_cast
    linarith

/-- **The hitting time is at most `h/q + 1`.**  This is the paper's
`τ_k ≤ C/ω_k`. -/
theorem hitting_le (u : ℕ → ℝ) (q h : ℝ) (hq : 0 < q) (hh : 0 ≤ h)
    (hu0 : u 0 = 0) (hmono : Monotone u)
    (hinc : ∀ n : ℕ, u n < h → q ≤ u (n + 1) - u n)
    (hex : ∃ n : ℕ, h ≤ u n) :
    ((Nat.find hex : ℕ) : ℝ) ≤ h / q + 1 := by
  classical
  set t : ℕ := Nat.find hex with ht
  have hqnn : 0 ≤ h / q := div_nonneg hh hq.le
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · rw [h0]
    push_cast
    linarith
  · have hmin : ¬ (h ≤ u (t - 1)) := Nat.find_min hex (by omega)
    have hlt : u (t - 1) < h := lt_of_not_ge hmin
    have hgrow := le_of_increments u q h hu0 hmono hinc (t - 1) hlt
    have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
      have hone : (1 : ℕ) ≤ t := hpos
      push_cast [Nat.cast_sub hone]
      ring
    rw [hcast] at hgrow
    have h1 : ((t : ℝ) - 1) * q < h := lt_of_le_of_lt hgrow hlt
    rw [← lt_div_iff₀ hq] at h1
    linarith

/-- **The value at the hitting time overshoots by at most one step.**  This is
the paper's `z_{k,τ_k} ≥ 1/2 - C/a_k`. -/
theorem hitting_value_le (u : ℕ → ℝ) (h M : ℝ) (hu0 : u 0 = 0) (hh : 0 ≤ h) (hM : 0 ≤ M)
    (hstep : ∀ n : ℕ, u (n + 1) - u n ≤ M)
    (hex : ∃ n : ℕ, h ≤ u n) :
    u (Nat.find hex) ≤ h + M := by
  classical
  set t : ℕ := Nat.find hex with ht
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · rw [h0, hu0]
    linarith
  · have hmin : ¬ (h ≤ u (t - 1)) := Nat.find_min hex (by omega)
    have hlt : u (t - 1) < h := lt_of_not_ge hmin
    have hs := hstep (t - 1)
    have hrw : t - 1 + 1 = t := by omega
    rw [hrw] at hs
    linarith

/-- The value at the hitting time is at least the level. -/
theorem le_hitting_value (u : ℕ → ℝ) (h : ℝ) (hex : ∃ n : ℕ, h ≤ u n) :
    h ≤ u (Nat.find hex) :=
  Nat.find_spec hex

/-- The profile coordinate `z_{k,n} = (a - u_n)/W`. -/
def bandProfileCoord (a W : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ := (a - u n) / W

/-- The profile coordinate starts at `a / W`, since `u` starts at zero. -/
theorem bandProfileCoord_zero (a W : ℝ) (u : ℕ → ℝ) (hu0 : u 0 = 0) :
    bandProfileCoord a W u 0 = a / W := by
  rw [bandProfileCoord, hu0, sub_zero]

/-- The profile coordinate is nonincreasing, because the mean height is
nondecreasing. -/
theorem bandProfileCoord_antitone (a W : ℝ) (hW : 0 < W) (u : ℕ → ℝ) (hmono : Monotone u) :
    Antitone (bandProfileCoord a W u) := by
  intro i j hij
  rw [bandProfileCoord, bandProfileCoord, div_le_div_iff_of_pos_right hW]
  have := hmono hij
  linarith

/-- The hitting condition `u_n ≥ a - W/2` is exactly `z_{k,n} ≤ 1/2`. -/
theorem bandProfileCoord_le_half_iff (a W : ℝ) (hW : 0 < W) (u : ℕ → ℝ) (n : ℕ) :
    bandProfileCoord a W u n ≤ 1 / 2 ↔ a - W / 2 ≤ u n := by
  rw [bandProfileCoord, div_le_iff₀ hW]
  constructor <;> intro h <;> linarith

end Sandpile.Support
