/-
Integrating a deterministic increment bound.

The upper bounds of `ssec:d5-height-upper` pass from a bound on
`E u_{t+1}(0) - E u_t(0)` to a bound on `E u_t(0)` itself.  The crude step
`eq:dgt4-crude-log-upper` of `sandpile.tex:4479-4499` is the case treated here:
increments at most `C e^{-c a_n}` force logarithmic growth.  The mechanism is
that `b_n := e^{c a_n}` has increments bounded by a constant, so `b_n` is at
most linear and `a_n` at most logarithmic.

The opposite direction is the integration step of `prop:dgt4-height-lower-stretched`
and of `thm:dgt4-height-lower` (`sandpile.tex:4331-4336`): increments at least
`c e^{-C (a_n+1)^β}` force growth at least `(log t)^{1/β}`.  There the argument
is by contradiction and needs no asymptotics: summing the increments over the
last `t/2` steps gives `a_t e^{C(a_t+1)^β} ≥ c t / 2`, while
`a_t < c' (log t)^{1/β}` with `C 2^β c'^β ≤ 1/2` makes the left side at most
`K₀ t^{3/4}`, using `log x ≤ (4/β) x^{β/4}`.
-/
import Mathlib

open Real

namespace Sandpile

/-- `e^u - 1 ≤ u e^u`, the tangent-line bound read at the other end point. -/
theorem exp_sub_one_le_mul_exp (u : ℝ) : Real.exp u - 1 ≤ u * Real.exp u := by
  have h : -u + 1 ≤ Real.exp (-u) := Real.add_one_le_exp (-u)
  have hmul : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hpos : (0 : ℝ) < Real.exp u := Real.exp_pos u
  nlinarith [mul_le_mul_of_nonneg_right h hpos.le]

/-- **Integrating a deterministic increment bound.**  A nondecreasing sequence
starting at zero whose increments are at most `C e^{-c a_n}` grows at most
logarithmically (`eq:dgt4-crude-log-upper`). -/
theorem exists_log_upper_of_increment (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (a : ℕ → ℝ) (h0 : a 0 = 0) (hmono : Monotone a)
    (hstep : ∀ n : ℕ, a (n + 1) - a n ≤ C * Real.exp (-(c * a n))) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ n : ℕ, a n ≤ C' * Real.log ((n : ℝ) + 2) := by
  set K : ℝ := c * C * Real.exp (c * C) with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hnn : ∀ n : ℕ, 0 ≤ a n := fun n => by rw [← h0]; exact hmono (Nat.zero_le n)
  have hb : ∀ n : ℕ, Real.exp (c * a n) ≤ 1 + K * (n : ℝ) := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      set E : ℝ := Real.exp (c * a n) with hEdef
      have hE0 : (0 : ℝ) < E := Real.exp_pos _
      have hE1 : (1 : ℝ) ≤ E := Real.one_le_exp (by have := hnn n; positivity)
      have hΔ0 : 0 ≤ a (n + 1) - a n := by
        have := hmono (Nat.le_succ n); linarith
      have hΔ : a (n + 1) - a n ≤ C * E⁻¹ := by
        have h := hstep n
        rwa [Real.exp_neg, ← hEdef] at h
      have hcΔ : c * (a (n + 1) - a n) ≤ c * C * E⁻¹ := by
        have := mul_le_mul_of_nonneg_left hΔ hc.le
        linarith [this]
      have hcΔC : c * (a (n + 1) - a n) ≤ c * C := by
        have hinv : E⁻¹ ≤ 1 := by
          rw [inv_le_one₀ hE0]; exact hE1
        nlinarith [hcΔ, mul_pos hc hC]
      have hsplit : Real.exp (c * a (n + 1)) = E * Real.exp (c * (a (n + 1) - a n)) := by
        rw [hEdef, ← Real.exp_add]
        congr 1
        ring
      have hkey : Real.exp (c * a (n + 1)) - E ≤ K := by
        rw [hsplit]
        have hstep1 : Real.exp (c * (a (n + 1) - a n)) - 1
            ≤ c * (a (n + 1) - a n) * Real.exp (c * (a (n + 1) - a n)) :=
          exp_sub_one_le_mul_exp _
        have hstep2 : c * (a (n + 1) - a n) * Real.exp (c * (a (n + 1) - a n))
            ≤ c * C * E⁻¹ * Real.exp (c * C) := by
          refine mul_le_mul hcΔ (Real.exp_le_exp.mpr hcΔC) (Real.exp_pos _).le ?_
          positivity
        have hE : E * (Real.exp (c * (a (n + 1) - a n)) - 1) ≤ E * (c * C * E⁻¹ * Real.exp (c * C)) :=
          mul_le_mul_of_nonneg_left (le_trans hstep1 hstep2) hE0.le
        have hcancel : E * (c * C * E⁻¹ * Real.exp (c * C)) = K := by
          rw [hKdef]; field_simp
        nlinarith [hE, hcancel]
      have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      calc Real.exp (c * a (n + 1)) ≤ E + K := by linarith
        _ ≤ 1 + K * (n : ℝ) + K := by linarith
        _ = 1 + K * ((n : ℝ) + 1) := by ring
        _ = 1 + K * ((n + 1 : ℕ) : ℝ) := by rw [hcast]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : (0 : ℝ) ≤ Real.log (1 + K) := Real.log_nonneg (by linarith)
  refine ⟨(Real.log (1 + K) / Real.log 2 + 1) / c, by positivity, fun n => ?_⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hKn : (0 : ℝ) ≤ K * (n : ℝ) := mul_nonneg hK0 hn0
  have hlin : (1 : ℝ) + K * (n : ℝ) ≤ (1 + K) * ((n : ℝ) + 2) := by nlinarith
  have hstep3 : c * a n ≤ Real.log (1 + K * (n : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos (c * a n)) (hb n)
    rwa [Real.log_exp] at h
  have hstep4 : Real.log (1 + K * (n : ℝ)) ≤ Real.log (1 + K) + Real.log ((n : ℝ) + 2) := by
    rw [← Real.log_mul (ne_of_gt (by linarith : (0:ℝ) < 1 + K))
      (ne_of_gt (by linarith : (0:ℝ) < (n : ℝ) + 2))]
    exact Real.log_le_log (by linarith) hlin
  have hL : Real.log 2 ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hfin : Real.log (1 + K) ≤ Real.log (1 + K) / Real.log 2 * Real.log ((n : ℝ) + 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith [hstep3, hstep4, hfin]


/-- `log x ≤ (4/β) x^{β/4}` for `x ≥ 1`, a scale-free form of `log x ≤ x - 1`. -/
theorem log_le_rpow_div (β : ℝ) (hβ : 0 < β) (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ≤ 4 / β * x ^ (β / 4) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hpow : (0 : ℝ) < x ^ (β / 4) := Real.rpow_pos_of_pos hx0 _
  have h := Real.log_le_sub_one_of_pos hpow
  rw [Real.log_rpow hx0] at h
  have h2 : β / 4 * Real.log x ≤ x ^ (β / 4) := by linarith
  have hb4 : (0 : ℝ) < β / 4 := by positivity
  have hfin : Real.log x ≤ x ^ (β / 4) / (β / 4) := by
    rw [le_div_iff₀ hb4]; linarith
  have heq : x ^ (β / 4) / (β / 4) = 4 / β * x ^ (β / 4) := by field_simp
  linarith [heq ▸ hfin]

/-- Hence `(log x)^{1/β} ≤ (4/β)^{1/β} x^{1/4}`. -/
theorem log_rpow_inv_le (β : ℝ) (hβ : 0 < β) (x : ℝ) (hx : 1 ≤ x) :
    (Real.log x) ^ (1 / β) ≤ (4 / β) ^ (1 / β) * x ^ ((1 : ℝ) / 4) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hβ4 : (0 : ℝ) < 4 / β := by positivity
  have hstep : (Real.log x) ^ (1 / β) ≤ (4 / β * x ^ (β / 4)) ^ (1 / β) :=
    Real.rpow_le_rpow hlog (log_le_rpow_div β hβ x hx) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  rw [Real.mul_rpow hβ4.le (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le]
  congr 2
  field_simp


/-- **Integrating a stretched-exponential increment bound from below, with an
explicit threshold.**  The constants and the time from which the bound holds are
written out, so that they do not depend on the sequence beyond the index `N`
past which it exceeds `max M 1`. -/
theorem log_lower_of_increment_explicit (c C M β : ℝ) (hc : 0 < c) (hC : 0 < C) (hβ : 0 < β)
    (a : ℕ → ℝ) (hmono : Monotone a) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → max M 1 ≤ a n)
    (hstep : ∀ n : ℕ, M ≤ a n → c * Real.exp (-(C * (a n + 1) ^ β)) ≤ a (n + 1) - a n) :
    ∀ t : ℕ, max (2 * N + 3) (⌈(2 * ((4 / β) ^ (1 / β)) / c) ^ 4⌉₊ + 1) ≤ t →
      min 1 ((1 / (2 * C * 2 ^ β)) ^ (1 / β)) * (Real.log t) ^ (1 / β) ≤ a t := by
  set K₀ : ℝ := (4 / β) ^ (1 / β) with hK₀def
  have hK₀ : 0 < K₀ := Real.rpow_pos_of_pos (by positivity) _
  set c' : ℝ := min 1 ((1 / (2 * C * 2 ^ β)) ^ (1 / β)) with hc'def
  have hc'0 : 0 < c' := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have hc'1 : c' ≤ 1 := min_le_left _ _
  have hc'β : C * 2 ^ β * c' ^ β ≤ 1 / 2 := by
    have h1 : c' ^ β ≤ ((1 / (2 * C * 2 ^ β)) ^ (1 / β)) ^ β :=
      Real.rpow_le_rpow hc'0.le (min_le_right _ _) hβ.le
    have h2 : ((1 / (2 * C * 2 ^ β)) ^ (1 / β) : ℝ) ^ β = 1 / (2 * C * 2 ^ β) := by
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt hβ), Real.rpow_one]
    rw [h2] at h1
    have h3 : (0 : ℝ) < 2 ^ β := Real.rpow_pos_of_pos (by norm_num) _
    have h4 : (0 : ℝ) < C * 2 ^ β := by positivity
    calc C * 2 ^ β * c' ^ β ≤ C * 2 ^ β * (1 / (2 * C * 2 ^ β)) :=
          mul_le_mul_of_nonneg_left h1 h4.le
      _ = 1 / 2 := by field_simp
  have hNM : ∀ n : ℕ, N ≤ n → M ≤ a n := fun n hn => le_trans (le_max_left _ _) (hN n hn)
  have hN1 : ∀ n : ℕ, N ≤ n → (1 : ℝ) ≤ a n := fun n hn => le_trans (le_max_right _ _) (hN n hn)
  show ∀ t : ℕ, max (2 * N + 3) (⌈(2 * K₀ / c) ^ 4⌉₊ + 1) ≤ t →
      c' * (Real.log t) ^ (1 / β) ≤ a t
  intro t ht
  have ht2N : 2 * N + 3 ≤ t := le_trans (le_max_left _ _) ht
  have htbig : ⌈(2 * K₀ / c) ^ 4⌉₊ + 1 ≤ t := le_trans (le_max_right _ _) ht
  have hNt : N ≤ t := by omega
  have ht0 : (0 : ℝ) < (t : ℝ) := by
    have : 0 < t := by omega
    exact_mod_cast this
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by
    have : 1 ≤ t := by omega
    exact_mod_cast this
  have hut : (1 : ℝ) ≤ a t := hN1 t hNt
  -- the telescoped lower bound on the increment sum
  have htel : ∀ k : ℕ, N ≤ k → k ≤ t →
      ((k : ℝ) - (N : ℝ)) * (c * Real.exp (-(C * (a t + 1) ^ β))) ≤ a k - a N := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; simp
    | succ k hk ih =>
      intro hkt
      have hkt' : k ≤ t := by omega
      have hprev := ih hkt'
      have hak : M ≤ a k := hNM k hk
      have hmonoexp : Real.exp (-(C * (a t + 1) ^ β)) ≤ Real.exp (-(C * (a k + 1) ^ β)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (a k + 1) ^ β ≤ (a t + 1) ^ β := by
          refine Real.rpow_le_rpow (by linarith [hN1 k hk]) ?_ hβ.le
          have := hmono hkt'
          linarith
        nlinarith
      have hone : c * Real.exp (-(C * (a t + 1) ^ β)) ≤ a (k + 1) - a k :=
        le_trans (mul_le_mul_of_nonneg_left hmonoexp hc.le) (hstep k hak)
      have hcast : ((k + 1 : ℕ) : ℝ) - (N : ℝ) = ((k : ℝ) - (N : ℝ)) + 1 := by push_cast; ring
      rw [hcast, add_mul, one_mul]
      linarith
  have hmain := htel t hNt le_rfl
  have haN0 : (0 : ℝ) ≤ a N := le_trans zero_le_one (hN1 N le_rfl)
  have hhalf : (t : ℝ) / 2 ≤ (t : ℝ) - (N : ℝ) := by
    have : (2 : ℝ) * (N : ℝ) + 3 ≤ (t : ℝ) := by exact_mod_cast ht2N
    linarith
  have hexp0 : (0 : ℝ) < Real.exp (-(C * (a t + 1) ^ β)) := Real.exp_pos _
  have hlow : (t : ℝ) / 2 * (c * Real.exp (-(C * (a t + 1) ^ β))) ≤ a t := by
    have := mul_le_mul_of_nonneg_right hhalf (by positivity : (0:ℝ) ≤ c * Real.exp (-(C * (a t + 1) ^ β)))
    linarith
  by_contra hcon
  simp only [not_le] at hcon
  -- the contradiction
  have hlogt : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht1
  have hupow : (a t) ^ β < c' ^ β * Real.log t := by
    have h1 : (a t) ^ β < (c' * (Real.log t) ^ (1 / β)) ^ β := by
      refine Real.rpow_lt_rpow (by linarith) hcon hβ
    rw [Real.mul_rpow hc'0.le (Real.rpow_nonneg hlogt _), ← Real.rpow_mul hlogt,
      one_div_mul_cancel (ne_of_gt hβ), Real.rpow_one] at h1
    exact h1
  have h2β : (0 : ℝ) < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
  have hplus : (a t + 1) ^ β ≤ 2 ^ β * (a t) ^ β := by
    have h1 : (a t + 1) ^ β ≤ (2 * a t) ^ β :=
      Real.rpow_le_rpow (by linarith) (by linarith) hβ.le
    rwa [Real.mul_rpow (by norm_num) (by linarith)] at h1
  have hC2 : C * (a t + 1) ^ β ≤ 1 / 2 * Real.log t := by
    have h1 : C * (a t + 1) ^ β ≤ C * (2 ^ β * (a t) ^ β) :=
      mul_le_mul_of_nonneg_left hplus hC.le
    have h2 : C * (2 ^ β * (a t) ^ β) ≤ C * 2 ^ β * (c' ^ β * Real.log t) := by
      have := mul_le_mul_of_nonneg_left hupow.le (by positivity : (0:ℝ) ≤ C * 2 ^ β)
      nlinarith [this]
    nlinarith [mul_le_mul_of_nonneg_right hc'β hlogt]
  have hsqrt : Real.exp (C * (a t + 1) ^ β) ≤ (t : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos ht0]
    exact Real.exp_le_exp.mpr (by linarith)
  have hu4 : a t ≤ K₀ * (t : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : a t ≤ (Real.log t) ^ (1 / β) := by
      have := hcon
      nlinarith [Real.rpow_nonneg hlogt (1/β)]
    exact le_trans h1 (log_rpow_inv_le β hβ (t : ℝ) ht1)
  -- turn the lower bound into a product bound
  have hprod : (t : ℝ) / 2 * c ≤ a t * Real.exp (C * (a t + 1) ^ β) := by
    have hinv : Real.exp (-(C * (a t + 1) ^ β)) = (Real.exp (C * (a t + 1) ^ β))⁻¹ := by
      rw [← Real.exp_neg]
    have hE : (0 : ℝ) < Real.exp (C * (a t + 1) ^ β) := Real.exp_pos _
    rw [hinv] at hlow
    have h := mul_le_mul_of_nonneg_right hlow hE.le
    have hcancel : (t : ℝ) / 2 * (c * (Real.exp (C * (a t + 1) ^ β))⁻¹) *
        Real.exp (C * (a t + 1) ^ β) = (t : ℝ) / 2 * c := by
      field_simp
    linarith [hcancel ▸ h]
  set v : ℝ := (t : ℝ) ^ ((1 : ℝ) / 4) with hvdef
  have hv0 : (0 : ℝ) < v := Real.rpow_pos_of_pos ht0 _
  have hv4 : v ^ 4 = (t : ℝ) := by
    rw [hvdef, ← Real.rpow_natCast ((t : ℝ) ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul ht0.le]
    norm_num
  have hv2 : v ^ 2 = (t : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [hvdef, ← Real.rpow_natCast ((t : ℝ) ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul ht0.le]
    norm_num
  have hchain : (t : ℝ) / 2 * c ≤ K₀ * v ^ 3 := by
    have h1 : a t * Real.exp (C * (a t + 1) ^ β) ≤ (K₀ * v) * (t : ℝ) ^ ((1:ℝ)/2) := by
      refine mul_le_mul hu4 hsqrt (Real.exp_pos _).le (by positivity)
    have h2 : (K₀ * v) * (t : ℝ) ^ ((1:ℝ)/2) = K₀ * v ^ 3 := by
      rw [← hv2]; ring
    linarith [hprod, h1, h2 ▸ h1]
  have hvle : v ≤ 2 * K₀ / c := by
    rw [← hv4] at hchain
    have hv3 : (0 : ℝ) < v ^ 3 := by positivity
    rw [le_div_iff₀ hc]
    nlinarith [hchain, hv3, hv0]
  have hcontra : (t : ℝ) ≤ (2 * K₀ / c) ^ 4 := by
    rw [← hv4]
    exact pow_le_pow_left₀ hv0.le hvle 4
  have hbig : ((2 * K₀ / c) ^ 4 : ℝ) < (t : ℝ) := by
    have h1 : ((2 * K₀ / c) ^ 4 : ℝ) ≤ (⌈(2 * K₀ / c) ^ 4⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(2 * K₀ / c) ^ 4⌉₊ : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast htbig
    linarith
  linarith


/-- **Integrating a stretched-exponential increment bound from below.** -/
theorem exists_log_lower_of_increment (c C M β : ℝ) (hc : 0 < c) (hC : 0 < C) (hβ : 0 < β)
    (a : ℕ → ℝ) (hmono : Monotone a)
    (hunb : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hstep : ∀ n : ℕ, M ≤ a n → c * Real.exp (-(C * (a n + 1) ^ β)) ≤ a (n + 1) - a n) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ t : ℕ in Filter.atTop,
      c' * (Real.log t) ^ (1 / β) ≤ a t := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hunb.eventually_ge_atTop (max M 1))
  refine ⟨min 1 ((1 / (2 * C * 2 ^ β)) ^ (1 / β)),
    lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _),
    Filter.eventually_atTop.mpr ⟨max (2 * N + 3) (⌈(2 * ((4 / β) ^ (1 / β)) / c) ^ 4⌉₊ + 1),
      fun t ht => ?_⟩⟩
  exact log_lower_of_increment_explicit c C M β hc hC hβ a hmono N hN hstep t ht

/-- **A positive increment forces divergence.**  If a nondecreasing sequence from a
nonnegative start has increments at least `f` of its current value, with `f`
positive and nonincreasing on the nonnegative reals, then the sequence tends to
infinity.  No rate is needed: below any fixed level the increment is bounded
below by a fixed positive number. -/
theorem tendsto_atTop_of_increment (a : ℕ → ℝ) (ha0 : 0 ≤ a 0) (hmono : Monotone a)
    (f : ℝ → ℝ) (hfpos : ∀ x, 0 < f x) (hfanti : ∀ x y : ℝ, 0 ≤ x → x ≤ y → f y ≤ f x)
    (hstep : ∀ n : ℕ, f (a n) ≤ a (n + 1) - a n) :
    Filter.Tendsto a Filter.atTop Filter.atTop := by
  have han : ∀ n, 0 ≤ a n := fun n => le_trans ha0 (hmono (Nat.zero_le n))
  refine Filter.tendsto_atTop_atTop.mpr fun L => ?_
  set L' : ℝ := max L 0 with hL'
  have hL'0 : 0 ≤ L' := le_max_right _ _
  set δ : ℝ := f L' with hδ
  have hδ0 : 0 < δ := hfpos L'
  have hind : ∀ n : ℕ, min L' ((n : ℝ) * δ) ≤ a n := by
    intro n
    induction n with
    | zero => simpa using le_trans (min_le_right _ _) (by simpa using ha0)
    | succ k ih =>
        rcases le_or_gt L' (a k) with hk | hk
        · exact le_trans (min_le_left _ _) (le_trans hk (hmono (Nat.le_succ k)))
        · have hmin : min L' ((k : ℝ) * δ) = (k : ℝ) * δ := by
            rcases min_cases L' ((k : ℝ) * δ) with ⟨he, -⟩ | ⟨he, -⟩
            · exact absurd (he ▸ ih) (not_le.mpr hk)
            · exact he
          have hstepk : δ ≤ a (k + 1) - a k := by
            refine le_trans (hfanti (a k) L' (han k) hk.le) (hstep k)
          have hkd : (k : ℝ) * δ ≤ a k := hmin ▸ ih
          have : ((k : ℕ) + 1 : ℝ) * δ ≤ a (k + 1) := by
            nlinarith
          refine le_trans (min_le_right _ _) ?_
          push_cast at this ⊢
          linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (L' / δ)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : L' ≤ (N : ℝ) * δ := by
    rw [div_le_iff₀ hδ0] at hN
    linarith
  have h2 : min L' ((N : ℝ) * δ) = L' := min_eq_left h1
  have h3 : L' ≤ a N := h2 ▸ hind N
  exact le_trans (le_max_left L 0) (le_trans h3 (hmono hn))

/-- **A uniform increment below a level forces the level to be reached.**  If a
nondecreasing sequence from a nonnegative start gains at least `δ` at every step
at which it is below `L`, then after `n` steps it is at least the smaller of `L`
and `n δ`. -/
theorem min_le_of_increment (a : ℕ → ℝ) (ha0 : 0 ≤ a 0) (hmono : Monotone a) (L δ : ℝ)
    (_hδ : 0 < δ) (hstep : ∀ n : ℕ, a n < L → δ ≤ a (n + 1) - a n) :
    ∀ n : ℕ, min L ((n : ℝ) * δ) ≤ a n := by
  intro n
  induction n with
  | zero => simpa using le_trans (min_le_right _ _) (by simpa using ha0)
  | succ k ih =>
      rcases le_or_gt L (a k) with hk | hk
      · exact le_trans (min_le_left _ _) (le_trans hk (hmono (Nat.le_succ k)))
      · have hmin : min L ((k : ℝ) * δ) = (k : ℝ) * δ := by
          rcases min_cases L ((k : ℝ) * δ) with ⟨he, -⟩ | ⟨he, -⟩
          · exact absurd (he ▸ ih) (not_le.mpr hk)
          · exact he
        have hkd : (k : ℝ) * δ ≤ a k := hmin ▸ ih
        have hgain := hstep k hk
        refine le_trans (min_le_right _ _) ?_
        push_cast
        linarith

/-- The index past which a sequence with a uniform increment below one has
passed one. -/
theorem one_le_of_increment (a : ℕ → ℝ) (ha0 : 0 ≤ a 0) (hmono : Monotone a) (δ : ℝ)
    (hδ : 0 < δ) (hstep : ∀ n : ℕ, a n < 1 → δ ≤ a (n + 1) - a n) :
    ∀ n : ℕ, ⌈1 / δ⌉₊ ≤ n → (1 : ℝ) ≤ a n := by
  intro n hn
  have h1 : (1 : ℝ) / δ ≤ (⌈(1 : ℝ) / δ⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((⌈(1 : ℝ) / δ⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h3 : (1 : ℝ) ≤ (n : ℝ) * δ := by
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  have := min_le_of_increment a ha0 hmono 1 δ hδ hstep n
  rw [min_eq_left h3] at this
  exact this

/-- **Integrating a stretched-exponential increment bound from above.**  A
nondecreasing sequence starting at zero whose increments are at most
`C e^{-c a_n^β}` grows at most like `(log n)^{1/β}`.  This is
`eq:dgt4-reduction-increment` integrated, in place of the paper's
`τ_R` argument. -/
theorem exists_log_upper_of_stretched_increment (C c β : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hβ : 0 < β) (a : ℕ → ℝ) (h0 : a 0 = 0) (hmono : Monotone a)
    (hstep : ∀ n : ℕ, a (n + 1) - a n ≤ C * Real.exp (-(c * a n ^ β))) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ n : ℕ, a n ≤ C' * (Real.log ((n : ℝ) + 2)) ^ (1 / β) := by
  classical
  have hnn : ∀ n : ℕ, 0 ≤ a n := fun n => by rw [← h0]; exact hmono (Nat.zero_le n)
  have hstepC : ∀ n : ℕ, a (n + 1) - a n ≤ C := by
    intro n
    refine le_trans (hstep n) ?_
    have h1 : Real.exp (-(c * a n ^ β)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ a n ^ β := Real.rpow_nonneg (hnn n) _
      nlinarith
    nlinarith
  have htel : ∀ n : ℕ, ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n := by
    intro n
    induction n with
    | zero => simpa using h0.symm
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  set B : ℝ := max 1 (2 * C) with hBdef
  have hB1 : (1 : ℝ) ≤ B := le_max_left _ _
  have hB2 : 2 * C ≤ B := le_max_right _ _
  set A : ℝ := 1 + Real.log (2 * C + 1) / Real.log 2 with hAdef
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hA1 : (1 : ℝ) ≤ A := by
    have : 0 ≤ Real.log (2 * C + 1) := Real.log_nonneg (by linarith)
    rw [hAdef]
    have : 0 ≤ Real.log (2 * C + 1) / Real.log 2 := by positivity
    linarith
  -- the core estimate
  have hcore : ∀ N : ℕ, B ≤ a N / 2 → c * (a N / 2) ^ β ≤ Real.log (2 * (N : ℝ) * C) := by
    intro N hBR
    set R : ℝ := a N / 2 with hRdef
    have hR1 : (1 : ℝ) ≤ R := le_trans hB1 hBR
    have hR2C : 2 * C ≤ R := le_trans hB2 hBR
    have hRle : R ≤ a N := by rw [hRdef]; linarith [hnn N]
    have hex : ∃ n : ℕ, R ≤ a n := ⟨N, hRle⟩
    set τ : ℕ := Nat.find hex with hτdef
    have hτspec : R ≤ a τ := Nat.find_spec hex
    have hτN : τ ≤ N := Nat.find_min' hex hRle
    have hτ0 : τ ≠ 0 := by
      intro h
      rw [h, h0] at hτspec
      linarith
    obtain ⟨p, hp⟩ : ∃ p : ℕ, τ = p + 1 := ⟨τ - 1, by omega⟩
    have hpτ : a p < R := by
      have := Nat.find_min hex (m := p) (by omega)
      linarith [not_le.mp this]
    have hτup : a τ < R + C := by
      have := hstepC p
      rw [hp]
      linarith
    -- the increments past τ
    have hsmall : ∀ n : ℕ, τ ≤ n → a (n + 1) - a n ≤ C * Real.exp (-(c * R ^ β)) := by
      intro n hn
      refine le_trans (hstep n) ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
      have hR0 : (0 : ℝ) ≤ R := by linarith
      have : R ^ β ≤ a n ^ β :=
        Real.rpow_le_rpow hR0 (le_trans hτspec (hmono hn)) hβ.le
      nlinarith
    have hsum : a N - a τ ≤ ((N : ℝ) - (τ : ℝ)) * (C * Real.exp (-(c * R ^ β))) := by
      have hIco : ∑ i ∈ Finset.Ico τ N, (a (i + 1) - a i) = a N - a τ := by
        rw [Finset.sum_Ico_eq_sub _ hτN, htel, htel]
      rw [← hIco]
      refine le_trans (Finset.sum_le_sum fun i hi => hsmall i (Finset.mem_Ico.mp hi).1) ?_
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have : ((N - τ : ℕ) : ℝ) ≤ (N : ℝ) - (τ : ℝ) := by
        have : (τ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hτN
        push_cast [Nat.cast_sub hτN]
        linarith
      have hpos : (0 : ℝ) ≤ C * Real.exp (-(c * R ^ β)) := by positivity
      exact mul_le_mul_of_nonneg_right this hpos
    have hτR : (τ : ℝ) ≥ 0 := Nat.cast_nonneg _
    have hkey : R - C ≤ (N : ℝ) * (C * Real.exp (-(c * R ^ β))) := by
      have h2R : 2 * R = a N := by rw [hRdef]; ring
      have hNτ : ((N : ℝ) - (τ : ℝ)) * (C * Real.exp (-(c * R ^ β)))
          ≤ (N : ℝ) * (C * Real.exp (-(c * R ^ β))) := by
        have hpos : (0 : ℝ) ≤ C * Real.exp (-(c * R ^ β)) := by positivity
        nlinarith [hτR, hpos]
      linarith [hsum, hτup, hNτ]
    have hexppos : (0 : ℝ) < Real.exp (c * R ^ β) := Real.exp_pos _
    have hmul : R / 2 * Real.exp (c * R ^ β) ≤ (N : ℝ) * C := by
      have hR2 : R / 2 ≤ R - C := by linarith
      have h1 : (R - C) * Real.exp (c * R ^ β)
          ≤ ((N : ℝ) * (C * Real.exp (-(c * R ^ β)))) * Real.exp (c * R ^ β) :=
        mul_le_mul_of_nonneg_right hkey hexppos.le
      have h2 : Real.exp (-(c * R ^ β)) * Real.exp (c * R ^ β) = 1 := by
        rw [← Real.exp_add]; simp
      have h3 : ((N : ℝ) * (C * Real.exp (-(c * R ^ β)))) * Real.exp (c * R ^ β)
          = (N : ℝ) * C := by
        calc ((N : ℝ) * (C * Real.exp (-(c * R ^ β)))) * Real.exp (c * R ^ β)
            = (N : ℝ) * C * (Real.exp (-(c * R ^ β)) * Real.exp (c * R ^ β)) := by ring
          _ = (N : ℝ) * C := by rw [h2]; ring
      rw [h3] at h1
      have h4 : R / 2 * Real.exp (c * R ^ β) ≤ (R - C) * Real.exp (c * R ^ β) :=
        mul_le_mul_of_nonneg_right hR2 hexppos.le
      linarith
    have hexple : Real.exp (c * R ^ β) ≤ 2 * (N : ℝ) * C := by
      nlinarith [hmul, hexppos, hR1,
        mul_nonneg (show (0 : ℝ) ≤ R - 1 by linarith) hexppos.le]
    have hNCpos : (0 : ℝ) < 2 * (N : ℝ) * C := lt_of_lt_of_le hexppos hexple
    exact (Real.le_log_iff_exp_le hNCpos).mpr hexple
  -- from the core estimate to the conclusion
  refine ⟨max (2 * (A / c) ^ (1 / β)) (2 * B / (Real.log 2) ^ (1 / β)),
    lt_of_lt_of_le (by positivity) (le_max_left _ _), fun N => ?_⟩
  have hlogN : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := by
    refine Real.log_le_log (by norm_num) ?_
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    linarith
  have hlogNpos : (0 : ℝ) < Real.log ((N : ℝ) + 2) := lt_of_lt_of_le hlog2 hlogN
  have hpowpos : (0 : ℝ) < (Real.log ((N : ℝ) + 2)) ^ (1 / β) :=
    Real.rpow_pos_of_pos hlogNpos _
  rcases le_or_gt B (a N / 2) with hcase | hcase
  · have h1 := hcore N hcase
    have hRpos : (0 : ℝ) < a N / 2 := lt_of_lt_of_le (by linarith) hcase
    have hbound : Real.log (2 * (N : ℝ) * C) ≤ A * Real.log ((N : ℝ) + 2) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
      have hle : 2 * (N : ℝ) * C ≤ (2 * C + 1) * ((N : ℝ) + 2) := by nlinarith
      have hN1 : 1 ≤ N := by
        rcases Nat.eq_zero_or_pos N with rfl | hNp
        · rw [h0] at hRpos; norm_num at hRpos
        · exact hNp
      have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
      have hpos : (0 : ℝ) < 2 * (N : ℝ) * C := by positivity
      have h2 : Real.log (2 * (N : ℝ) * C) ≤ Real.log ((2 * C + 1) * ((N : ℝ) + 2)) :=
        Real.log_le_log hpos hle
      have h2' : Real.log ((2 * C + 1) * ((N : ℝ) + 2))
          = Real.log (2 * C + 1) + Real.log ((N : ℝ) + 2) :=
        Real.log_mul (by linarith) (by linarith)
      rw [h2'] at h2
      have h3 : Real.log (2 * C + 1) ≤ (A - 1) * Real.log ((N : ℝ) + 2) := by
        rw [hAdef]
        have : Real.log (2 * C + 1) / Real.log 2 * Real.log ((N : ℝ) + 2)
            ≥ Real.log (2 * C + 1) / Real.log 2 * Real.log 2 := by
          have hq : 0 ≤ Real.log (2 * C + 1) / Real.log 2 := by
            have : 0 ≤ Real.log (2 * C + 1) := Real.log_nonneg (by linarith)
            positivity
          exact mul_le_mul_of_nonneg_left hlogN hq
        have heq : Real.log (2 * C + 1) / Real.log 2 * Real.log 2 = Real.log (2 * C + 1) := by
          field_simp
        simp only [add_sub_cancel_left]
        linarith [heq.le, heq.ge]
      linarith
    have hRβ : (a N / 2) ^ β ≤ (A / c) * Real.log ((N : ℝ) + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      nlinarith [h1, hbound]
    have hR : a N / 2 ≤ ((A / c) * Real.log ((N : ℝ) + 2)) ^ (1 / β) := by
      have h4 : ((a N / 2) ^ β) ^ (1 / β) = a N / 2 := by
        rw [← Real.rpow_mul hRpos.le]
        rw [mul_one_div, div_self (ne_of_gt hβ), Real.rpow_one]
      calc a N / 2 = ((a N / 2) ^ β) ^ (1 / β) := h4.symm
        _ ≤ ((A / c) * Real.log ((N : ℝ) + 2)) ^ (1 / β) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hRpos.le _) hRβ (by positivity)
    have hsplit : ((A / c) * Real.log ((N : ℝ) + 2)) ^ (1 / β)
        = (A / c) ^ (1 / β) * (Real.log ((N : ℝ) + 2)) ^ (1 / β) :=
      Real.mul_rpow (by positivity) hlogNpos.le
    rw [hsplit] at hR
    have : a N ≤ 2 * ((A / c) ^ (1 / β) * (Real.log ((N : ℝ) + 2)) ^ (1 / β)) := by linarith
    calc a N ≤ 2 * ((A / c) ^ (1 / β) * (Real.log ((N : ℝ) + 2)) ^ (1 / β)) := this
      _ = (2 * (A / c) ^ (1 / β)) * (Real.log ((N : ℝ) + 2)) ^ (1 / β) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hpowpos.le
  · have hsmallN : a N ≤ 2 * B := by linarith
    have hpow2 : (Real.log 2) ^ (1 / β) ≤ (Real.log ((N : ℝ) + 2)) ^ (1 / β) :=
      Real.rpow_le_rpow hlog2.le hlogN (by positivity)
    have hpow2pos : (0 : ℝ) < (Real.log 2) ^ (1 / β) := Real.rpow_pos_of_pos hlog2 _
    have hBpos : (0 : ℝ) < 2 * B := by linarith
    calc a N ≤ 2 * B := hsmallN
      _ = (2 * B / (Real.log 2) ^ (1 / β)) * (Real.log 2) ^ (1 / β) := by
          field_simp
      _ ≤ (2 * B / (Real.log 2) ^ (1 / β)) * (Real.log ((N : ℝ) + 2)) ^ (1 / β) :=
          mul_le_mul_of_nonneg_left hpow2 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hpowpos.le

end Sandpile
