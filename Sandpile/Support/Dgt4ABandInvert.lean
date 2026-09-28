import Mathlib

/-!
# The inversion step of the summed-profile passage

The inversion step of Step 2 of `thm:dgt4-many-limits` (`sandpile.tex:6233-6241`): the summed
profile `eq:dgt4-band-summed-profile` gives `y_{k,⌊tR_k²⌋}/L_k → t/κ_k`, and
`eq:dgt4-band-scaled-profile` is its reciprocal, `L_kz_{k,⌊tR_k²⌋}^{ϑ_k} → κ_k/t`.

Inverting a uniform approximation is legitimate only away from zero, and here the limit
`t/κ_k` is at least `δ/κ_1` on the band, because `t ≥ δ` and the exponents are bounded above.
That is the whole content of the passage, and it is stated for arbitrary families of
functions on an arbitrary set: `eventually_abs_inv_sub_le` inverts a uniform approximation
bounded away from zero, and `eventually_abs_ratio_sub_one_le` applies it to the index shift
`eq:dgt4-band-index-shift`, where a step bound small compared with `L_k` against a lower
bound of order `L_k` forces consecutive values of the profile to have ratio tending to one.
-/

open Filter Topology

namespace Sandpile.Support

/-- **Inverting a uniform approximation away from zero.**  If `A_k` approximates
`B_k` uniformly on `S`, and `B_k` stays above `b_0 > 0` there, then `A_k⁻¹`
approximates `B_k⁻¹` uniformly on `S`. -/
theorem eventually_abs_inv_sub_le
    (A B : ℕ → ℝ → ℝ) (S : Set ℝ) (b0 : ℝ) (hb0 : 0 < b0)
    (hB : ∀ᶠ k : ℕ in atTop, ∀ t ∈ S, b0 ≤ B k t)
    (hA : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ k : ℕ in atTop, ∀ t ∈ S, |A k t - B k t| ≤ ζ) :
    ∀ ζ : ℝ, 0 < ζ → ∀ᶠ k : ℕ in atTop, ∀ t ∈ S, |(A k t)⁻¹ - (B k t)⁻¹| ≤ ζ := by
  intro ζ hζ
  have hb2 : (0 : ℝ) < b0 ^ 2 / 2 := by
    have := pow_pos hb0 2
    linarith
  set ε : ℝ := min (b0 / 2) (ζ * b0 ^ 2 / 2) with hε_def
  have hεpos : 0 < ε := by
    refine lt_min (by linarith) ?_
    have := pow_pos hb0 2
    positivity
  filter_upwards [hB, hA ε hεpos] with k hBk hAk
  intro t ht
  have hBt : b0 ≤ B k t := hBk t ht
  have hAt : |A k t - B k t| ≤ ε := hAk t ht
  have hεb : ε ≤ b0 / 2 := min_le_left _ _
  have hεζ : ε ≤ ζ * b0 ^ 2 / 2 := min_le_right _ _
  have hAge : b0 / 2 ≤ A k t := by
    have h1 := (abs_le.mp hAt).1
    linarith
  have hApos : 0 < A k t := lt_of_lt_of_le (by linarith) hAge
  have hBpos : 0 < B k t := lt_of_lt_of_le hb0 hBt
  have hkey : (A k t)⁻¹ - (B k t)⁻¹ = (B k t - A k t) / (A k t * B k t) := by
    field_simp
  rw [hkey, abs_div, abs_of_pos (mul_pos hApos hBpos)]
  have hnum : |B k t - A k t| ≤ ε := by rwa [abs_sub_comm]
  have hden : b0 ^ 2 / 2 ≤ A k t * B k t := by nlinarith
  calc |B k t - A k t| / (A k t * B k t) ≤ ε / (b0 ^ 2 / 2) :=
        div_le_div₀ hεpos.le hnum hb2 hden
    _ ≤ ζ := by
        rw [div_le_iff₀ hb2]
        nlinarith

/-- **The index shift** (`eq:dgt4-band-index-shift`, `sandpile.tex:6237-6245`).
Because `z_{k,n-1}^{ϑ_k}/z_{k,n}^{ϑ_k} = y_{k,n}/y_{k,n-1}`, the index shift is
the statement that consecutive values of the profile have ratio tending to one.
That follows from a step bound small compared with `L_k` and a lower bound of
order `L_k`, which the summed profile supplies on the band. -/
theorem eventually_abs_ratio_sub_one_le
    (u : ℕ → ℕ → ℝ) (L e : ℕ → ℝ) (P : ℕ → ℕ → Prop) (m : ℝ) (hm : 0 < m)
    (hLpos : ∀ᶠ k : ℕ in atTop, 0 < L k)
    (he : Tendsto (fun k : ℕ => e k / L k) atTop (𝓝 0))
    (hlow : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, P k n → m * L k ≤ u k (n - 1))
    (hstep : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, P k n → |u k n - u k (n - 1)| ≤ e k) :
    ∀ ζ : ℝ, 0 < ζ → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, P k n →
      |u k n / u k (n - 1) - 1| ≤ ζ := by
  intro ζ hζ
  have hmζ : 0 < ζ * m := mul_pos hζ hm
  have hsmall : ∀ᶠ k : ℕ in atTop, |e k / L k| ≤ ζ * m := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp he (ζ * m) hmζ
    filter_upwards [eventually_ge_atTop N] with k hk
    have hd := hN k hk
    rw [Real.dist_eq, sub_zero] at hd
    exact hd.le
  filter_upwards [hLpos, hlow, hstep, hsmall] with k hLk hlowk hstepk hsmallk
  intro n hn
  have hlowkn : m * L k ≤ u k (n - 1) := hlowk n hn
  have hupos : 0 < u k (n - 1) := lt_of_lt_of_le (mul_pos hm hLk) hlowkn
  have hrw : u k n / u k (n - 1) - 1 = (u k n - u k (n - 1)) / u k (n - 1) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hupos]
  have hnum : |u k n - u k (n - 1)| ≤ e k := hstepk n hn
  have henn : 0 ≤ e k := le_trans (abs_nonneg _) hnum
  have hbound : |u k n - u k (n - 1)| / u k (n - 1) ≤ e k / (m * L k) :=
    div_le_div₀ henn hnum (mul_pos hm hLk) hlowkn
  refine hbound.trans ?_
  have hek : e k / L k ≤ ζ * m := le_trans (le_abs_self _) hsmallk
  rw [div_le_iff₀ (mul_pos hm hLk)]
  have hkey : e k ≤ ζ * m * L k := by
    rw [div_le_iff₀ hLk] at hek
    exact hek
  nlinarith

end Sandpile.Support
