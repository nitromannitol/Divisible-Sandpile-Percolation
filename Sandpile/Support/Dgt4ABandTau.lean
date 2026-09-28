import Sandpile.Support.Dgt4ABandHitting

/-!
# Scale, profile coordinate and hitting time for Step 2

The bookkeeping of Step 2 of `thm:dgt4-many-limits` (`sandpile.tex:6085-6135`):
the scale `R_k`, the profile coordinate `z_{k,n}`, and the hitting time `τ_k`.

The paper sets
`R_k^2 = G(0,0)L_k/ω_k`, `z_{k,n} = (a_k - b_n)/((1-ℓ_1)a_k)` with
`b_n = E u_n(0)/G(0,0)`, and `τ_k = inf{n : b_n ≥ a_k - (1-ℓ_1)a_k/2}`, and then
proves `τ_k ≤ C/ω_k`, `τ_k/R_k^2 → 0`, and `1/2 - C/a_k ≤ z_{k,τ_k} ≤ 1/2`.

Every step of that is an assertion about a nondecreasing real sequence starting
at zero, once two inputs are granted: a lower bound `cω_ka_k` on the increments
before the hitting time, and the crude upper bound
`eq:dgt4-one-step-mean-increment` on every increment.  The first of those is
itself an instance of the elementary lower bound
`E(ξ-w)_+ ≥ s·P(ξ > w+s)`, proved here as `integral_posPart_neg_ge`, at
`w = E W_n` and `s = (1-ℓ_1)a_k/8`, so that lemma is proved here too.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

/-! ### The lower bound on the mean overshoot -/

/-- **`E(ξ-w)_+ ≥ s·P(ξ > w+s)`** for `ξ = -z` under `ν`: the mean overshoot
above a level is at least the height above it times the mass that far above.
This is the step that turns the band profile `eq:dgt4-band-profile` into the
increment lower bound `E u_{n+1}(0) - E u_n(0) ≥ cω_ka_k`. -/
theorem integral_posPart_neg_ge (ν : Measure ℝ) [IsFiniteMeasure ν] (w s : ℝ)
    (hint : Integrable (fun z : ℝ => max (-z - w) 0) ν) :
    s * (ν {z : ℝ | w + s < -z}).toReal ≤ ∫ z, max (-z - w) 0 ∂ν := by
  have hset : {z : ℝ | w + s < -z} = Iio (-(w + s)) := by
    ext z
    simp only [mem_setOf_eq, mem_Iio]
    constructor <;> intro h <;> linarith
  have hmeas : MeasurableSet {z : ℝ | w + s < -z} := by
    rw [hset]; exact measurableSet_Iio
  have hind : Integrable
      (Set.indicator {z : ℝ | w + s < -z} (fun _ => s)) ν :=
    (integrable_const s).indicator hmeas
  have hle : ∀ z : ℝ,
      Set.indicator {z : ℝ | w + s < -z} (fun _ => s) z ≤ max (-z - w) 0 := by
    intro z
    by_cases hz : z ∈ {z : ℝ | w + s < -z}
    · rw [Set.indicator_of_mem hz]
      have hz' : w + s < -z := hz
      exact le_max_of_le_left (by linarith)
    · rw [Set.indicator_of_notMem hz]
      exact le_max_right _ _
  have hmono := integral_mono hind hint hle
  rwa [integral_indicator_const s hmeas, smul_eq_mul, mul_comm] at hmono

/-- Before the hitting time the frozen mean level `b_n` is below
`a_k - (1-ℓ_1)a_k/2`, and the random level is within the concentration error of
it, so the expected random level is below `a_k - 3(1-ℓ_1)a_k/8`
(`sandpile.tex:6103-6105`).  The two levels are distinct objects: the passage
from one to the other goes through the error, never through a shift. -/
theorem meanLevel_le_of_before_hitting {l1 : ℝ} (a b : ℕ → ℝ) (k n : ℕ) (EW err : ℝ)
    (hb : b n < a k - (1 - l1) * a k / 2)
    (hEW : |EW - b n| ≤ err) (herr : err ≤ (1 - l1) * a k / 8) :
    EW ≤ a k - 3 * ((1 - l1) * a k) / 8 := by
  have h1 := (abs_le.mp hEW).2
  linarith

/-- **The increment lower bound `E u_{n+1}(0) - E u_n(0) ≥ cω_ka_k`**
(`sandpile.tex:6106-6120`).  On the event `{-ζ(0) > a_k - (1-ℓ_1)a_k/4}`, whose
probability the band profile bounds below by `cω_k`, the overshoot above the
expected random level is at least `(1-ℓ_1)a_k/8`. -/
theorem integral_posPart_neg_ge_band {l1 : ℝ} (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a : ℕ → ℝ) (k : ℕ) (EW p : ℝ)
    (hEW : EW ≤ a k - 3 * ((1 - l1) * a k) / 8)
    (hW : 0 ≤ (1 - l1) * a k)
    (hmass : p ≤ (ν {z : ℝ | a k - (1 - l1) * a k / 4 < -z}).toReal)
    (hint : Integrable (fun z : ℝ => max (-z - EW) 0) ν) :
    p * ((1 - l1) * a k / 8) ≤ ∫ z, max (-z - EW) 0 ∂ν := by
  have hs : (0 : ℝ) ≤ (1 - l1) * a k / 8 := by linarith
  have hsub : {z : ℝ | a k - (1 - l1) * a k / 4 < -z} ⊆
      {z : ℝ | EW + (1 - l1) * a k / 8 < -z} := by
    intro z hz
    have hz' : a k - (1 - l1) * a k / 4 < -z := hz
    have : EW + (1 - l1) * a k / 8 ≤ a k - (1 - l1) * a k / 4 := by linarith
    exact lt_of_le_of_lt this hz'
  have hmono : (ν {z : ℝ | a k - (1 - l1) * a k / 4 < -z}).toReal ≤
      (ν {z : ℝ | EW + (1 - l1) * a k / 8 < -z}).toReal :=
    ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono hsub)
  have hkey := integral_posPart_neg_ge ν EW ((1 - l1) * a k / 8) hint
  have hp : p * ((1 - l1) * a k / 8) ≤
      ((1 - l1) * a k / 8) * (ν {z : ℝ | EW + (1 - l1) * a k / 8 < -z}).toReal := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (le_trans hmass hmono) hs
  linarith

/-! ### The scale and the profile coordinate -/

/-- The scale `R_k^2 = G(0,0)L_k/ω_k` of Step 2. -/
def bandScaleSq (G00 : ℝ) (L ω : ℕ → ℝ) (k : ℕ) : ℝ := G00 * L k / ω k

/-- The scale `R_k` itself. -/
def bandScale (G00 : ℝ) (L ω : ℕ → ℝ) (k : ℕ) : ℝ := Real.sqrt (bandScaleSq G00 L ω k)

/-- `bandScaleSq G00 L ω k` is nonnegative when `G00` and `L k` are nonnegative and `ω k` is
positive. -/
theorem bandScaleSq_nonneg {G00 : ℝ} {L ω : ℕ → ℝ} {k : ℕ} (hG : 0 ≤ G00) (hL : 0 ≤ L k)
    (hω : 0 < ω k) : 0 ≤ bandScaleSq G00 L ω k :=
  div_nonneg (mul_nonneg hG hL) hω.le

/-- `bandScale G00 L ω k` squares back to `bandScaleSq G00 L ω k`, since `bandScale` is
defined as its square root. -/
theorem bandScale_sq {G00 : ℝ} {L ω : ℕ → ℝ} {k : ℕ} (hG : 0 ≤ G00) (hL : 0 ≤ L k)
    (hω : 0 < ω k) : bandScale G00 L ω k ^ 2 = bandScaleSq G00 L ω k :=
  Real.sq_sqrt (bandScaleSq_nonneg hG hL hω)

/-- The scale satisfies the relation `R_k^2ω_k = G(0,0)L_k` that the summation of
the one-step profile is stated against. -/
theorem bandScale_sq_mul {G00 : ℝ} {L ω : ℕ → ℝ} {k : ℕ} (hG : 0 ≤ G00) (hL : 0 ≤ L k)
    (hω : 0 < ω k) : bandScale G00 L ω k ^ 2 * ω k = G00 * L k := by
  rw [bandScale_sq hG hL hω, bandScaleSq, div_mul_cancel₀]
  exact ne_of_gt hω

/-- The profile coordinate `z_{k,n} = (a_k - b_n)/((1-ℓ_1)a_k)`. -/
def bandLevelCoord (l1 : ℝ) (a b : ℕ → ℝ) (k n : ℕ) : ℝ :=
  bandProfileCoord (a k) ((1 - l1) * a k) b n

/-- Unfolds `bandLevelCoord` to its defining ratio `(a k - b n)/((1-l1)*a k)`. -/
theorem bandLevelCoord_eq (l1 : ℝ) (a b : ℕ → ℝ) (k n : ℕ) :
    bandLevelCoord l1 a b k n = (a k - b n) / ((1 - l1) * a k) := rfl

/-- The profile coordinate is nonincreasing in `n`, because the mean height is
nondecreasing. -/
theorem bandLevelCoord_antitone (l1 : ℝ) (a b : ℕ → ℝ) (k : ℕ)
    (hW : 0 < (1 - l1) * a k) (hmono : Monotone b) :
    Antitone (bandLevelCoord l1 a b k) :=
  bandProfileCoord_antitone (a k) ((1 - l1) * a k) hW b hmono

/-- The band level read back from the profile coordinate: the paper's
`a_k - (1-ℓ_1)a_kz_{k,n}` IS the frozen mean level `b_n`.  This is the identity
that lets the integrated profile `eq:dgt4-band-integrated-profile` be evaluated
at `z = z_{k,n}` and read as a statement about `E(ξ - b_n)_+`. -/
theorem level_eq_of_bandLevelCoord {l1 : ℝ} (a b : ℕ → ℝ) (k n : ℕ)
    (hW : (1 - l1) * a k ≠ 0) :
    a k - (1 - l1) * a k * bandLevelCoord l1 a b k n = b n := by
  rw [bandLevelCoord_eq, mul_div_cancel₀ _ hW]
  ring

/-- The one-step decrement of the profile coordinate is the one-step increment
of the frozen mean level, divided by the width of the band. -/
theorem bandLevelCoord_sub_succ {l1 : ℝ} (a b : ℕ → ℝ) (k n : ℕ) :
    bandLevelCoord l1 a b k n - bandLevelCoord l1 a b k (n + 1)
      = (b (n + 1) - b n) / ((1 - l1) * a k) := by
  rw [bandLevelCoord_eq, bandLevelCoord_eq, div_sub_div_same]
  ring_nf

/-! ### The hitting time -/

/-- The level `a_k - (1-ℓ_1)a_k/2` is reached, because the mean height diverges. -/
theorem bandHitting_exists (h : ℝ) (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) :
    ∃ n : ℕ, h ≤ b n :=
  (hb.eventually_ge_atTop h).exists

/-- **`τ_k ≤ C/ω_k`** (`sandpile.tex:6122-6127`).  Before the hitting time the
mean height grows by at least `cω_ka_k` at every step, so the hitting time is at
most the level divided by that, plus one; the level is at most `a_k`, and
`ω_k ≤ 1`, so the bound is `(1/c + 1)/ω_k`. -/
theorem bandHittingTime_le {l1 c : ℝ} (hl10 : 0 ≤ l1) (hl11 : l1 ≤ 1) (hc : 0 < c)
    (a ω b : ℕ → ℝ) (k : ℕ) (ha : 0 < a k) (hω : 0 < ω k) (hω1 : ω k ≤ 1)
    (hb0 : b 0 = 0) (hmono : Monotone b)
    (hinc : ∀ n : ℕ, b n < a k - (1 - l1) * a k / 2 → c * (ω k * a k) ≤ b (n + 1) - b n)
    (hex : ∃ n : ℕ, a k - (1 - l1) * a k / 2 ≤ b n) :
    ((Nat.find hex : ℕ) : ℝ) ≤ (1 / c + 1) / ω k := by
  have hq : 0 < c * (ω k * a k) := by positivity
  have hh : 0 ≤ a k - (1 - l1) * a k / 2 := by nlinarith [ha, hl10]
  have hkey := hitting_le b (c * (ω k * a k)) (a k - (1 - l1) * a k / 2) hq hh hb0 hmono hinc hex
  have hcne : c ≠ 0 := ne_of_gt hc
  have hωne : ω k ≠ 0 := ne_of_gt hω
  have hdiv : (a k - (1 - l1) * a k / 2) / (c * (ω k * a k)) ≤ 1 / (c * ω k) := by
    rw [div_le_iff₀ hq]
    have hrhs : 1 / (c * ω k) * (c * (ω k * a k)) = a k := by field_simp
    rw [hrhs]
    nlinarith
  have hinv : (1 : ℝ) ≤ 1 / ω k := by
    rw [le_div_iff₀ hω]; linarith
  have hsplit : (1 / c + 1) / ω k = 1 / (c * ω k) + 1 / ω k := by
    field_simp
  rw [hsplit]
  linarith

/-- **`τ_k/R_k^2 → 0`** (`sandpile.tex:6123`).  The hitting time is `O(1/ω_k)`
and `R_k^2 = G(0,0)L_k/ω_k`, so the ratio is `O(1/L_k)`. -/
theorem tendsto_hittingTime_div_scaleSq (τ : ℕ → ℕ) (ω L R : ℕ → ℝ) {G00 C : ℝ}
    (hG : 0 < G00) (hω : ∀ k, 0 < ω k) (hL : Tendsto L atTop atTop)
    (hRL : ∀ k : ℕ, R k ^ 2 * ω k = G00 * L k)
    (hτ : ∀ᶠ k : ℕ in atTop, ((τ k : ℕ) : ℝ) ≤ C / ω k) :
    Tendsto (fun k : ℕ => ((τ k : ℕ) : ℝ) / R k ^ 2) atTop (𝓝 0) := by
  have hLpos : ∀ᶠ k : ℕ in atTop, 0 < L k := hL.eventually_gt_atTop 0
  have hupper : ∀ᶠ k : ℕ in atTop,
      ((τ k : ℕ) : ℝ) / R k ^ 2 ≤ C / (G00 * L k) := by
    filter_upwards [hLpos, hτ] with k hLk hτk
    have hRsq : 0 < R k ^ 2 := by
      have h1 : 0 < R k ^ 2 * ω k := by rw [hRL k]; positivity
      nlinarith [(hω k).le, sq_nonneg (R k)]
    have hmul : R k ^ 2 * ω k = G00 * L k := hRL k
    rw [div_le_div_iff₀ hRsq (by positivity)]
    calc ((τ k : ℕ) : ℝ) * (G00 * L k) = ((τ k : ℕ) : ℝ) * (R k ^ 2 * ω k) := by rw [hmul]
      _ = (((τ k : ℕ) : ℝ) * ω k) * R k ^ 2 := by ring
      _ ≤ C * R k ^ 2 := by
          have : ((τ k : ℕ) : ℝ) * ω k ≤ C := by
            rw [← le_div_iff₀ (hω k)]; exact hτk
          exact mul_le_mul_of_nonneg_right this hRsq.le
  have hlower : ∀ᶠ k : ℕ in atTop, (0 : ℝ) ≤ ((τ k : ℕ) : ℝ) / R k ^ 2 := by
    filter_upwards with k
    positivity
  have hzero : Tendsto (fun k : ℕ => C / (G00 * L k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hL.const_mul_atTop hG)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero hlower hupper

/-! ### The profile coordinate at the hitting time -/

/-- **`z_{k,τ_k} ≤ 1/2`**: the hitting condition, read in the profile
coordinate. -/
theorem bandLevelCoord_hitting_le_half {l1 : ℝ} (a b : ℕ → ℝ) (k : ℕ)
    (hW : 0 < (1 - l1) * a k)
    (hex : ∃ n : ℕ, a k - (1 - l1) * a k / 2 ≤ b n) :
    bandLevelCoord l1 a b k (Nat.find hex) ≤ 1 / 2 :=
  (bandProfileCoord_le_half_iff (a k) ((1 - l1) * a k) hW b _).mpr (le_hitting_value b _ hex)

/-- **`1/2 - C/a_k ≤ z_{k,τ_k}`**: the mean height overshoots the level by at
most one crude step `eq:dgt4-one-step-mean-increment`. -/
theorem half_sub_le_bandLevelCoord_hitting {l1 M : ℝ} (a b : ℕ → ℝ) (k : ℕ)
    (hW : 0 < (1 - l1) * a k) (hM : 0 ≤ M) (hb0 : b 0 = 0)
    (hh : 0 ≤ a k - (1 - l1) * a k / 2)
    (hstep : ∀ n : ℕ, b (n + 1) - b n ≤ M)
    (hex : ∃ n : ℕ, a k - (1 - l1) * a k / 2 ≤ b n) :
    1 / 2 - M / ((1 - l1) * a k) ≤ bandLevelCoord l1 a b k (Nat.find hex) := by
  have hv := hitting_value_le b (a k - (1 - l1) * a k / 2) M hb0 hh hM hstep hex
  have hWne : (1 - l1) * a k ≠ 0 := ne_of_gt hW
  rw [bandLevelCoord_eq, le_div_iff₀ hW]
  have hexp : (1 / 2 - M / ((1 - l1) * a k)) * ((1 - l1) * a k)
      = (1 - l1) * a k / 2 - M := by
    rw [sub_mul, div_mul_cancel₀ M hWne]
    ring
  rw [hexp]
  linarith

/-! ### `y_{k,τ_k} = O(1)` -/

/-- A negative power of a quantity bounded below by `z_0 ∈ (0,1]` is bounded by
`z_0^{-Θ}`, for every exponent in `[0,Θ]`. -/
theorem rpow_neg_le_of_lower_bound {z z0 θ Θ : ℝ} (hz0 : 0 < z0) (hz01 : z0 ≤ 1)
    (hz : z0 ≤ z) (hθ : 0 ≤ θ) (hθΘ : θ ≤ Θ) :
    z ^ (-θ) ≤ z0⁻¹ ^ Θ := by
  have hzpos : 0 < z := lt_of_lt_of_le hz0 hz
  have h1 : z0 ^ θ ≤ z ^ θ := Real.rpow_le_rpow hz0.le hz hθ
  have h0 : (0 : ℝ) < z0 ^ θ := Real.rpow_pos_of_pos hz0 θ
  have h2 : (z ^ θ)⁻¹ ≤ (z0 ^ θ)⁻¹ := inv_anti₀ h0 h1
  have h3 : (z0 ^ θ)⁻¹ = z0⁻¹ ^ θ := (Real.inv_rpow hz0.le θ).symm
  have hone : (1 : ℝ) ≤ z0⁻¹ := (one_le_inv₀ hz0).mpr hz01
  have h4 : z0⁻¹ ^ θ ≤ z0⁻¹ ^ Θ := Real.rpow_le_rpow_of_exponent_le hone hθΘ
  rw [Real.rpow_neg hzpos.le]
  calc (z ^ θ)⁻¹ ≤ (z0 ^ θ)⁻¹ := h2
    _ = z0⁻¹ ^ θ := h3
    _ ≤ z0⁻¹ ^ Θ := h4

/-- **`y_{k,τ_k} = z_{k,τ_k}^{-ϑ_k} = O(1)`** (`sandpile.tex:6212-6214`): the
profile coordinate at the hitting time is between `1/2 - C/a_k` and `1/2`, and
the band exponents are bounded, so the negative power is bounded. -/
theorem bandProfile_hitting_le {l1 M Θ : ℝ} (a b : ℕ → ℝ) (θ : ℕ → ℝ) (k : ℕ)
    (hW : 0 < (1 - l1) * a k) (hM : 0 ≤ M) (hb0 : b 0 = 0)
    (hh : 0 ≤ a k - (1 - l1) * a k / 2)
    (hstep : ∀ n : ℕ, b (n + 1) - b n ≤ M)
    (hθ : 0 ≤ θ k) (hθΘ : θ k ≤ Θ)
    (hsmall : M / ((1 - l1) * a k) ≤ 1 / 4)
    (hex : ∃ n : ℕ, a k - (1 - l1) * a k / 2 ≤ b n) :
    bandLevelCoord l1 a b k (Nat.find hex) ^ (-(θ k)) ≤ (4 : ℝ) ^ Θ := by
  have hlow := half_sub_le_bandLevelCoord_hitting a b k hW hM hb0 hh hstep hex
  have hquarter : (1 : ℝ) / 4 ≤ bandLevelCoord l1 a b k (Nat.find hex) := by
    have : (1 : ℝ) / 4 ≤ 1 / 2 - M / ((1 - l1) * a k) := by linarith
    linarith
  have hinv : ((1 : ℝ) / 4)⁻¹ = 4 := by norm_num
  have := rpow_neg_le_of_lower_bound (z := bandLevelCoord l1 a b k (Nat.find hex))
    (z0 := (1 : ℝ) / 4) (θ := θ k) (Θ := Θ) (by norm_num) (by norm_num) hquarter hθ hθΘ
  rwa [hinv] at this

end Sandpile.Support
