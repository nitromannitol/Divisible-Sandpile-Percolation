/-
The block estimate `eq:d4-positive-block-estimate` (`sandpile.tex:3981-3987`):
for every deficit `δ` and all large `r`, the good block of the block field
`𝓑_{2r,N} + Y_{2r}` at level `b₀ log(2r)/2` fails with probability at most `δ`,
uniformly in the coarse site and over the law class.  The three steps of the
paper's proof enter as the future-height tail, the time-truncation tail and the
crossing estimate for the ball field.
-/
import Sandpile.Support.D4CritStep1Mean
import Sandpile.Support.D4CritStep1Prob
import Sandpile.Support.D4CritCombine
import Sandpile.Support.D4CritLSS
import Sandpile.Support.D4CritLimits
import Sandpile.Support.D4BlockBallCrossing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section
namespace Sandpile

theorem exists_block_estimate
    (hBallGreen : Sandpile.External.BallGreenBounds)
    (hRSW : Sandpile.External.PlanarRSW)
    (hVarScale : Sandpile.External.VarianceScale)
    (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ (b₀ Aloc : ℝ) (Aex : ℕ), 0 < b₀ ∧ 1 ≤ Aloc ∧ 1 ≤ Aex ∧
      ∀ δ : ℝ, 0 < δ → ∃ r₀ : ℕ, 1 ≤ r₀ ∧
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
          ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
          Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
          ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
          ∀ r : ℕ, r₀ ≤ r → ∀ z : Site 2,
            LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | ¬ BlockGood r
                (frBlockField Aex Aloc (2 * r) ζ)
                (b₀ * Real.log ((2 * r : ℕ) : ℝ) / 2) z}
              ≤ ENNReal.ofReal δ := by
  obtain ⟨c₀, b₀, Aloc, Aex, hc₀, hb₀, hAloc, hAex, R₀, hR₀2, hmean1⟩ :=
    exists_step1_mean hVarScale ν₀ θ₀ K₀ hν₀ hθ₀
  have hb₀pos : 0 < b₀ := by rw [hb₀]; positivity
  obtain ⟨c₂, C₂, hc₂, hC₂, hstep1⟩ := measure_exit_value_low_le hBallGreen θ₀ K₀ hθ₀
  obtain ⟨c₃, C₃, hc₃, hC₃, hstep2⟩ := exists_ball_time_tail hBallGreen θ₀ K₀ hθ₀
  obtain ⟨γ, B, hγ, hB, r₁, hstep3⟩ :=
    measure_not_blockGood_ballField_le hBallGreen hRSW ν₀ θ₀ K₀ hν₀ hθ₀ (b₀ / 4) (by positivity)
  refine ⟨b₀, Aloc, Aex, hb₀pos, hAloc, hAex, ?_⟩
  intro δ hδ
  -- the three decay conditions, plus the thresholds
  have hcond : ∀ᶠ R : ℕ in atTop,
      B * (Real.log R) ^ 3 * (R : ℝ) ^ (-γ) ≤ δ / 3 ∧
      25 * (R : ℝ) ^ 2 * (C₂ * Real.exp (-(c₂ * b₀ ^ 2 * (Real.log R) ^ 2))) ≤ δ / 3 ∧
      25 * (R : ℝ) ^ 2 * (C₃ * Real.exp (-(c₃ * (b₀ / 4) ^ 2 * (Real.log R) ^ 2))) ≤ δ / 3 ∧
      b₀ * Real.log R ≤ (R : ℝ) ^ 2 ∧ R₀ ≤ R ∧ r₁ ≤ R ∧ 2 ≤ R := by
    have e1 := eventually_log_cube_rpow_le B γ (δ / 3) hB hγ (by linarith)
    have e2 := eventually_sq_exp_sq_log_le 25 C₂ (c₂ * b₀ ^ 2) (δ / 3)
      (by norm_num) hC₂ (by positivity) (by linarith)
    have e3 := eventually_sq_exp_sq_log_le 25 C₃ (c₃ * (b₀ / 4) ^ 2) (δ / 3)
      (by norm_num) hC₃ (by positivity) (by linarith)
    have e4 : ∀ᶠ R : ℕ in atTop, b₀ * Real.log R ≤ (R : ℝ) ^ 2 := by
      have hlin : ∀ᶠ R : ℕ in atTop, b₀ * Real.log R ≤ (R : ℝ) ^ 2 := by
        filter_upwards [eventually_ge_atTop (Nat.ceil (b₀ + 1)), eventually_ge_atTop 1]
          with R hR hR1
        have hR0 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
        have hlog : Real.log R ≤ (R : ℝ) := Real.log_le_sub_one_of_pos (by linarith) |>.trans
          (by linarith)
        have hbR : b₀ ≤ (R : ℝ) := by
          have h1 : b₀ + 1 ≤ ((Nat.ceil (b₀ + 1) : ℕ) : ℝ) := Nat.le_ceil _
          have h2 : ((Nat.ceil (b₀ + 1) : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
          linarith
        have hlog0 : 0 ≤ Real.log R := Real.log_nonneg hR0
        nlinarith
      exact hlin
    filter_upwards [e1, e2, e3, e4, eventually_ge_atTop R₀, eventually_ge_atTop r₁,
      eventually_ge_atTop 2] with R h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp hcond
  refine ⟨max R₁ 1, le_max_right _ _, ?_⟩
  intro ν hν hmean hvar hexpint hexp r hr z
  haveI := hν
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hRge : R₁ ≤ 2 * r := by
    have : R₁ ≤ r := le_trans (le_max_left _ _) hr
    omega
  obtain ⟨hd1, hd2, hd3, hd4, hdR₀, -, hd2R⟩ := hR₁ (2 * r) hRge
  have hdr₁ : r₁ ≤ r := (hR₁ r (le_trans (le_max_left _ _) hr)).2.2.2.2.2.1
  set L : ℝ := Real.log ((2 * r : ℕ) : ℝ) with hL
  set M : ℝ := ((2 * r : ℕ) : ℝ) with hM
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]; exact_mod_cast (by omega : 1 ≤ 2 * r)
  have hL0 : 0 ≤ L := Real.log_nonneg hM1
  -- Step 3: the ball field crossing estimate
  have h1 := hstep3 ν hν hmean hvar hexpint hexp r hdr₁ z
  -- Step 1: the future height
  have hmeanX : ∀ x : Site 4, 2 * (b₀ * L) ≤
      ∫ ζ, eaExitValue Aex Aloc (2 * r) ζ x ∂(LatticeProb.iidLaw 4 ν) := by
    intro x
    have := hmean1 ν hν hmean hvar hexpint hexp (2 * r) hdR₀ x
    rw [← mul_assoc]
    exact this
  have h2 := fun x : Site 4 => hstep1 Aloc hAloc Aex hAex ν hν hmean hexpint hexp
    (2 * r) hd2R (b₀ * L) (by positivity) hmeanX x
  -- Step 2: the time truncation
  have h3 := fun x : Site 4 => hstep2 Aex hAex ν hν hexpint hexp hmean
    (2 * r) hd2R (b₀ * L / 4) (by positivity) x
  -- the minima are attained at the square
  have hmin2 : min ((b₀ * L) ^ 2) (b₀ * L * M ^ 2) = (b₀ * L) ^ 2 := by
    refine min_eq_left ?_
    nlinarith [mul_nonneg hb₀pos.le hL0, hd4]
  have hmin3 : min ((b₀ * L / 4) ^ 2) (b₀ * L / 4 * M ^ 2) = (b₀ * L / 4) ^ 2 := by
    refine min_eq_left ?_
    nlinarith [mul_nonneg hb₀pos.le hL0, hd4]
  rw [hmin2] at h2
  rw [hmin3] at h3
  -- combine
  have hcomb := measure_not_blockGood_block_le ν Aex Aloc b₀ r z
    (ENNReal.ofReal (B * L ^ 3 * M ^ (-γ)))
    (ENNReal.ofReal (C₂ * Real.exp (-(c₂ * (b₀ * L) ^ 2))))
    (ENNReal.ofReal (C₃ * Real.exp (-(c₃ * (b₀ * L / 4) ^ 2))))
    h1 h2 h3
  refine le_trans hcomb ?_
  -- the numerical bound
  set K : ℝ := ((planeRectangle (4 * r) (4 * r)).card : ℝ) with hK
  have hKle : K ≤ 25 * (r : ℝ) ^ 2 := card_planeRectangle_four_le r hr1
  have hK0 : 0 ≤ K := by positivity
  have hcard : ((planeRectangle (4 * r) (4 * r)).card : ℝ≥0∞) = ENNReal.ofReal K := by
    rw [hK]
    simp
  rw [hcard, ← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul hK0,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hMr : M = 2 * (r : ℝ) := by rw [hM]; push_cast; ring
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hrM : (r : ℝ) ^ 2 ≤ M ^ 2 := by
    rw [hMr]
    nlinarith
  have h25 : K ≤ 25 * M ^ 2 :=
    hKle.trans (mul_le_mul_of_nonneg_left hrM (by norm_num))
  have hb2 : K * (C₂ * Real.exp (-(c₂ * (b₀ * L) ^ 2))) ≤ δ / 3 := by
    have heq : c₂ * (b₀ * L) ^ 2 = c₂ * b₀ ^ 2 * L ^ 2 := by ring
    rw [heq]
    exact le_trans
      (mul_le_mul_of_nonneg_right h25 (le_of_lt (mul_pos hC₂ (Real.exp_pos _)))) hd2
  have hb3 : K * (C₃ * Real.exp (-(c₃ * (b₀ * L / 4) ^ 2))) ≤ δ / 3 := by
    have heq : c₃ * (b₀ * L / 4) ^ 2 = c₃ * (b₀ / 4) ^ 2 * L ^ 2 := by ring
    rw [heq]
    exact le_trans
      (mul_le_mul_of_nonneg_right h25 (le_of_lt (mul_pos hC₃ (Real.exp_pos _)))) hd3
  linarith [hd1, hb2, hb3]

end Sandpile
