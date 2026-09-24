/-
Theorem 1.3(iii)(b) of sandpile.tex, frozen.  `sandpile.tex:266-273`
(label `thm:main-explosion`, part (iii)(b)):

  "[$d\geq5$] If, for some $\gamma\in[1,\infty)$ with $\gamma\neq d/2$, we have,
   as $s\to\infty$, $-\log\P(\zeta(0)\leq-s)\asymp s^\gamma$, then
   $\E u_t(0)\asymp(\log t)^{1/\min\{\gamma,d/2\}}$."

Both `≍` are written with two constants and a threshold.

The paper proves this part from `prop:dgt4-height-lower-stretched` and
`thm:dgt4-height-upper-tail`, whose proofs cite `eq:dgt4-green-tail`,
`eq:dgt4-green-l2` and `eq:dgt4-tail-kernel`, so by the standing convention of
this repository the statement takes `Sandpile.External.GreenBoundsHigh` as an
explicit hypothesis and nothing more.  The exponential-moment bound `K₀` that
those two statements quantify over is read off the law itself here, since this
statement fixes the law first.
-/
import Sandpile.Law
import Sandpile.Frozen.DGT4HeightUpperTail
import Sandpile.Frozen.DGT4HeightLowerStretched

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.high_tail
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (γ : ℝ) (hγ : 1 ≤ γ) (hγd : γ ≠ (d : ℝ) / 2)
    (htail : ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ᶠ s : ℝ in atTop,
      a * s ^ γ ≤ -Real.log (ν (Set.Iic (-s))).toReal ∧
        -Real.log (ν (Set.Iic (-s))).toReal ≤ b * s ^ γ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ t : ℕ in atTop,
      c * (Real.log t) ^ (1 / min γ ((d : ℝ) / 2)) ≤
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t ∧
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t ≤
          C * (Real.log t) ^ (1 / min γ ((d : ℝ) / 2))
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  obtain ⟨a, b, ha, hab, hev⟩ := htail
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨s₁, hs₁⟩ := hev.exists_forall_of_atTop
  set s₀ : ℝ := max s₁ 1 with hs₀def
  have hs₀ : 0 < s₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hboth : ∀ s : ℝ, s₀ ≤ s →
      Real.exp (-(b * s ^ γ)) ≤ (ν (Set.Iic (-s))).toReal ∧
        (ν (Set.Iic (-s))).toReal ≤ Real.exp (-(a * s ^ γ)) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs₁ s (le_trans (le_max_left _ _) hs)
    have hs1 : (1 : ℝ) ≤ s := le_trans (le_max_right _ _) hs
    have hspos : (0 : ℝ) < s := by linarith
    have hsγ : (0 : ℝ) < s ^ γ := Real.rpow_pos_of_pos hspos γ
    have hpnn : (0 : ℝ) ≤ (ν (Set.Iic (-s))).toReal := ENNReal.toReal_nonneg
    have hpos : (0 : ℝ) < (ν (Set.Iic (-s))).toReal := by
      rcases eq_or_lt_of_le hpnn with h0 | hpos
      · exfalso
        rw [← h0, Real.log_zero] at h1
        nlinarith
      · exact hpos
    constructor
    · calc Real.exp (-(b * s ^ γ)) ≤ Real.exp (Real.log ((ν (Set.Iic (-s))).toReal)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = (ν (Set.Iic (-s))).toReal := Real.exp_log hpos
    · calc (ν (Set.Iic (-s))).toReal = Real.exp (Real.log ((ν (Set.Iic (-s))).toReal)) :=
            (Real.exp_log hpos).symm
        _ ≤ Real.exp (-(a * s ^ γ)) := Real.exp_le_exp.mpr (by linarith)
  have hupper : ∀ s : ℝ, s₀ ≤ s →
      ν (Set.Iic (-s)) ≤ ENNReal.ofReal (1 * Real.exp (-(a * s ^ γ))) := by
    intro s hs
    rw [one_mul, ← ENNReal.ofReal_toReal (measure_ne_top ν (Set.Iic (-s)))]
    exact ENNReal.ofReal_le_ofReal (hboth s hs).2
  have hlower : ∀ s : ℝ, s₀ ≤ s →
      ENNReal.ofReal (1 * Real.exp (-(b * s ^ γ))) ≤ ν (Set.Iic (-s)) := by
    intro s hs
    rw [one_mul]
    exact ENNReal.ofReal_le_of_le_toReal (hboth s hs).1
  obtain ⟨C, hC, hup⟩ :=
    Sandpile.Frozen.dgt4_height_upper_tail hGreenHigh d hd ν hprob hmean hvar hvar' θ₀
      (∫ z, Real.exp (θ₀ * |z|) ∂ν) hθ₀ hexp le_rfl γ hγ hγd a 1 s₀ ha one_pos hs₀ hupper
  obtain ⟨c, hc, hlow⟩ :=
    Sandpile.Frozen.dgt4_height_lower_stretched hGreenHigh d hd ν hprob hmean hvar hvar' θ₀
      (∫ z, Real.exp (θ₀ * |z|) ∂ν) hθ₀ hexp le_rfl γ 1 b s₀
      (lt_of_lt_of_le one_pos hγ) one_pos hb hs₀ hlower
  refine ⟨min c C, max c C, lt_min hc hC,
    le_trans (min_le_left _ _) (le_max_left _ _), ?_⟩
  filter_upwards [hlow, eventually_ge_atTop 2] with t ht htw
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by
    have : (2 : ℕ) ≤ t := htw
    have : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast this
    linarith
  have hlognn : (0 : ℝ) ≤ (Real.log t) ^ (1 / min γ ((d : ℝ) / 2)) :=
    Real.rpow_nonneg (Real.log_nonneg ht1) _
  refine ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hlognn) ht, ?_⟩
  exact le_trans (hup t htw) (mul_le_mul_of_nonneg_right (le_max_right _ _) hlognn)
