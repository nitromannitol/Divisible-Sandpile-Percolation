import Sandpile.External.RSW.ScaleCompositionProved

/-!
# Propagation of quasi-crossing estimates

At a scale where the bridge comparison fails, the cascade inequality propagates the
quasi-crossing estimate from the previous scale.
-/

open Set

namespace Sandpile.External.RSW

/-- The bad-scale branch of the quasi-crossing induction, in division-free form. -/
theorem kstCascade_induction_step
    (b₀ b₁ d₀ d₁ q₀ q₁ : Icc (0 : ℝ) 1)
    (hb : kstScaleIso 1 b₀ ≤ b₁) (hd : kstScaleIso 1 d₀ ≤ d₁)
    (hbad : b₁ < kstScaleIso 18 (unitIntervalComplement d₁))
    (hprev : kstScaleIso 4 (unitIntervalComplement d₀) ≤ q₀)
    (hcascade : q₁ < kstScaleIso 4 (unitIntervalComplement d₁) →
      (kstScaleIso 4 (unitIntervalComplement d₁) : ℝ) * (q₀ : ℝ) ≤
        1 - (1 - (b₀ : ℝ)) ^ 2) :
    kstScaleIso 4 (unitIntervalComplement d₁) ≤ q₁ := by
  by_contra! hq
  let y := (kstScaleIso 1).symm (kstScaleIso 18 (unitIntervalComplement d₁))
  let D := kstScaleIso 4 (unitIntervalComplement ((kstScaleIso 1).symm d₁))
  let F := kstScaleIso 4 (unitIntervalComplement d₁)
  have hb₀ : b₀ < y := by
    have hh := (kstScaleIso 1).symm.strictMono (lt_of_le_of_lt hb hbad)
    simpa only [OrderIso.symm_apply_apply] using hh
  have hd₀ : d₀ ≤ (kstScaleIso 1).symm d₁ := (kstScaleIso 1).le_symm_apply.mpr hd
  have hD : D ≤ q₀ := by
    apply le_trans _ hprev
    apply (kstScaleIso 4).monotone
    change 1 - (((kstScaleIso 1).symm d₁ : Icc (0 : ℝ) 1) : ℝ) ≤ 1 - (d₀ : ℝ)
    have hd₀' : (d₀ : ℝ) ≤ (kstScaleIso 1).symm d₁ := hd₀
    linarith
  have hnum : 1 - (1 - (b₀ : ℝ)) ^ 2 < 1 - (1 - (y : ℝ)) ^ 2 := by
    have hlt : (b₀ : ℝ) < (y : ℝ) := hb₀
    have hpos : 0 < ((y : ℝ) - b₀) * (2 - (y : ℝ) - b₀) :=
      mul_pos (sub_pos.mpr hlt) (by linarith [y.property.2])
    nlinarith
  have hfunc : 1 - (1 - (y : ℝ)) ^ 2 ≤
      (kstScaleIso 8 (unitIntervalComplement d₁) : ℝ) * D :=
    kstCascade_function_bound_unconditional d₁
  have hF : (kstScaleIso 8 (unitIntervalComplement d₁) : ℝ) ≤ F :=
    kstScaleIso_antitone 4 8 (by omega) _
  have hmul : (kstScaleIso 8 (unitIntervalComplement d₁) : ℝ) * D ≤ (F : ℝ) * q₀ :=
    mul_le_mul hF (show (D : ℝ) ≤ q₀ from hD) D.property.1 F.property.1
  have hh := hcascade hq
  linarith

/-- The quasi-crossing lower bound propagates through a finite sequence of bad scales. -/
theorem kstCascade_induction
    (b d q : ℕ → Icc (0 : ℝ) 1) (K : ℕ)
    (hbase : kstScaleIso 4 (unitIntervalComplement (d 0)) ≤ q 0)
    (hb : ∀ k < K, kstScaleIso 1 (b k) ≤ b (k + 1))
    (hd : ∀ k < K, kstScaleIso 1 (d k) ≤ d (k + 1))
    (hbad : ∀ k < K, b (k + 1) < kstScaleIso 18 (unitIntervalComplement (d (k + 1))))
    (hcascade : ∀ k < K, q (k + 1) < kstScaleIso 4 (unitIntervalComplement (d (k + 1))) →
      (kstScaleIso 4 (unitIntervalComplement (d (k + 1))) : ℝ) * (q k : ℝ) ≤
        1 - (1 - (b k : ℝ)) ^ 2) :
    ∀ k ≤ K, kstScaleIso 4 (unitIntervalComplement (d k)) ≤ q k := by
  intro k
  induction k with
  | zero => intro _; exact hbase
  | succ k ih =>
    intro hk
    have hk' : k < K := by omega
    exact kstCascade_induction_step (b k) (b (k + 1)) (d k) (d (k + 1)) (q k) (q (k + 1))
      (hb k hk') (hd k hk') (hbad k hk') (ih (by omega)) (hcascade k hk')

end Sandpile.External.RSW
