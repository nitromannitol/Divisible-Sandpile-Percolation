import Sandpile.External.RSW.CascadeInduction
import Sandpile.External.RSW.BridgeScale

/-!
# The last good scale in the bridge induction

A quasi-crossing estimate propagates across consecutive bad scales. Together with the
closing estimate, it bounds the square of the bridge probability at the last good scale.
-/

open Set

namespace Sandpile.External.RSW

/-- A finite sequence of interval-isomorphism comparisons can be composed. -/
theorem exists_intervalIso_comparison_of_finite_steps
    (f : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1)
    (p : ℕ → Icc (0 : ℝ) 1) (K : ℕ)
    (h : ∀ k < K, f (p k) ≤ p (k + 1)) :
    ∃ g : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1, g (p 0) ≤ p K := by
  induction K with
  | zero => exact ⟨OrderIso.refl _, le_rfl⟩
  | succ K ih =>
    obtain ⟨g, hg⟩ := ih (fun k hk => h k (by omega))
    exact ⟨g.trans f, (f.monotone hg).trans (h K (by omega))⟩

/-- The quasi-crossing estimate holds at every bad scale after the initial scale. -/
theorem kstQuasi_bound_of_bad_scales
    (b d q : ℕ → Icc (0 : ℝ) 1) (K : ℕ)
    (hbase : kstScaleIso 4 (unitIntervalComplement (d 1)) ≤ q 1)
    (hb : ∀ k < K, kstScaleIso 1 (b k) ≤ b (k + 1))
    (hd : ∀ k < K, kstScaleIso 1 (d k) ≤ d (k + 1))
    (hbad : ∀ k, 1 ≤ k → k ≤ K →
      b k < kstScaleIso 18 (unitIntervalComplement (d k)))
    (hcascade : ∀ k, 1 ≤ k → k < K →
      q (k + 1) < kstScaleIso 4 (unitIntervalComplement (d (k + 1))) →
      (kstScaleIso 4 (unitIntervalComplement (d (k + 1))) : ℝ) * (q k : ℝ) ≤
        1 - (1 - (b k : ℝ)) ^ 2) :
    ∀ k, 1 ≤ k → k ≤ K → kstScaleIso 4 (unitIntervalComplement (d k)) ≤ q k := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    intro hkK
    by_cases hk0 : k = 0
    · subst k
      exact hbase
    · have hk1 : 1 ≤ k := by omega
      have hklt : k < K := by omega
      exact kstCascade_induction_step (b k) (b (k + 1)) (d k) (d (k + 1))
        (q k) (q (k + 1)) (hb k hklt) (hd k hklt)
        (hbad (k + 1) (by omega) hkK) (ih hk1 (by omega)) (hcascade k hk1 hklt)

/-- Closing at a bad scale bounds the square of the bridge probability at the initial scale. -/
theorem kstBridge_sq_of_bad_scales
    (b d q : ℕ → Icc (0 : ℝ) 1) (K : ℕ) (hK : 1 ≤ K)
    (hbase : kstScaleIso 4 (unitIntervalComplement (d 1)) ≤ q 1)
    (hb : ∀ k < K, kstScaleIso 1 (b k) ≤ b (k + 1))
    (hd : ∀ k < K, kstScaleIso 1 (d k) ≤ d (k + 1))
    (hbad : ∀ k, 1 ≤ k → k ≤ K →
      b k < kstScaleIso 18 (unitIntervalComplement (d k)))
    (hcascade : ∀ k, 1 ≤ k → k < K →
      q (k + 1) < kstScaleIso 4 (unitIntervalComplement (d (k + 1))) →
      (kstScaleIso 4 (unitIntervalComplement (d (k + 1))) : ℝ) * (q k : ℝ) ≤
        1 - (1 - (b k : ℝ)) ^ 2)
    (hclose : (q K : ℝ) * (b 0 : ℝ) ≤ b K) :
    (b 0 : ℝ) ^ 2 ≤ b K := by
  have hq := kstQuasi_bound_of_bad_scales b d q K hbase hb hd hbad hcascade K hK le_rfl
  have hroot : Real.sqrt (b K : ℝ) ≤ q K := by
    have h₁ : Real.sqrt (b K : ℝ) ≤
        Real.sqrt (kstScaleIso 18 (unitIntervalComplement (d K)) : ℝ) :=
      Real.sqrt_le_sqrt (le_of_lt (hbad K hK le_rfl))
    have h₂ := kstScaleIso_sqrt_succ_le 17 (unitIntervalComplement (d K))
    have h₃ := kstScaleIso_antitone 4 17 (by omega) (unitIntervalComplement (d K))
    exact ((h₁.trans h₂).trans h₃).trans hq
  have hclose' : Real.sqrt (b K : ℝ) * (b 0 : ℝ) ≤ b K :=
    (mul_le_mul_of_nonneg_right hroot (b 0).property.1).trans hclose
  obtain ⟨g, hg⟩ := exists_intervalIso_comparison_of_finite_steps (kstScaleIso 1) b K hb
  exact sq_le_of_sqrt_mul_le_of_scale g (b K) (b 0) hg hclose'


/-- Primal and dual bad-scale estimates turn the last good comparison into the final
bridge comparison. -/
theorem kstBridge_comparison_of_bad_scales
    (b d q r : ℕ → Icc (0 : ℝ) 1) (K : ℕ) (hK : 1 ≤ K)
    (hgood : kstScaleIso 18 (unitIntervalComplement (d 0)) ≤ b 0)
    (hbase : kstScaleIso 4 (unitIntervalComplement (d 1)) ≤ q 1)
    (hbaseDual : kstScaleIso 4 (unitIntervalComplement (b 1)) ≤ r 1)
    (hb : ∀ k < K, kstScaleIso 1 (b k) ≤ b (k + 1))
    (hd : ∀ k < K, kstScaleIso 1 (d k) ≤ d (k + 1))
    (hbad : ∀ k, 1 ≤ k → k ≤ K →
      b k < kstScaleIso 18 (unitIntervalComplement (d k)))
    (hcascade : ∀ k, 1 ≤ k → k < K →
      q (k + 1) < kstScaleIso 4 (unitIntervalComplement (d (k + 1))) →
      (kstScaleIso 4 (unitIntervalComplement (d (k + 1))) : ℝ) * (q k : ℝ) ≤
        1 - (1 - (b k : ℝ)) ^ 2)
    (hcascadeDual : ∀ k, 1 ≤ k → k < K →
      r (k + 1) < kstScaleIso 4 (unitIntervalComplement (b (k + 1))) →
      (kstScaleIso 4 (unitIntervalComplement (b (k + 1))) : ℝ) * (r k : ℝ) ≤
        1 - (1 - (d k : ℝ)) ^ 2)
    (hclose : (q K : ℝ) * (b 0 : ℝ) ≤ b K)
    (hcloseDual : (r K : ℝ) * (d 0 : ℝ) ≤ d K) :
    kstScaleIso 20 (unitIntervalComplement (d K)) ≤ b K := by
  have hbadDual (k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ K) :
      d k < kstScaleIso 18 (unitIntervalComplement (b k)) := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt (hbad k hk hkK)) ((kstScaleIso_duality 18 (b k) (d k)).2 h)
  have hsq := kstBridge_sq_of_bad_scales b d q K hK hbase hb hd hbad hcascade hclose
  have hsqDual := kstBridge_sq_of_bad_scales d b r K hK hbaseDual hd hb hbadDual
    hcascadeDual hcloseDual
  exact kstScaleIso_closing 18 (b K) (b 0) (d K) (d 0) hsq hsqDual hgood

end Sandpile.External.RSW
