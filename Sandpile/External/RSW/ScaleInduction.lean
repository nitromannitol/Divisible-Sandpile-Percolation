import Sandpile.External.RSW.LastGoodScale

/-!
# Bridge comparison across all scales

The last good scale exists because the initial scale is good. The quasi-crossing and
closing estimates then give the bridge comparison at any later scale.
-/

open Set

namespace Sandpile.External.RSW

/-- Adjacent-scale, cascade and closing estimates imply the bridge comparison at every scale. -/
theorem kstBridge_comparison_of_scale_estimates
    (b d : ℕ → Icc (0 : ℝ) 1) (q r : ℕ → ℕ → Icc (0 : ℝ) 1)
    (hgood : kstScaleIso 18 (unitIntervalComplement (d 0)) ≤ b 0)
    (hb : ∀ k, kstScaleIso 1 (b k) ≤ b (k + 1))
    (hd : ∀ k, kstScaleIso 1 (d k) ≤ d (k + 1))
    (hnear : ∀ j, kstScaleIso 4 (unitIntervalComplement (d (j + 1))) ≤ q (j + 1) j)
    (hnearDual : ∀ j, kstScaleIso 4 (unitIntervalComplement (b (j + 1))) ≤ r (j + 1) j)
    (hcascade : ∀ i j, j < i →
      q (i + 1) j < kstScaleIso 4 (unitIntervalComplement (d (i + 1))) →
      (kstScaleIso 4 (unitIntervalComplement (d (i + 1))) : ℝ) * (q i j : ℝ) ≤
        1 - (1 - (b i : ℝ)) ^ 2)
    (hcascadeDual : ∀ i j, j < i →
      r (i + 1) j < kstScaleIso 4 (unitIntervalComplement (b (i + 1))) →
      (kstScaleIso 4 (unitIntervalComplement (b (i + 1))) : ℝ) * (r i j : ℝ) ≤
        1 - (1 - (d i : ℝ)) ^ 2)
    (hclose : ∀ i j, j ≤ i → (q i j : ℝ) * (b j : ℝ) ≤ b i)
    (hcloseDual : ∀ i j, j ≤ i → (r i j : ℝ) * (d j : ℝ) ≤ d i)
    (K : ℕ) : kstScaleIso 20 (unitIntervalComplement (d K)) ≤ b K := by
  classical
  by_cases hK : kstScaleIso 18 (unitIntervalComplement (d K)) ≤ b K
  · exact (kstScaleIso_antitone 18 20 (by omega) _).trans hK
  · let P : ℕ → Prop := fun k => kstScaleIso 18 (unitIntervalComplement (d k)) ≤ b k
    let j := Nat.findGreatest P K
    have hjK : j ≤ K := Nat.findGreatest_le K
    have hjgood : P j := Nat.findGreatest_spec (Nat.zero_le K) hgood
    have hjlt : j < K := by
      by_contra hn
      have : j = K := by omega
      exact hK (this ▸ hjgood)
    let L := K - j
    have hL : 1 ≤ L := by dsimp [L]; omega
    have hjL : j + L = K := by dsimp [L]; omega
    have hbad : ∀ k, 1 ≤ k → k ≤ L →
        b (j + k) < kstScaleIso 18 (unitIntervalComplement (d (j + k))) := by
      intro k hk hkL
      apply lt_of_not_ge
      exact Nat.findGreatest_is_greatest (P := P) (by omega : j < j + k)
        (by omega : j + k ≤ K)
    have h := kstBridge_comparison_of_bad_scales
      (fun k => b (j + k)) (fun k => d (j + k))
      (fun k => q (j + k) j) (fun k => r (j + k) j) L hL
      (by simpa only [Nat.add_zero] using hjgood)
      (by simpa only using hnear j) (by simpa only using hnearDual j)
      (fun k _ => by simpa only [← Nat.add_assoc] using hb (j + k))
      (fun k _ => by simpa only [← Nat.add_assoc] using hd (j + k)) hbad
      (fun k hk hkL => by
        simpa only [← Nat.add_assoc] using hcascade (j + k) j (by omega))
      (fun k hk hkL => by
        simpa only [← Nat.add_assoc] using hcascadeDual (j + k) j (by omega))
      (by simpa only [Nat.add_zero] using hclose (j + L) j (by omega))
      (by simpa only [Nat.add_zero] using hcloseDual (j + L) j (by omega))
    simpa only [hjL] using h

end Sandpile.External.RSW
