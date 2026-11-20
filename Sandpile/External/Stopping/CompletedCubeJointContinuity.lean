import Sandpile.External.Stopping.CompletedCubeStartContinuity
import Sandpile.External.Stopping.ValueHorizonContinuity

/-!
# Joint continuity of completed cube stopping values

The completed-event cube value varies continuously with both the horizon and
the starting point for bounded continuous rewards.
-/

open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Completed cube-killed Brownian values converge when both starting points
and horizons converge. -/
theorem tendsto_sSup_aeCubeClockPayoffs_of_tendsto_start_horizon
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Continuum.Space d → ℝ≥0 → Ω → Continuum.Space d)
    (hB : ∀ x, Continuum.IsBrownian d x (B x) P)
    (x : Continuum.Space d) (xn : ℕ → Continuum.Space d) (hx : Tendsto xn atTop (𝓝 x))
    (T : ℝ≥0) (Tn : ℕ → ℝ≥0) (hTn : Tendsto Tn atTop (𝓝 T))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Tendsto (fun n => sSup (aeClockPayoffs (B (xn n)) P (Tn n) G
      (fun ω => (min (LatticeProb.openExitTime (B (xn n)) (openUnitCube (xn n)) ω)
        (Tn n : ℝ≥0∞)).toNNReal))) atTop
      (𝓝 (sSup (aeClockPayoffs (B x) P T G
        (fun ω => (min (LatticeProb.openExitTime (B x) (openUnitCube x) ω)
          (T : ℝ≥0∞)).toNNReal)))) := by
  obtain ⟨V, hVm, hVc, _, hV⟩ := exists_continuous_sandpile_brownian_version (hB 0)
  let D : Continuum.Space d → ℝ≥0 → ℝ := fun u s =>
    Continuum.brownianDiscountCube V P (fun t z => -G t (u + z)) s 1 0
  have hvalue (u : Continuum.Space d) (s : ℝ≥0) :
      sSup (aeClockPayoffs (B u) P s G
        (fun ω => (min (LatticeProb.openExitTime (B u) (openUnitCube u) ω)
          (s : ℝ≥0∞)).toNNReal)) = D u s := by
    let C : ℝ≥0 → Ω → Continuum.Space d := fun t ω => u + V t ω
    have hC : Continuum.IsBrownian d u C P := Sandpile.Support.isBrownian_add_const d P V hV u
    have hCm : ∀ t, Measurable (C t) := fun t => measurable_const.add (hVm t)
    have hCc : ∀ ω, Continuous fun t => C t ω := fun ω => continuous_const.add (hVc ω)
    calc
      _ = sSup (aeClockPayoffs C P s G
          (fun ω => (min (LatticeProb.openExitTime C (openUnitCube u) ω)
            (s : ℝ≥0∞)).toNNReal)) :=
        sSup_aeCubeClockPayoffs_eq_of_isBrownian P P u (B u) C (hB u) hC s G hGc M hG
      _ = Continuum.brownianDiscountCube C P (fun t z => -G t z) s 1 u :=
        sSup_aeCubeClockPayoffs_eq_brownianDiscountCube P u C hC hCm hCc s G hGc M hG
      _ = D u s := by
        unfold D Continuum.brownianDiscountCube
        exact congrArg sSup (Sandpile.Support.cubeStoppingPayoffs_add_const P V
          (fun t z => -G t z) s 1 u)
  have hshift (u : Continuum.Space d) :
      Continuous (fun p : ℝ × Continuum.Space d => G p.1 (u + p.2)) :=
    hGc.comp (continuous_fst.prodMk (continuous_const.add continuous_snd))
  have htime : Tendsto (fun n => D x (Tn n)) atTop (𝓝 (D x T)) := by
    exact tendsto_brownianDiscountCube_of_tendsto_horizon P 0 V hV T Tn hTn
      (fun t z => G t (x + z)) (hshift x) M (fun s z => hG s (x + z))
  have herr : Tendsto (fun n => D (xn n) (Tn n) - D x (Tn n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let H : ℝ≥0 := T + 1
    have hK := Sandpile.Support.isCompact_strip_cube d (0 : Continuum.Space d) H 1
    have hjoint : Continuous (Function.uncurry
        fun (u : Continuum.Space d) (q : ℝ × Continuum.Space d) => G q.1 (u + q.2)) :=
      hGc.comp (continuous_snd.fst.prodMk (continuous_fst.add continuous_snd.snd))
    obtain ⟨v, hv, hvε⟩ := hK.mem_uniformity_of_prod
      (f := fun (u : Continuum.Space d) (q : ℝ × Continuum.Space d) => G q.1 (u + q.2))
      (s := Set.univ) (q := x) (u := {p : ℝ × ℝ | dist p.1 p.2 < ε / 2})
      hjoint.continuousOn (Set.mem_univ _) (Metric.dist_mem_uniformity (half_pos hε))
    rw [nhdsWithin_univ] at hv
    have hbounded : ∀ᶠ n in atTop, Tn n ≤ H := by
      have ht : T < H := by dsimp [H]; exact lt_add_of_pos_right _ (by norm_num)
      exact (hTn.eventually (Iio_mem_nhds ht)).mono fun _ h => h.le
    filter_upwards [hx.eventually hv, hbounded] with n hn hH
    have hc₁ : ContinuousOn (fun p : ℝ × Continuum.Space d => -G p.1 (xn n + p.2))
        (Set.Icc 0 (Tn n : ℝ) ×ˢ Set.univ) := (hshift (xn n)).neg.continuousOn
    have hc₂ : ContinuousOn (fun p : ℝ × Continuum.Space d => -G p.1 (x + p.2))
        (Set.Icc 0 (Tn n : ℝ) ×ˢ Set.univ) := (hshift x).neg.continuousOn
    have hlip := Continuum.abs_brownianDiscountCube_sub_le_of_continuousOn hV
      (fun t z => -G t (xn n + z)) (fun t z => -G t (x + z))
      (Tn n) 1 M M (ε / 2) (NNReal.coe_nonneg _) zero_le_one hc₁ hc₂
      (fun s hs z hz => by simpa only [abs_neg] using hG s (xn n + z))
      (fun s hs z hz => by simpa only [abs_neg] using hG s (x + z))
      (fun s hs z hz => by
        have hsH : s ∈ Set.Icc (0 : ℝ) H := ⟨hs.1, hs.2.trans (by exact_mod_cast hH)⟩
        have h := hvε (xn n) hn (s, z) ⟨hsH, hz⟩
        have hh : |G s (xn n + z) - G s (x + z)| < ε / 2 := by
          simpa only [Set.mem_ofPred_eq, Real.dist_eq] using h
        simpa only [neg_sub_neg, abs_sub_comm] using hh.le)
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt hlip (half_lt_self hε)
  have hlim : Tendsto (fun n => D (xn n) (Tn n)) atTop (𝓝 (D x T)) := by
    have h := herr.add htime
    simpa only [sub_add_cancel, zero_add] using h
  simpa only [hvalue] using hlim

end Sandpile.External.Stopping
