import Sandpile.Support.ClippedStoppingContinuity
import Sandpile.Support.ShiftedBrownianRewardBound
import Sandpile.Support.ClippedStoppingValue
import Sandpile.Support.D23CubeValueRegularity

/-!
# Continuity of translated Brownian stopping values

Translated Brownian stopping values are jointly sequentially continuous in
the horizon and starting point.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Finite-horizon stopping values of translated Brownian motions converge
jointly in the horizon and starting point. -/
theorem Sandpile.Support.tendsto_snellValue_translated
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d 0 B P)
    (hBm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ y ∈ K, ‖y‖ ≤ R)
    (u : ℕ → ℝ≥0) (v : ℝ≥0) (hu : ∀ n, u n ≤ T) (hv : v ≤ T)
    (y : ℕ → Sandpile.Continuum.Space d) (z : Sandpile.Continuum.Space d)
    (hy : ∀ n, y n ∈ K) (hz : z ∈ K)
    (huv : Tendsto u atTop (𝓝 v)) (hyz : Tendsto y atTop (𝓝 z)) :
    Tendsto (fun n => Sandpile.External.Snell.snellValue (fun t ω => y n + B t ω) P G (u n))
      atTop (𝓝 (Sandpile.External.Snell.snellValue (fun t ω => z + B t ω) P G v)) := by
  obtain ⟨bound, hint, hbound⟩ :=
    Sandpile.Support.exists_integrable_shifted_brownian_reward_bound 0 P B hB hBm hBc T G hgrow K R hR hKR
  have hlim := Sandpile.Support.tendsto_clipped_stopping_values P B hBm hBc T G hG K hK
    u v hu hv y z hy hz huv hyz bound hint hbound
  have hval : ∀ a ≤ T, ∀ q : Sandpile.Continuum.Space d,
      Sandpile.External.Snell.snellValue (fun t ω => q + B t ω) P G a =
      sSup {w : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B σ ∧
        (∀ ω, σ ω ≤ T) ∧ w = ∫ ω, G ((a : ℝ) - min (σ ω) a)
          (q + B (min (σ ω) a) ω) ∂P} := by
    intro a ha q
    rw [Sandpile.Support.snellValue_eq_sSup_clipped P (fun t ω => q + B t ω) G a T ha]
    congr 1
    ext w
    simp only [Set.mem_ofPred_eq, Sandpile.Support.isBrownianStopping_add_const]
  simpa only [hval _ (hu _) _, hval _ hv _] using hlim
