import Sandpile.Support.ClippedRewardEnvelope
import Sandpile.Support.StoppingValueStability
import Sandpile.Support.StopMeasurable

/-!
# Continuity of clipped stopping values

An integrable uniform reward bound gives sequential joint continuity in the
horizon and spatial shift for stopping values on a fixed stopping class.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Clipped stopping values converge jointly in horizon and spatial shift
under an integrable uniform reward bound on a compact set. -/
theorem Sandpile.Support.tendsto_clipped_stopping_values
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hBm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (u : ℕ → ℝ≥0) (v : ℝ≥0) (hu : ∀ n, u n ≤ T) (hv : v ≤ T)
    (y : ℕ → Sandpile.Continuum.Space d) (z : Sandpile.Continuum.Space d)
    (hy : ∀ n, y n ∈ K) (hz : z ∈ K)
    (huv : Tendsto u atTop (𝓝 v)) (hyz : Tendsto y atTop (𝓝 z))
    (bound : Ω → ℝ) (hint : Integrable bound P)
    (hbound : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) (T : ℝ), ∀ q ∈ K,
      ∀ s ≤ T, ‖G r (q + B s ω)‖ ≤ bound ω) :
    Tendsto (fun n => sSup {a : ℝ | ∃ σ : Ω → ℝ≥0,
      Sandpile.Continuum.IsBrownianStopping B σ ∧ (∀ ω, σ ω ≤ T) ∧
      a = ∫ ω, G ((u n : ℝ) - min (σ ω) (u n))
        (y n + B (min (σ ω) (u n)) ω) ∂P}) atTop
      (𝓝 (sSup {a : ℝ | ∃ σ : Ω → ℝ≥0,
        Sandpile.Continuum.IsBrownianStopping B σ ∧ (∀ ω, σ ω ≤ T) ∧
        a = ∫ ω, G ((v : ℝ) - min (σ ω) v) (z + B (min (σ ω) v) ω) ∂P})) := by
  let F := LatticeProb.natFiltration B hBm
  let R : ℝ≥0 → Sandpile.Continuum.Space d → ℝ≥0 → Ω → ℝ :=
    fun a q s ω => G ((a : ℝ) - min s a) (q + B (min s a) ω)
  let S : (ℝ≥0 → Ω → ℝ) → Set ℝ := fun H => {a | ∃ σ : Ω → ℝ≥0,
    IsStoppingTime F (fun ω => (σ ω : ℝ≥0∞)) ∧ (∀ ω, σ ω ≤ T) ∧
    a = ∫ ω, H (σ ω) ω ∂P}
  have hSet : ∀ (a : ℝ≥0) (q : Sandpile.Continuum.Space d), {w : ℝ | ∃ σ : Ω → ℝ≥0,
      Sandpile.Continuum.IsBrownianStopping B σ ∧ (∀ ω, σ ω ≤ T) ∧
      w = ∫ ω, G ((a : ℝ) - min (σ ω) a) (q + B (min (σ ω) a) ω) ∂P} = S (R a q) := by
    intro a q
    ext w
    simp only [Set.mem_ofPred_eq, S, R, F,
      Sandpile.Continuum.isBrownianStopping_iff_natFiltration B hBm]
  let Gext : ℝ × Sandpile.Continuum.Space d → ℝ :=
    fun p => G (max 0 (min (T : ℝ) p.1)) p.2
  have hGext : Continuous Gext := by
    change Continuous ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘
      fun p : ℝ × Sandpile.Continuum.Space d => (max 0 (min (T : ℝ) p.1), p.2))
    apply hG.comp_continuous
    · exact ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    · intro p
      exact ⟨⟨le_max_left _ _, max_le T.coe_nonneg (min_le_left _ _)⟩, Set.mem_univ _⟩
  have hpay : ∀ a ≤ T, ∀ q ∈ K, ∀ σ : Ω → ℝ≥0,
      IsStoppingTime F (fun ω => (σ ω : ℝ≥0∞)) → (∀ ω, σ ω ≤ T) →
      Integrable (fun ω => R a q (σ ω) ω) P := by
    intro a ha q hq σ hσ hσT
    have hσ' : Sandpile.Continuum.IsBrownianStopping B σ :=
      (Sandpile.Continuum.isBrownianStopping_iff_natFiltration B hBm σ).mpr hσ
    have hσm : Measurable σ := hσ'.measurable hBm
    have hθm : Measurable (fun ω => min (σ ω) a) := hσm.min measurable_const
    have hposm : Measurable (fun ω => B (min (σ ω) a) ω) :=
      Sandpile.Continuum.measurable_stopped_position (fun t => (hBm t).measurable) hBc hθm
    have hm : Measurable (fun ω => Gext ((a : ℝ) - min (σ ω) a, q + B (min (σ ω) a) ω)) :=
      hGext.measurable.comp ((measurable_const.sub (measurable_coe_nnreal_real.comp hθm)).prodMk
        (hposm.const_add q))
    have heq : (fun ω => Gext ((a : ℝ) - min (σ ω) a, q + B (min (σ ω) a) ω)) =
        fun ω => R a q (σ ω) ω := by
      funext ω
      dsimp [Gext, R]
      have h0 : (0 : ℝ) ≤ (a : ℝ) - (min (σ ω) a : ℝ≥0) :=
        sub_nonneg.mpr (by exact_mod_cast min_le_right (σ ω) a)
      have hT : (a : ℝ) - (min (σ ω) a : ℝ≥0) ≤ (T : ℝ) :=
        (sub_le_self _ (min (σ ω) a).coe_nonneg).trans (by exact_mod_cast ha)
      rw [min_eq_right hT, max_eq_right h0]
    have hmeas : AEStronglyMeasurable (fun ω => R a q (σ ω) ω) P := by
      rw [← heq]
      exact hm.stronglyMeasurable.aestronglyMeasurable
    apply hint.mono' hmeas
    filter_upwards [hbound] with ω hω
    have hr : (a : ℝ) - min (σ ω) a ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
      ⟨sub_nonneg.mpr (by exact_mod_cast min_le_right (σ ω) a),
        (sub_le_self _ (min (σ ω) a).coe_nonneg).trans (by exact_mod_cast ha)⟩
    exact hω _ hr q hq _ ((min_le_right (σ ω) a).trans ha)
  have hbb : ∀ a ≤ T, ∀ q ∈ K, BddAbove (S (R a q)) := by
    intro a ha q hq
    refine ⟨∫ ω, bound ω ∂P, ?_⟩
    rintro w ⟨σ, hσ, hσT, rfl⟩
    apply integral_mono_ae (hpay a ha q hq σ hσ hσT) hint
    filter_upwards [hbound] with ω hω
    have hr : (a : ℝ) - min (σ ω) a ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
      ⟨sub_nonneg.mpr (by exact_mod_cast min_le_right (σ ω) a),
        (sub_le_self _ (min (σ ω) a).coe_nonneg).trans (by exact_mod_cast ha)⟩
    have hh := hω _ hr q hq _ ((min_le_right (σ ω) a).trans ha)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, R] using hh)
  obtain ⟨D, hDi, hDmajor, hDlim⟩ :=
    Sandpile.Support.exists_integrable_clipped_reward_envelopes P B hBm hBc T G hG K hK
      u v hu hv y z hy hz huv hyz bound hint hbound
  have hdiff : ∀ n, |sSup (S (R (u n) (y n))) - sSup (S (R v z))| ≤ ∫ ω, D n ω ∂P := by
    intro n
    apply Sandpile.Support.abs_sSup_stopping_payoffs_sub_le P F T (R (u n) (y n)) (R v z)
      (D n) (hDi n) ?_ ?_ (hbb (u n) (hu n) (y n) (hy n)) (hbb v hv z hz)
    · filter_upwards [hDmajor] with ω hω s hs
      exact hω n s hs
    · intro H hH σ hσ hσT
      rcases hH with rfl | rfl
      · exact hpay (u n) (hu n) (y n) (hy n) σ hσ hσT
      · exact hpay v hv z hz σ hσ hσT
  have hlim : Tendsto (fun n => sSup (S (R (u n) (y n)))) atTop
      (𝓝 (sSup (S (R v z)))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero_norm (fun n => ?_) hDlim
    simpa only [Real.norm_eq_abs, abs_abs] using hdiff n
  simpa only [hSet] using hlim
