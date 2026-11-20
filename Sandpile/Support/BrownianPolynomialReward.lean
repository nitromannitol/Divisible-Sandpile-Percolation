import Sandpile.Support.BrownianPathMoments
import Sandpile.Support.BrownianAugmentedStopping

/-!
# Polynomial Brownian stopping rewards

Polynomial growth and Brownian maximal moments provide integrable pathwise
domination for finite-horizon stopping rewards.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

/-- A polynomial-growth reward has an integrable bound along a finite-horizon
Brownian path. -/
theorem Sandpile.Support.exists_integrable_brownian_reward_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (x : Sandpile.Continuum.Space d)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hBm : ∀ t, StronglyMeasurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k) :
    ∃ bound : Ω → ℝ, Integrable bound P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖G ((T : ℝ) - t) (B t ω)‖ ≤ bound ω := by
  obtain ⟨C, k, hCk⟩ := hgrow
  have hC : 0 ≤ C := by
    have h := hCk 0 ⟨le_rfl, T.coe_nonneg⟩ 0
    simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  obtain ⟨n, hn⟩ := exists_nat_ge k
  obtain ⟨M, hMm, hM0, hMbound, hMint⟩ :=
    Sandpile.Support.exists_brownian_path_bound x P B hB hBm hBc T
  let bound : Ω → ℝ := fun ω => C * (1 + M ω) ^ n
  have hint : Integrable bound P := by
    have hmom : Integrable (fun ω => (1 + M ω) ^ n) P := by
      by_cases hn0 : n = 0
      · subst n
        simpa only [pow_zero] using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P)
      · have hLp : MemLp M n P := by
          apply (integrable_norm_rpow_iff hMm.aestronglyMeasurable
            (by exact_mod_cast hn0) (ENNReal.natCast_ne_top n)).mp
          simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
            abs_of_nonneg (hM0 _)] using hMint n
        have hLp' : MemLp (fun ω => 1 + M ω) n P := (memLp_const (1 : ℝ)).add hLp
        have hi := hLp'.integrable_norm_pow hn0
        simpa only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg zero_le_one (hM0 _))] using hi
    exact hmom.const_mul C
  refine ⟨bound, hint, ?_⟩
  filter_upwards [hMbound] with ω hω t ht
  have h0 : (0 : ℝ) ≤ (T : ℝ) - (t : ℝ) := sub_nonneg.mpr (by exact_mod_cast ht)
  have hT : (T : ℝ) - (t : ℝ) ≤ (T : ℝ) := sub_le_self _ t.coe_nonneg
  calc
    ‖G ((T : ℝ) - t) (B t ω)‖ = |G ((T : ℝ) - t) (B t ω)| := Real.norm_eq_abs _
    _ ≤ C * (1 + ‖B t ω‖) ^ k := hCk _ ⟨h0, hT⟩ _
    _ ≤ C * (1 + ‖B t ω‖) ^ n := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [Real.rpow_natCast] using
        (Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 1 + ‖B t ω‖ by linarith [norm_nonneg (B t ω)]) hn)
    _ ≤ bound ω := by
      dsimp [bound]
      have hm : 1 + ‖B t ω‖ ≤ 1 + M ω := by linarith [hω t ht]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm n) hC

/-- Polynomial-growth Brownian stopping values are unchanged by the usual
augmentation of the natural filtration. -/
theorem Sandpile.Support.snellValue_eq_sSup_usualAugmentation
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (x : Sandpile.Continuum.Space d)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hBm : ∀ t, StronglyMeasurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k) :
    Sandpile.External.Snell.snellValue B P G T =
    sSup {a : ℝ | ∃ σ : Ω → ℝ≥0,
      IsStoppingTime (Sandpile.Support.aeCompletedFiltration P
        (LatticeProb.natFiltration B hBm)).rightCont (fun ω => (σ ω : ℝ≥0∞)) ∧
      (∀ ω, σ ω ≤ T) ∧ a = ∫ ω, G ((T : ℝ) - σ ω) (B (σ ω) ω) ∂P} := by
  obtain ⟨bound, hint, hbound⟩ :=
    Sandpile.Support.exists_integrable_brownian_reward_bound x P B hB hBm hBc T G hgrow
  exact Sandpile.Support.snellValue_eq_sSup_usualAugmentation_of_integrable_bound
    P B hBc hBm T G hG bound hint hbound

/-- Polynomial-growth Brownian stopping payoffs in the augmented filtration
form a bounded-above set. -/
theorem Sandpile.Support.bddAbove_augmented_brownian_payoffs
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (x : Sandpile.Continuum.Space d)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hBm : ∀ t, StronglyMeasurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k) :
    BddAbove {a : ℝ | ∃ σ : Ω → ℝ≥0,
      IsStoppingTime (Sandpile.Support.aeCompletedFiltration P
        (LatticeProb.natFiltration B hBm)).rightCont (fun ω => (σ ω : ℝ≥0∞)) ∧
      (∀ ω, σ ω ≤ T) ∧ a = ∫ ω, G ((T : ℝ) - σ ω) (B (σ ω) ω) ∂P} := by
  obtain ⟨bound, hint, hbound⟩ :=
    Sandpile.Support.exists_integrable_brownian_reward_bound x P B hB hBm hBc T G hgrow
  obtain ⟨hcont, hmeas⟩ :=
    Sandpile.Support.brownian_stopping_reward_regular P B hBc hBm T G hG
  exact Sandpile.Support.bddAbove_augmented_stopping_payoffs P (LatticeProb.natFiltration B hBm)
    T (fun t ω => G ((T : ℝ) - t) (B t ω)) bound (ae_of_all _ hcont) hint hbound hmeas
