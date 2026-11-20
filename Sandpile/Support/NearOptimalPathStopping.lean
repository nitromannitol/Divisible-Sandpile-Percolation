import Sandpile.Support.PathStoppingApproximation
import Sandpile.Support.BrownianPolynomialReward
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Near-optimal path stopping rules

Continuous rewards with polynomial growth have bounded near-optimal stopping
rules on path space.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Every positive tolerance admits a bounded raw path stopping rule whose
payoff is within that tolerance of the Brownian stopping value. -/
theorem Sandpile.Support.exists_near_optimal_raw_path_stoppingTime
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (x : Sandpile.Continuum.Space d)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hBm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0,
      IsStoppingTime (LatticeProb.natFiltration
        (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
        (fun t => (measurable_pi_apply t).stronglyMeasurable))
        (fun p => (θ p : ℝ≥0∞)) ∧
      (∀ p, θ p ≤ T) ∧
      Sandpile.External.Snell.snellValue B P G T - ε <
        ∫ ω, G ((T : ℝ) - θ (fun t => B t ω))
          (B (θ (fun t => B t ω)) ω) ∂P := by
  have hne : (Sandpile.External.Snell.attainable B P G T).Nonempty := by
    refine ⟨∫ ω, G T (B 0 ω) ∂P, (fun _ => 0),
      Sandpile.Continuum.isBrownianStopping_const B 0, ?_, ?_⟩
    · intro ω
      exact T.coe_nonneg
    · simp only [NNReal.coe_zero, sub_zero]
  obtain ⟨_, hbd⟩ :=
    Sandpile.Support.brownian_stopping_payoffs_integrable_and_bddAbove x P B hB hBm hBc T G hG hgrow
  have hlt : Sandpile.External.Snell.snellValue B P G T - ε / 2 <
      sSup (Sandpile.External.Snell.attainable B P G T) := by
    change Sandpile.External.Snell.snellValue B P G T - ε / 2 <
      Sandpile.External.Snell.snellValue B P G T
    linarith
  obtain ⟨a, ⟨τ, hτ, hτT, rfl⟩, ha⟩ := (lt_csSup_iff hbd hne).mp hlt
  have hτT' : ∀ ω, τ ω ≤ T := fun ω => by exact_mod_cast hτT ω
  obtain ⟨θ, hθ, hθT, hθlim⟩ :=
    Sandpile.Support.exists_raw_path_stoppingTime_seq P B hBm τ hτ T hτT'
  let σ : ℕ → Ω → ℝ≥0 := fun n ω => θ n (fun t => B t ω)
  have hσ : ∀ n, Sandpile.Continuum.IsBrownianStopping B (σ n) := fun n =>
    Sandpile.Support.isBrownianStopping_path_comp B (θ n) (hθ n)
  have hσT : ∀ n ω, σ n ω ≤ T := fun n ω => hθT n _
  obtain ⟨bound, hbi, hb⟩ :=
    Sandpile.Support.exists_integrable_brownian_reward_bound x P B hB hBm hBc T G hgrow
  obtain ⟨hRc, hRm⟩ := Sandpile.Support.brownian_stopping_reward_regular P B hBc hBm T G hG
  have hlim : Tendsto (fun n => ∫ ω, G ((T : ℝ) - σ n ω) (B (σ n ω) ω) ∂P) atTop
      (𝓝 (∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence bound
    · intro n
      exact hRm (σ n) (hσ n) (hσT n)
    · exact hbi
    · intro n
      filter_upwards [hb] with ω hω
      exact hω (σ n ω) (hσT n ω)
    · filter_upwards [hθlim] with ω hω
      have hwithin : Tendsto (fun n => σ n ω) atTop (𝓝[Set.Icc 0 T] (τ ω)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hω, Eventually.of_forall fun n => ⟨zero_le, hσT n ω⟩⟩
      exact ((hRc ω) (τ ω) ⟨zero_le, hτT' ω⟩).tendsto.comp hwithin
  have hnear : Sandpile.External.Snell.snellValue B P G T - ε <
      ∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P := by linarith
  have hev := hlim.eventually (isOpen_Ioi.mem_nhds hnear)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨θ n, hθ n, hθT n, hn⟩
