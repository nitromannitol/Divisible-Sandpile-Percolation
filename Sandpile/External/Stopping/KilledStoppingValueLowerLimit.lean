import Sandpile.External.Stopping.FiniteClippedStoppingApproximation
import Sandpile.External.Stopping.FiniteClippedRewardDensity

/-!
# Lower limits of killed stopping values

Finite stopping approximations and converging killing clocks give a lower
bound for optimal stopping values of convergent adapted processes.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Rewards of bounded filtration stopping times before a killing clock. -/
def adaptedClockPayoffs {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ}
    (F : Filtration ℝ≥0 m) (P : Measure Ω) (X : ℝ≥0 → Ω → Continuum.Space d)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ) (κ : Ω → ℝ≥0) : Set ℝ :=
  {a | ∃ τ : Ω → ℝ≥0, IsStoppingTime F (fun ω => (τ ω : ℝ≥0∞)) ∧
    (∀ ω, τ ω ≤ T) ∧ (∀ᵐ ω ∂P, τ ω ≤ κ ω) ∧
    a = ∫ ω, G ((T : ℝ) - τ ω) (X (τ ω) ω) ∂P}

/-- The killed value of a continuous process is bounded by the lower limit of
killed values of adapted uniformly convergent processes with convergent clocks. -/
theorem eventually_clock_value_le_adapted_clock_value_add
    {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Filtration ℝ≥0 m) (T : ℝ≥0)
    (Xn : ℕ → ℝ≥0 → Ω → Continuum.Space d) (X : ℝ≥0 → Ω → Continuum.Space d)
    (hXm : ∀ t, Measurable (X t)) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hXn : ∀ n, Measurable (fun p : ℝ≥0 × Ω => Xn n p.1 p.2))
    (hXadapt : ∀ n t, @Measurable Ω (Continuum.Space d) (F n t) inferInstance (Xn n t))
    (hpath : ∀ᵐ ω ∂P,
      TendstoUniformlyOn (fun n t => Xn n t ω) (fun t => X t ω) atTop (Set.Icc 0 T))
    (κn : ℕ → Ω → ℝ≥0) (κ : Ω → ℝ≥0)
    (hκn : ∀ n, IsStoppingTime (F n) (fun ω => (κn n ω : ℝ≥0∞)))
    (hκ : Continuum.IsBrownianStopping X κ)
    (hκlim : ∀ᵐ ω ∂P, Tendsto (fun n => κn n ω) atTop (𝓝 (κ ω)))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      sSup (clockPayoffs X P T G κ (Continuum.brownianFiltration X)) ≤
        sSup (adaptedClockPayoffs (F n) P (Xn n) T G (κn n)) + ε := by
  have hne : (clockPayoffs X P T G κ (Continuum.brownianFiltration X)).Nonempty :=
    ⟨_, fun _ => 0, Continuum.isBrownianStopping_const X 0, (fun _ => bot_le),
      Filter.Eventually.of_forall (fun _ => bot_le), rfl⟩
  have hbound (n : ℕ) : BddAbove (adaptedClockPayoffs (F n) P (Xn n) T G (κn n)) := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, _, rfl⟩
    have hb := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G ((T : ℝ) - τ ω) (Xn n (τ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  obtain ⟨a, ⟨τ, hτ, hτT, hτκ, rfl⟩, ha⟩ := exists_lt_of_lt_csSup hne
    (show sSup (clockPayoffs X P T G κ (Continuum.brownianFiltration X)) - ε / 3 <
      sSup (clockPayoffs X P T G κ (Continuum.brownianFiltration X)) by linarith)
  obtain ⟨σ, hσ, hσT, hσfin, hσclose⟩ :=
    exists_finite_natural_stop_clipped_reward_close P X hXm hXc T τ κ hτ hκ hτT hτκ
      G hGc M hG (ε / 3) (by positivity)
  let V : Finset ℝ≥0 := hσfin.toFinset
  have hσV : ∀ ω, σ ω ∈ V := fun ω => hσfin.mem_toFinset.mpr ⟨ω, rfl⟩
  have hVT : ∀ t ∈ V, t ≤ T := by
    intro t ht
    obtain ⟨ω, hω⟩ := hσfin.mem_toFinset.mp ht
    rw [← hω]
    exact hσT ω
  let H : ℝ≥0 → Continuum.Space d → ℝ := fun t z => G ((T : ℝ) - t) z
  have hHc : Continuous (fun p : ℝ≥0 × Continuum.Space d => H p.1 p.2) := by
    exact hGc.comp ((continuous_const.sub (NNReal.continuous_coe.comp continuous_fst)).prodMk continuous_snd)
  obtain ⟨ρ, hρ, hρT, hρκ, hlim⟩ :=
    exists_clipped_finite_natural_stopping_reward_approx P F T V hVT σ hσV Xn X
      hσ hXm hXc hXn hXadapt hpath κn κ hκn hκlim H hHc M (fun t z => hG _ _)
  have hnear : ∀ᶠ n in atTop,
      (∫ ω, H (min (σ ω) (κ ω)) (X (min (σ ω) (κ ω)) ω) ∂P) - ε / 3 <
        ∫ ω, H (ρ n ω) (Xn n (ρ n ω) ω) ∂P :=
    hlim.eventually (eventually_gt_nhds (by linarith :
      (∫ ω, H (min (σ ω) (κ ω)) (X (min (σ ω) (κ ω)) ω) ∂P) - ε / 3 <
        ∫ ω, H (min (σ ω) (κ ω)) (X (min (σ ω) (κ ω)) ω) ∂P))
  filter_upwards [hnear] with n hn
  have hpay : (∫ ω, G ((T : ℝ) - ρ n ω) (Xn n (ρ n ω) ω) ∂P) ≤
      sSup (adaptedClockPayoffs (F n) P (Xn n) T G (κn n)) :=
    le_csSup (hbound n) ⟨ρ n, hρ n, hρT n, Filter.Eventually.of_forall (hρκ n), rfl⟩
  dsimp only [H] at hn
  have hclose := (abs_lt.mp hσclose).1
  linarith

end Sandpile.External.Stopping
