import Sandpile.External.Stopping.FiniteNaturalRewardDensity

/-!
# Lower limit of stopping values under uniform path convergence

Finite decision approximation proves the lower value inequality of Coquet and
Toldo, Section 2.2, for continuous limiting paths and almost surely uniformly
convergent adapted approximations.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Expected rewards attainable by bounded stopping times of a filtration. -/
def filtrationStoppingPayoffs {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ}
    (F : Filtration ℝ≥0 m) (P : Measure Ω)
    (X : ℝ≥0 → Ω → Continuum.Space d) (T : ℝ≥0)
    (G : ℝ≥0 → Continuum.Space d → ℝ) : Set ℝ :=
  {a | ∃ τ : Ω → ℝ≥0, IsStoppingTime F (fun ω => (τ ω : ℝ≥0∞)) ∧
    (∀ ω, τ ω ≤ T) ∧ a = ∫ ω, G (τ ω) (X (τ ω) ω) ∂P}

/-- Expected rewards attainable by bounded natural stopping times. -/
def naturalStoppingPayoffs {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (X : ℝ≥0 → Ω → Continuum.Space d) (T : ℝ≥0)
    (G : ℝ≥0 → Continuum.Space d → ℝ) : Set ℝ :=
  {a | ∃ τ : Ω → ℝ≥0, Continuum.IsBrownianStopping X τ ∧
    (∀ ω, τ ω ≤ T) ∧ a = ∫ ω, G (τ ω) (X (τ ω) ω) ∂P}

/-- The natural stopping value of a continuous limit is no larger than the
asymptotic lower value of adapted uniformly convergent processes. -/
theorem eventually_natural_value_le_adapted_value_add
    {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Filtration ℝ≥0 m) (T : ℝ≥0)
    (Xn : ℕ → ℝ≥0 → Ω → Continuum.Space d) (X : ℝ≥0 → Ω → Continuum.Space d)
    (hXm : ∀ t, Measurable (X t)) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hXn : ∀ n, Measurable (fun p : ℝ≥0 × Ω => Xn n p.1 p.2))
    (hXadapt : ∀ n t, @Measurable Ω (Continuum.Space d) (F n t) inferInstance (Xn n t))
    (hpath : ∀ᵐ ω ∂P,
      TendstoUniformlyOn (fun n t => Xn n t ω) (fun t => X t ω) atTop (Set.Icc 0 T))
    (G : ℝ≥0 → Continuum.Space d → ℝ) (hGc : Continuous (fun p : ℝ≥0 × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, sSup (naturalStoppingPayoffs P X T G) ≤
      sSup (filtrationStoppingPayoffs (F n) P (Xn n) T G) + ε := by
  have hne : (naturalStoppingPayoffs P X T G).Nonempty :=
    ⟨_, fun _ => 0, Continuum.isBrownianStopping_const X 0, (fun _ => bot_le), rfl⟩
  have hbound (n : ℕ) : BddAbove (filtrationStoppingPayoffs (F n) P (Xn n) T G) := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, rfl⟩
    have hb := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G (τ ω) (Xn n (τ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  obtain ⟨a, ⟨τ, hτ, hτT, rfl⟩, ha⟩ := exists_lt_of_lt_csSup hne
    (show sSup (naturalStoppingPayoffs P X T G) - ε / 3 < sSup (naturalStoppingPayoffs P X T G) by linarith)
  obtain ⟨σ, hσ, hσT, hσfin, hσclose⟩ :=
    exists_finite_natural_stop_reward_close P X hXm hXc T τ hτ hτT G hGc M hG (ε / 3) (by positivity)
  let V : Finset ℝ≥0 := hσfin.toFinset
  have hσV : ∀ ω, σ ω ∈ V := fun ω => hσfin.mem_toFinset.mpr ⟨ω, rfl⟩
  have hVT : ∀ t ∈ V, t ≤ T := by
    intro t ht
    obtain ⟨ω, hω⟩ := hσfin.mem_toFinset.mp ht
    rw [← hω]
    exact hσT ω
  obtain ⟨τn, hτn, hτnT, hlim⟩ := exists_finite_natural_stopping_reward_approx
    P F T V hVT σ hσV Xn X hσ hXm hXc hXn hXadapt hpath G hGc M hG
  have hnear : ∀ᶠ n in atTop,
      (∫ ω, G (σ ω) (X (σ ω) ω) ∂P) - ε / 3 <
        ∫ ω, G (τn n ω) (Xn n (τn n ω) ω) ∂P :=
    hlim.eventually (eventually_gt_nhds (by linarith :
      (∫ ω, G (σ ω) (X (σ ω) ω) ∂P) - ε / 3 <
        ∫ ω, G (σ ω) (X (σ ω) ω) ∂P))
  filter_upwards [hnear] with n hn
  have hpay : (∫ ω, G (τn n ω) (Xn n (τn n ω) ω) ∂P) ≤
      sSup (filtrationStoppingPayoffs (F n) P (Xn n) T G) :=
    le_csSup (hbound n) ⟨τn n, hτn n, hτnT n, rfl⟩
  have hclose := (abs_lt.mp hσclose).1
  linarith

end Sandpile.External.Stopping
