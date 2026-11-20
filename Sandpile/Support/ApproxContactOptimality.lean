import Sandpile.Support.ContinuousApproxContact
import Sandpile.Support.StoppedProcessConvergence

/-!
# First-contact optimality from approximate contacts

If the expected value at every approximate contact equals the initial value,
continuity and an integrable envelope give equality at first contact.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Equality of expected values at approximate contacts passes to first
contact for a continuous adapted value process with an integrable envelope. -/
theorem Sandpile.Support.exists_optimal_first_contact_of_approximate_contacts
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 m) (M R : ℝ≥0 → Ω → ℝ)
    (hMad : StronglyAdapted 𝓕 M) (hRad : StronglyAdapted 𝓕 R)
    (hMc : ∀ ω, Continuous fun t => M t ω)
    (hRc : ∀ ω, Continuous fun t => R t ω) (T : ℝ≥0)
    (hdom : ∀ ω t, t ≤ T → R t ω ≤ M t ω) (hterminal : ∀ ω, M T ω = R T ω)
    (D : Ω → ℝ) (hDi : Integrable D P)
    (hD : ∀ᵐ ω ∂P, ∀ t ≤ T, ‖M t ω‖ ≤ D ω)
    (ε : ℕ → ℝ) (hεnonneg : ∀ n, 0 ≤ ε n) (hεmono : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0)) (v : ℝ)
    (happrox : ∀ (n : ℕ) (σ : Ω → ℝ≥0),
      (∀ ω, IsLeast {t : ℝ≥0 | t ≤ T ∧ M t ω - R t ω ≤ ε n} (σ ω)) →
      (∫ ω, M (σ ω) ω ∂P) = v) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, IsLeast {t : ℝ≥0 | t ≤ T ∧ M t ω = R t ω} (τ ω)) ∧
      IsStoppingTime 𝓕 (fun ω => (τ ω : ℝ≥0∞)) ∧
      (∫ ω, R (τ ω) ω ∂P) = v := by
  let X : ℝ≥0 → Ω → ℝ := fun t ω => M t ω - R t ω
  have hXad : StronglyAdapted 𝓕 X := hMad.sub hRad
  have hXc : ∀ ω, Continuous fun t => X t ω := fun ω => (hMc ω).sub (hRc ω)
  have hXnonneg : ∀ ω t, t ≤ T → 0 ≤ X t ω := fun ω t ht => sub_nonneg.mpr (hdom ω t ht)
  have hXT : ∀ ω, X T ω = 0 := fun ω => sub_eq_zero.mpr (hterminal ω)
  obtain ⟨τ, σ, hτleast, hτstop, hσleast, hσstop, _, _, hσlim⟩ :=
    Sandpile.Support.exists_first_le_stoppingTime_tendsto X hXad hXc T hXnonneg hXT
      ε hεnonneg hεmono hεlim
  have hτfirst : ∀ ω, IsLeast {t : ℝ≥0 | t ≤ T ∧ M t ω = R t ω} (τ ω) := by
    intro ω
    have he : {t : ℝ≥0 | t ≤ T ∧ X t ω = 0} =
        {t : ℝ≥0 | t ≤ T ∧ M t ω = R t ω} := by
      ext t
      simp only [Set.mem_ofPred_eq, X, sub_eq_zero]
    exact he ▸ hτleast ω
  have hmeas : ∀ ρ : Ω → ℝ≥0, IsStoppingTime 𝓕 (fun ω => (ρ ω : ℝ≥0∞)) →
      Measurable ρ := fun ρ hρ => measurable_coe_nnreal_ennreal_iff.1
    (hρ.measurable.mono hρ.measurableSpace_le le_rfl)
  have hσT : ∀ n ω, σ n ω ≤ T := fun n ω => (hσleast n ω).1.1
  have hτT : ∀ ω, τ ω ≤ T := fun ω => (hτfirst ω).1.1
  have hMm : ∀ t, StronglyMeasurable (M t) := fun t => (hMad t).mono (𝓕.le t)
  obtain ⟨_, hlim⟩ := Sandpile.Support.tendsto_integral_stopped_process
    P M hMm hMc T D hDi hD σ τ (fun n => hmeas (σ n) (hσstop n))
    (hmeas τ hτstop) hσT hτT (ae_of_all P hσlim)
  have hseq : ∀ n, (∫ ω, M (σ n ω) ω ∂P) = v := fun n =>
    happrox n (σ n) (hσleast n)
  have hvalue : (∫ ω, M (τ ω) ω ∂P) = v := by
    apply tendsto_nhds_unique hlim
    simpa only [hseq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (𝓝 v))
  refine ⟨τ, hτfirst, hτstop, ?_⟩
  calc
    _ = ∫ ω, M (τ ω) ω ∂P := by
      apply integral_congr_ae
      exact ae_of_all P fun ω => (hτfirst ω).1.2.symm
    _ = v := hvalue
