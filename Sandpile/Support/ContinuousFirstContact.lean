import LatticeProb.Prob.StopFunctionalHit

/-!
# First contact of a continuous adapted process

A continuous adapted process that vanishes by a deterministic horizon has a
first zero, and that time is a stopping time of the given filtration.
-/

open MeasureTheory
open scoped ENNReal NNReal

/-- A continuous adapted process that vanishes at the horizon has a least zero
before the horizon, and its least zero is a stopping time. -/
theorem Sandpile.Support.exists_first_zero_stopping_time
    {Ω : Type*} [MeasurableSpace Ω]
    {𝔽 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (X : ℝ≥0 → Ω → ℝ) (hXad : StronglyAdapted 𝔽 X)
    (hXc : ∀ ω, Continuous fun t => X t ω) (T : ℝ≥0)
    (hXT : ∀ ω, X T ω = 0) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, IsLeast {t : ℝ≥0 | t ≤ T ∧ X t ω = 0} (τ ω)) ∧
      IsStoppingTime 𝔽 (fun ω => (τ ω : ℝ≥0∞)) := by
  let H : Ω → ℝ≥0∞ := fun ω => LatticeProb.hitFrom 0 0 (fun t => X t ω)
  have hHle : ∀ ω, H ω ≤ (T : ℝ≥0∞) := fun ω =>
    LatticeProb.hitFrom_le zero_le (hXT ω)
  have hHne : ∀ ω, H ω ≠ ⊤ := fun ω =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (hHle ω)
  let τ : Ω → ℝ≥0 := fun ω => (H ω).toNNReal
  have hτ : ∀ ω, (τ ω : ℝ≥0∞) = H ω := fun ω => ENNReal.coe_toNNReal (hHne ω)
  refine ⟨τ, ?_, ?_⟩
  · intro ω
    obtain ⟨t, ht, _, htzero, htleast⟩ := LatticeProb.exists_hitFrom_eq (hXc ω) (hHne ω)
    have hτt : τ ω = t := ENNReal.coe_inj.mp ((hτ ω).trans ht)
    rw [hτt]
    refine ⟨⟨?_, htzero⟩, ?_⟩
    · exact_mod_cast (ht.symm.trans_le (hHle ω))
    · intro s hs
      exact htleast s zero_le hs.2
  · have hstop := LatticeProb.isStoppingTime_hitFrom_zero hXad hXc 0
    simpa only [hτ] using hstop
