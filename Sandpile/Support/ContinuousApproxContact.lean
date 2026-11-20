import Sandpile.Support.ContinuousFirstContact

/-!
# Approximate contact of a continuous adapted process

The first time a continuous adapted process falls below a fixed threshold is a
stopping time when it is below that threshold at a deterministic horizon.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- A continuous adapted process below a threshold at the horizon has a first
threshold contact before the horizon, and that time is a stopping time. -/
theorem Sandpile.Support.exists_first_le_stopping_time
    {Ω : Type*} [MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (X : ℝ≥0 → Ω → ℝ) (hXad : StronglyAdapted 𝓕 X)
    (hXc : ∀ ω, Continuous fun t => X t ω) (T : ℝ≥0) (ε : ℝ)
    (hXT : ∀ ω, X T ω ≤ ε) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, IsLeast {t : ℝ≥0 | t ≤ T ∧ X t ω ≤ ε} (τ ω)) ∧
      IsStoppingTime 𝓕 (fun ω => (τ ω : ℝ≥0∞)) := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => max (X t ω - ε) 0
  have hYad : StronglyAdapted 𝓕 Y := by
    intro t
    exact (continuous_id.max continuous_const).comp_stronglyMeasurable
      ((hXad t).sub stronglyMeasurable_const)
  have hYc : ∀ ω, Continuous fun t => Y t ω := fun ω =>
    ((hXc ω).sub continuous_const).max continuous_const
  have hYzero : ∀ t ω, Y t ω = 0 ↔ X t ω ≤ ε := by
    intro t ω
    simp only [Y, max_eq_right_iff, sub_nonpos]
  obtain ⟨τ, hτleast, hτstop⟩ :=
    Sandpile.Support.exists_first_zero_stopping_time Y hYad hYc T (fun ω =>
      (hYzero T ω).2 (hXT ω))
  refine ⟨τ, ?_, hτstop⟩
  intro ω
  have he : {t : ℝ≥0 | t ≤ T ∧ Y t ω = 0} =
      {t : ℝ≥0 | t ≤ T ∧ X t ω ≤ ε} := by
    ext t
    simp only [Set.mem_ofPred_eq, hYzero]
  rw [← he]
  exact hτleast ω

/-- First contacts with nonnegative thresholds decreasing to zero converge
pointwise to the first zero of a nonnegative continuous adapted process. -/
theorem Sandpile.Support.exists_first_le_stoppingTime_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (X : ℝ≥0 → Ω → ℝ) (hXad : StronglyAdapted 𝓕 X)
    (hXc : ∀ ω, Continuous fun t => X t ω) (T : ℝ≥0)
    (hXnonneg : ∀ ω t, t ≤ T → 0 ≤ X t ω) (hXT : ∀ ω, X T ω = 0)
    (ε : ℕ → ℝ) (hεnonneg : ∀ n, 0 ≤ ε n) (hεmono : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    ∃ (τ : Ω → ℝ≥0) (σ : ℕ → Ω → ℝ≥0),
      (∀ ω, IsLeast {t : ℝ≥0 | t ≤ T ∧ X t ω = 0} (τ ω)) ∧
      IsStoppingTime 𝓕 (fun ω => (τ ω : ℝ≥0∞)) ∧
      (∀ n ω, IsLeast {t : ℝ≥0 | t ≤ T ∧ X t ω ≤ ε n} (σ n ω)) ∧
      (∀ n, IsStoppingTime 𝓕 (fun ω => (σ n ω : ℝ≥0∞))) ∧
      (∀ ω, Monotone fun n => σ n ω) ∧
      (∀ n ω, σ n ω ≤ τ ω) ∧
      ∀ ω, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω)) := by
  classical
  obtain ⟨τ, hτleast, hτstop⟩ :=
    Sandpile.Support.exists_first_zero_stopping_time X hXad hXc T hXT
  have hex : ∀ n, ∃ σ : Ω → ℝ≥0,
      (∀ ω, IsLeast {t : ℝ≥0 | t ≤ T ∧ X t ω ≤ ε n} (σ ω)) ∧
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) := fun n =>
    Sandpile.Support.exists_first_le_stopping_time X hXad hXc T (ε n)
      (fun ω => (hXT ω).trans_le (hεnonneg n))
  choose σ hσleast hσstop using hex
  have hστ : ∀ n ω, σ n ω ≤ τ ω := by
    intro n ω
    apply (hσleast n ω).2
    exact ⟨(hτleast ω).1.1, (hτleast ω).1.2.le.trans (hεnonneg n)⟩
  have hmono : ∀ ω, Monotone fun n => σ n ω := by
    intro ω n m hnm
    apply (hσleast n ω).2
    exact ⟨(hσleast m ω).1.1, (hσleast m ω).1.2.trans (hεmono hnm)⟩
  refine ⟨τ, σ, hτleast, hτstop, hσleast, hσstop, hmono, hστ, ?_⟩
  intro ω
  have hbdd : BddAbove (Set.range fun n => σ n ω) :=
    ⟨τ ω, fun _ ⟨n, hn⟩ => hn ▸ hστ n ω⟩
  let L := ⨆ n, σ n ω
  have hlim : Tendsto (fun n => σ n ω) atTop (𝓝 L) :=
    tendsto_atTop_ciSup (hmono ω) hbdd
  have hLτ : L ≤ τ ω := ciSup_le fun n => hστ n ω
  have hLT : L ≤ T := hLτ.trans (hτleast ω).1.1
  have hXLle : X L ω ≤ 0 := by
    apply le_of_tendsto_of_tendsto ((hXc ω).tendsto L |>.comp hlim) hεlim
    exact Eventually.of_forall fun n => (hσleast n ω).1.2
  have hXL : X L ω = 0 := le_antisymm hXLle (hXnonneg ω L hLT)
  have hτL : τ ω ≤ L := (hτleast ω).2 ⟨hLT, hXL⟩
  simpa only [le_antisymm hLτ hτL] using hlim
