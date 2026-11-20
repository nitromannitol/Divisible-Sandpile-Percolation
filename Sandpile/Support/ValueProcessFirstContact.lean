import Sandpile.Support.BrownianFirstContact
import Sandpile.External.ContinuumOptimalStopping

/-!
# Value processes and first contact

A continuous finite-horizon value function with terminal contact produces a
measurable continuous value process and a first natural-filtration contact time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- A continuous value function and its terminal identity yield the measurable
value process and a pointwise least natural-filtration contact time. -/
theorem Sandpile.Support.exists_value_process_first_contact
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (x : Sandpile.Continuum.Space d) (hBc : ∀ ω, Continuous fun t => B x t ω)
    (hBm : ∀ t, StronglyMeasurable (B x t))
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (V : ℝ≥0 → Sandpile.Continuum.Space d → ℝ)
    (hV : ContinuousOn (fun p : ℝ≥0 × Sandpile.Continuum.Space d => V p.1 p.2)
      (Set.Icc 0 T ×ˢ Set.univ))
    (hVT : ∀ y, V T y = G 0 y)
    (hVval : ∀ s ≤ T, ∀ y, V s y =
      Sandpile.External.Snell.snellValue (B y) P G ((T : ℝ) - s)) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ s, Measurable (M s)) ∧
      (∀ s ≤ T, ∀ ω, M s ω =
        Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s)) ∧
      (∀ ω, Continuous fun s => M s ω) ∧
      ∃ τ : Ω → ℝ≥0,
        (∀ ω, IsLeast {s : ℝ≥0 | s ≤ T ∧
          M s ω = G ((T : ℝ) - s) (B x s ω)} (τ ω)) ∧
        Sandpile.Continuum.IsBrownianStopping (B x) τ := by
  let Vext : ℝ≥0 × Sandpile.Continuum.Space d → ℝ := fun p => V (min p.1 T) p.2
  have hVext : Continuous Vext := by
    change Continuous ((fun p : ℝ≥0 × Sandpile.Continuum.Space d => V p.1 p.2) ∘
      fun p : ℝ≥0 × Sandpile.Continuum.Space d => (min p.1 T, p.2))
    apply hV.comp_continuous
    · exact ((continuous_fst.min continuous_const).prodMk continuous_snd)
    · intro p
      exact ⟨⟨zero_le, min_le_right _ _⟩, Set.mem_univ _⟩
  let Gext : ℝ≥0 × Sandpile.Continuum.Space d → ℝ :=
    fun p => G ((T : ℝ) - (min p.1 T : ℝ≥0)) p.2
  have hGext : Continuous Gext := by
    change Continuous ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘
      fun p : ℝ≥0 × Sandpile.Continuum.Space d =>
        ((T : ℝ) - (min p.1 T : ℝ≥0), p.2))
    apply hG.comp_continuous
    · exact ((continuous_const.sub (continuous_subtype_val.comp
        (continuous_fst.min continuous_const))).prodMk continuous_snd)
    · intro p
      refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
      · exact sub_nonneg.mpr (by exact_mod_cast min_le_right p.1 T)
      · exact sub_le_self _ (min p.1 T).coe_nonneg
  let H : ℝ≥0 × Sandpile.Continuum.Space d → ℝ := fun p => Vext p - Gext p
  have hH : Continuous H := hVext.sub hGext
  have hHT : ∀ y, H (T, y) = 0 := by
    intro y
    simp only [H, Vext, Gext, min_self, sub_self, hVT]
  obtain ⟨τ, hτleast, hτstop⟩ :=
    Sandpile.Support.exists_brownian_first_contact (B x) hBc H hH T hHT
  let M : ℝ≥0 → Ω → ℝ := fun s ω => Vext (s, B x s ω)
  have hMmeas : ∀ s, Measurable (M s) := by
    intro s
    exact (hVext.comp (continuous_const.prodMk continuous_id)).measurable.comp (hBm s).measurable
  have hMcont : ∀ ω, Continuous fun s => M s ω := by
    intro ω
    exact hVext.comp (continuous_id.prodMk (hBc ω))
  refine ⟨M, hMmeas, ?_, hMcont, τ, ?_, hτstop⟩
  · intro s hs ω
    change V (min s T) (B x s ω) = _
    rw [min_eq_left hs]
    exact hVval s hs (B x s ω)
  · intro ω
    have heq : {s : ℝ≥0 | s ≤ T ∧ H (s, B x s ω) = 0} =
        {s : ℝ≥0 | s ≤ T ∧ M s ω = G ((T : ℝ) - s) (B x s ω)} := by
      ext s
      simp only [Set.mem_ofPred_eq, and_congr_right_iff]
      intro hs
      simp only [H, Vext, Gext, M, min_eq_left hs, sub_eq_zero]
    exact heq ▸ hτleast ω
