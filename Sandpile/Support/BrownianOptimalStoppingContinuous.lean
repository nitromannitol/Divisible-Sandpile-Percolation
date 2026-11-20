import Sandpile.Frozen.BrownianOptimalStopping
import Sandpile.External.ContinuumOptimalStoppingOfContinuous

/-!
# Brownian optimal stopping with continuous paths

The optimal-stopping representation under the everywhere-continuous path convention.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The Brownian optimal-stopping representation for continuous paths. -/
theorem Sandpile.Support.brownian_optimal_stopping_of_continuous
    (d : ℕ) (T : ℝ) (hT : 0 < T) (h : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => h p.1 p.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ y : Sandpile.Continuum.Space d, |h t y| ≤ C * (1 + ‖y‖) ^ k)
    (x : Sandpile.Continuum.Space d)
    {Ω : Type*} [MeasurableSpace Ω]
    (hOS : Sandpile.External.ContinuumOptimalStoppingOfContinuous Ω)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBc : ∀ y ω, Continuous fun s => B y s ω) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ s : ℝ≥0, Measurable (M s)) ∧
      (∀ s : ℝ≥0, (s : ℝ) ≤ T →
        M s =ᵐ[P] fun ω =>
          Sandpile.Continuum.brownianDiscount (B (B x s ω)) P h (T - (s : ℝ))) ∧
      (∀ (ω : Ω) (s : ℝ≥0),
        ContinuousWithinAt (fun r : ℝ≥0 => M r ω) (Set.Ici s) s) ∧
      ∃ τ : Ω → ℝ≥0,
        (∀ ω : Ω, IsLeast {s : ℝ≥0 | (s : ℝ) ≤ T ∧
          h (T - (s : ℝ)) (B x s ω) + M s ω = 0} (τ ω)) ∧
        Sandpile.Continuum.IsBrownianStopping (B x) τ ∧
        Sandpile.Continuum.brownianValue (B x) P h T x =
          h T x - ∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P ∧
        (∀ τ' : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) τ' →
          (∀ ω : Ω, (τ' ω : ℝ) ≤ T) →
          Sandpile.Continuum.brownianValue (B x) P h T x =
            h T x - ∫ ω, h (T - (τ' ω : ℝ)) (B x (τ' ω) ω) ∂P →
          ∀ᵐ ω ∂P, τ ω ≤ τ' ω) ∧
        Sandpile.Continuum.brownianValue (B x) P h T x =
          sSup {a : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ ∧
            (∀ ω : Ω, (σ ω : ℝ) ≤ T) ∧
            a = h T x - ∫ ω, h (T - (σ ω : ℝ)) (B x (σ ω) ω) ∂P}
:= by
  classical
  have hGcont : ContinuousOn
      (fun p : ℝ × Sandpile.Continuum.Space d => (fun t y => -h t y) p.1 p.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) := hcont.neg
  have hGgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ y : Sandpile.Continuum.Space d, |(fun t y => -h t y) t y| ≤ C * (1 + ‖y‖) ^ k := by
    obtain ⟨C, k, hCk⟩ := hgrow
    exact ⟨C, k, fun t ht y => by simpa using hCk t ht y⟩
  obtain ⟨M, hMmeas, hMmod, hMright, τ, hτleast, hτstop, hτgreat, hτmin⟩ :=
    hOS d T hT (fun t y => -h t y) hGcont hGgrow x P B hB hBc
  have hτle : ∀ ω : Ω, ((τ ω : ℝ≥0) : ℝ) ≤ T := fun ω => (hτleast ω).1.1
  have hdisc : Sandpile.Continuum.brownianDiscount (B x) P h T
      = -∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P := by
    have hg : sSup (Sandpile.External.Snell.attainable (B x) P (fun t y => -h t y) T)
        = ∫ ω, -h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P := hτgreat.csSup_eq
    rw [show Sandpile.Continuum.brownianDiscount (B x) P h T
        = sSup (Sandpile.External.Snell.attainable (B x) P (fun t y => -h t y) T) from rfl,
      hg, integral_neg]
  have hvalue : Sandpile.Continuum.brownianValue (B x) P h T x
      = h T x - ∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P := by
    rw [show Sandpile.Continuum.brownianValue (B x) P h T x
        = h T x + Sandpile.Continuum.brownianDiscount (B x) P h T from rfl, hdisc]
    ring
  refine ⟨M, hMmeas, ?_, hMright, τ, ?_, hτstop, hvalue, ?_, ?_⟩
  · intro s hs
    exact hMmod s hs
  · intro ω
    have hset : {s : ℝ≥0 | (s : ℝ) ≤ T ∧ M s ω = (fun t y => -h t y) (T - (s : ℝ)) (B x s ω)}
        = {s : ℝ≥0 | (s : ℝ) ≤ T ∧ h (T - (s : ℝ)) (B x s ω) + M s ω = 0} := by
      ext s
      simp only [Set.mem_ofPred_eq, and_congr_right_iff]
      intro _
      constructor
      · intro hh; rw [hh]; ring
      · intro hh; linarith
    exact hset ▸ hτleast ω
  · intro τ' hτ'stop hτ'le hτ'opt
    refine hτmin τ' hτ'stop hτ'le ?_
    have h1 : Sandpile.Continuum.brownianDiscount (B x) P h T
        = -∫ ω, h (T - (τ' ω : ℝ)) (B x (τ' ω) ω) ∂P := by
      have := hτ'opt
      rw [show Sandpile.Continuum.brownianValue (B x) P h T x
          = h T x + Sandpile.Continuum.brownianDiscount (B x) P h T from rfl] at this
      linarith
    rw [show Sandpile.External.Snell.snellValue (B x) P (fun t y => -h t y) T
        = Sandpile.Continuum.brownianDiscount (B x) P h T from rfl, h1, integral_neg]
  · have hmem : (h T x - ∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P) ∈
        {a : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ ∧
          (∀ ω : Ω, (σ ω : ℝ) ≤ T) ∧
          a = h T x - ∫ ω, h (T - (σ ω : ℝ)) (B x (σ ω) ω) ∂P} :=
      ⟨τ, hτstop, hτle, rfl⟩
    have hub : ∀ a ∈ {a : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ ∧
        (∀ ω : Ω, (σ ω : ℝ) ≤ T) ∧
        a = h T x - ∫ ω, h (T - (σ ω : ℝ)) (B x (σ ω) ω) ∂P},
        a ≤ h T x - ∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P := by
      rintro a ⟨σ, hσstop, hσle, rfl⟩
      have hmemσ : (∫ ω, -h (T - (σ ω : ℝ)) (B x (σ ω) ω) ∂P) ∈
          Sandpile.External.Snell.attainable (B x) P (fun t y => -h t y) T :=
        ⟨σ, hσstop, hσle, rfl⟩
      have := hτgreat.2 hmemσ
      rw [integral_neg, integral_neg] at this
      linarith
    have : IsGreatest {a : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ ∧
        (∀ ω : Ω, (σ ω : ℝ) ≤ T) ∧
        a = h T x - ∫ ω, h (T - (σ ω : ℝ)) (B x (σ ω) ω) ∂P}
        (h T x - ∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P) := ⟨hmem, hub⟩
    rw [hvalue, this.csSup_eq]

