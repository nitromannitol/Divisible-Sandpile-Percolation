import Sandpile.Support.BrownianContinuationSelection
import Sandpile.Support.StoppingTimeSelectionEvents

/-!
# Continuations after countably valued Brownian stops

A path rule chosen from information at a countably valued stopping time can be
concatenated with that time without exceeding a deterministic horizon.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- A countably valued Brownian stop can be followed by a bounded path rule
chosen using a label measurable at the stop. -/
theorem Sandpile.Support.isBrownianStopping_continuation_of_countable_stop
    {Ω ι : Type*} [MeasurableSpace Ω] {d : ℕ} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hBm : ∀ t, StronglyMeasurable (B t)) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (LatticeProb.natFiltration B hBm) (fun ω => (τ ω : ℝ≥0∞)))
    (hcount : (Set.range τ).Countable) (hτT : ∀ ω, τ ω ≤ T)
    (j : Ω → ι) (hj : Measurable[hτ.measurableSpace] j)
    (y : Set.range τ → ι → Sandpile.Continuum.Space d)
    (θ : Set.range τ → ι → (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0)
    (hθ : ∀ r i, IsStoppingTime (LatticeProb.natFiltration
      (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
      (fun t => (measurable_pi_apply t).stronglyMeasurable))
      (fun p => (θ r i p : ℝ≥0∞)))
    (hθT : ∀ r i p, θ r i p ≤ T - r.1) :
    let σ : Ω → ℝ≥0 := fun ω =>
      τ ω + θ ⟨τ ω, ⟨ω, rfl⟩⟩ (j ω)
        (fun t => y ⟨τ ω, ⟨ω, rfl⟩⟩ (j ω) + (B (τ ω + t) ω - B (τ ω) ω))
    Sandpile.Continuum.IsBrownianStopping B σ ∧ ∀ ω, τ ω ≤ σ ω ∧ σ ω ≤ T := by
  classical
  let : Countable (Set.range τ) := hcount.to_subtype
  let k : Ω → Set.range τ × ι := fun ω => (⟨τ ω, ⟨ω, rfl⟩⟩, j ω)
  let s : Set.range τ × ι → ℝ≥0 := fun p => p.1.1
  have hτcount : (Set.range fun ω => (τ ω : ℝ≥0∞)).Countable := by
    refine (hcount.image (fun r : ℝ≥0 => (r : ℝ≥0∞))).mono ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨τ ω, ⟨ω, rfl⟩, rfl⟩
  have hk : ∀ p, MeasurableSet[Sandpile.Continuum.brownianFiltration B (s p)]
      {ω | k ω = p} := by
    intro ⟨r, i⟩
    have he := Sandpile.Support.measurableSet_stoppingTime_eq_and_label
      (LatticeProb.natFiltration B hBm) τ hτ hτcount j hj r.1 i
    have hset : {ω | k ω = (r, i)} = {ω | τ ω = r.1 ∧ j ω = i} := by
      ext ω
      simp only [Set.mem_ofPred_eq, k, Prod.mk.injEq, Subtype.ext_iff]
    rw [hset]
    exact he
  have hr : ∀ p : Set.range τ × ι, s p ≤ T := by
    rintro ⟨⟨r, ω, rfl⟩, i⟩
    exact hτT ω
  have h := Sandpile.Support.isBrownianStopping_select_continuation_of_times
    B s (fun p => T - s p) k hk (fun p => y p.1 p.2) (fun p => θ p.1 p.2)
    (fun p => hθ p.1 p.2) (fun p => hθT p.1 p.2) T
    (fun p => le_of_eq (add_tsub_cancel_of_le (hr p)))
  exact h
