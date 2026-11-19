import Sandpile.External.Stopping.BrownianLevelExit

/-!
# Regular exits through finitely many Brownian levels

The earliest of finitely many one-dimensional Brownian level hits is regular:
all coordinates stay in their open half-lines before it, and at least one
crosses its boundary strictly before every later time. No independence between
the coordinates is needed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Finitely many Brownian coordinates have a common regular exit time from the
intersection of their open half-lines. -/
theorem ae_brownian_finite_level_exit {ι Ω : Type*} [Finite ι] [Nonempty ι]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ι → ℝ≥0 → Ω → ℝ) (a : ι → ℝ)
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hm : ∀ i t, Measurable (B i t))
    (hc : ∀ i ω, Continuous fun t => B i t ω) :
    ∀ᵐ ω ∂P, ∃ τ : ℝ≥0,
      (∀ s : ℝ≥0, s < τ → ∀ i, -a i < B i s ω) ∧
      (∀ t : ℝ≥0, τ < t → ∃ s : ℝ≥0, s < t ∧ ∃ i, B i s ω < -a i) := by
  have hall : ∀ᵐ ω ∂P, ∀ i,
      let σ := LatticeProb.hitDrift (fun t ω => -B i t ω) 0 (a i) ω
      σ < ⊤ ∧
        (∀ s : ℝ≥0, s < σ.toNNReal → -a i < B i s ω) ∧
        (∀ t : ℝ≥0, σ.toNNReal < t → ∃ s : ℝ≥0, s < t ∧ B i s ω < -a i) :=
    ae_all_iff.2 fun i => ae_brownian_level_regular (hB i) (hm i) (hc i) (a i)
  filter_upwards [hall] with ω hω
  let σ : ι → ℝ≥0 := fun i =>
    (LatticeProb.hitDrift (fun t ω => -B i t ω) 0 (a i) ω).toNNReal
  obtain ⟨i₀, hmin⟩ := Finite.exists_min σ
  refine ⟨σ i₀, ?_, ?_⟩
  · intro s hs i
    exact (hω i).2.1 s (lt_of_lt_of_le hs (hmin i))
  · intro t ht
    obtain ⟨s, hs, hs'⟩ := (hω i₀).2.2 t ht
    exact ⟨s, hs, i₀, hs'⟩

end Sandpile.External.Stopping
