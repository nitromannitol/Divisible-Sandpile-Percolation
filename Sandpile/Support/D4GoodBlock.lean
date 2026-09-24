/-
Block percolation for a superlevel set in the coordinate plane: the
Liggett-Schonmann-Stacey domination of `sandpile.tex:3991-3995` applied to the
good-block process of a field, followed by the chaining of good blocks into an
infinite nearest-neighbour component of the superlevel set.
-/
import Sandpile.Support.BlockPercolation
import Sandpile.External.LSSDomination

open MeasureTheory ProbabilityTheory

namespace Sandpile

open scoped Classical

/-- Block percolation for a superlevel set: if the good-block process of a
field is stationary, `k`-dependent and has one-site success probability at
least `1 - δ`, then the superlevel set `{ℓ ≤ F}` has an infinite
nearest-neighbour component almost surely. -/
theorem good_block_percolation (hLSS : Sandpile.External.LSSDomination) (k : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (r : ℕ), 1 ≤ r → ∀ (F : Ω → Site 2 → ℝ) (ℓ : ℝ),
        (∀ z : Site 2, Measurable (fun ω => decide (BlockGood r (F ω) ℓ z))) →
        (∀ w : Site 2,
          MeasureTheory.Measure.map
              (fun ω z => decide (BlockGood r (F ω) ℓ (z + w))) P =
            MeasureTheory.Measure.map
              (fun ω z => decide (BlockGood r (F ω) ℓ z)) P) →
        (∀ S T : Set (Site 2), S.Finite → T.Finite →
          (∀ s ∈ S, ∀ t ∈ T, (k : ℝ) < Sandpile.External.latticeDist s t) →
          ProbabilityTheory.Indep
            (MeasurableSpace.generateFrom
              (S.image fun s => {ω : Ω | decide (BlockGood r (F ω) ℓ s) = true}))
            (MeasurableSpace.generateFrom
              (T.image fun t => {ω : Ω | decide (BlockGood r (F ω) ℓ t) = true})) P) →
        (∀ z : Site 2, 1 - δ ≤ (P {ω : Ω | decide (BlockGood r (F ω) ℓ z) = true}).toReal) →
        ∀ᵐ ω ∂P, HasInfiniteComponent {u : Site 2 | ℓ ≤ F ω u} := by
  obtain ⟨δ, hδ, hmain⟩ := hLSS k
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ P _ r hr F ℓ hmeas hstat hindep hone
  have hcomp := hmain Ω P (fun z ω => decide (BlockGood r (F ω) ℓ z)) hmeas hstat hindep hone
  filter_upwards [hcomp] with ω hω
  refine block_component_infinite hr (F ω) ℓ ?_
  have hset : {z : Site 2 | decide (BlockGood r (F ω) ℓ z) = true} =
      {z : Site 2 | BlockGood r (F ω) ℓ z} := by
    ext z
    simp
  simpa only [hset] using hω

end Sandpile
