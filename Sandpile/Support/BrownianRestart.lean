import Sandpile.Continuum.Stopping
import LatticeProb.Prob.BrownianStrongMarkov

/-!
# Brownian restart at stopping times

The Brownian motion used for the stopping value satisfies the strong Markov
restart property in its natural filtration.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The Brownian-motion predicate has the library's Brownian-space interface. -/
theorem Sandpile.Continuum.IsBrownian.toIsBrownianSpace
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {x : Sandpile.Continuum.Space d} {B : ℝ≥0 → Ω → Sandpile.Continuum.Space d}
    {P : Measure Ω} (hB : Sandpile.Continuum.IsBrownian d x B P) :
    LatticeProb.IsBrownianSpace d x B P :=
  ⟨hB.start, hB.coord, hB.indep⟩

/-- At a deterministic time, the future increments form a Brownian motion
started at zero and are independent of the whole past. -/
theorem Sandpile.Continuum.IsBrownian.shift_independent
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {x : Sandpile.Continuum.Space d} {B : ℝ≥0 → Ω → Sandpile.Continuum.Space d}
    {P : Measure Ω} (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (s : ℝ≥0) :
    LatticeProb.IsBrownianSpace d 0 (fun t ω => B (s + t) ω - B s ω) P ∧
      IndepFun (fun ω t => B (s + t) ω - B s ω)
        (fun ω (t : Set.Iic s) => B t ω) P :=
  ⟨hB.toIsBrownianSpace.shift s,
    hB.toIsBrownianSpace.indepFun_shift (fun t => (hm t).measurable) s⟩

/-- The future increment path at a Brownian stopping time is independent of the
past at that time and has the law of the centred Brownian path. -/
theorem Sandpile.Continuum.IsBrownian.restart
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {x : Sandpile.Continuum.Space d} {B : ℝ≥0 → Ω → Sandpile.Continuum.Space d}
    {P : Measure Ω} (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    (τ : Ω → ℝ≥0) (hτ : Sandpile.Continuum.IsBrownianStopping B τ)
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E)
    (Γ : Set (ℝ≥0 → Sandpile.Continuum.Space d)) (hΓ : MeasurableSet Γ) :
    P (E ∩ {ω | (fun t => B (τ ω + t) ω - B (τ ω) ω) ∈ Γ}) =
      P E * P {ω | (fun t => B t ω - B 0 ω) ∈ Γ} := by
  exact hB.toIsBrownianSpace.restart hm hc τ hτ E hE Γ hΓ
