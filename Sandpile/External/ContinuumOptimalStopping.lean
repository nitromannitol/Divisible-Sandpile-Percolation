import Sandpile.Continuum.Stopping

/-!
# The finite-horizon optimal-stopping theorem, cited

`snellValue` and `attainable` set up the vocabulary for the finite-horizon Markovian
optimal-stopping theorem of Peskir and Shiryaev (*Optimal Stopping and Free-Boundary Problems*,
2006, Chapter I, Section 2, Theorem 2.2): `snellValue` is the value
`V(t,x) = sup_{0 ≤ τ ≤ t} E_x G(t-τ, B_τ)` of the stopping problem with gain `G` and horizon `t`,
and `attainable` is the set of payoffs achieved by some admissible stopping time.
`Sandpile.External.ContinuumOptimalStopping` asserts, for Brownian motion on `ℝ^d` and a gain of
polynomial growth, that the value process has a right-continuous modification, that the first
entry time into the contact set is an optimal stopping time attaining the value, and that every
optimal stopping time dominates it; it is cited rather than proved.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Snell

/-- The value of the finite-horizon stopping problem with gain `G` and horizon
`t`, `V(t,x) = sup_{0 ≤ τ ≤ t} E_x G(t - τ, B_τ)`, for the Brownian motion `B`
started at `x`.  The paper's `𝒟_h(t,x)` is this value at the gain `G = -h`. -/
noncomputable def snellValue {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d) (P : Measure Ω)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ) (t : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ ∧
    (∀ ω, (τ ω : ℝ) ≤ t) ∧ a = ∫ ω, G (t - τ ω) (B (τ ω) ω) ∂P}

/-- The payoffs attainable at horizon `t` by an admissible stopping time. -/
def attainable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d) (P : Measure Ω)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ) (t : ℝ) : Set ℝ :=
  {a : ℝ | ∃ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ ∧
    (∀ ω, (τ ω : ℝ) ≤ t) ∧ a = ∫ ω, G (t - τ ω) (B (τ ω) ω) ∂P}

end Sandpile.External.Snell

-- FROZEN-STATEMENT-BEGIN
/-- The finite-horizon optimal-stopping theorem for Brownian motion on `ℝ^d`
with a continuous gain of polynomial growth, in the form cited at
`sandpile.tex:1099` (Peskir and Shiryaev, Theorem 2.2), on a probability space
`Ω` carrying such a Brownian family.  Assumed, not proved. -/
def Sandpile.External.ContinuumOptimalStopping (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (d : ℕ) (T : ℝ), 0 < T →
    ∀ G : ℝ → Sandpile.Continuum.Space d → ℝ,
      ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
        (Set.Icc 0 T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) →
      (∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ y : Sandpile.Continuum.Space d, |G t y| ≤ C * (1 + ‖y‖) ^ k) →
      ∀ x : Sandpile.Continuum.Space d,
        ∀ (P : Measure Ω) [IsProbabilityMeasure P]
          (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d),
          (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) P) →
          ∃ M : ℝ≥0 → Ω → ℝ,
            (∀ s : ℝ≥0, Measurable (M s)) ∧
            (∀ s : ℝ≥0, (s : ℝ) ≤ T →
              M s =ᵐ[P] fun ω =>
                Sandpile.External.Snell.snellValue (B (B x s ω)) P G (T - (s : ℝ))) ∧
            (∀ (ω : Ω) (s : ℝ≥0),
              ContinuousWithinAt (fun r : ℝ≥0 => M r ω) (Set.Ici s) s) ∧
            ∃ τ : Ω → ℝ≥0,
              (∀ ω : Ω, IsLeast {s : ℝ≥0 | (s : ℝ) ≤ T ∧
                M s ω = G (T - (s : ℝ)) (B x s ω)} (τ ω)) ∧
              Sandpile.Continuum.IsBrownianStopping (B x) τ ∧
              IsGreatest (Sandpile.External.Snell.attainable (B x) P G T)
                (∫ ω, G (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P) ∧
              ∀ τ' : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) τ' →
                (∀ ω : Ω, (τ' ω : ℝ) ≤ T) →
                (∫ ω, G (T - (τ' ω : ℝ)) (B x (τ' ω) ω) ∂P) =
                  Sandpile.External.Snell.snellValue (B x) P G T →
                ∀ᵐ ω ∂P, τ ω ≤ τ' ω
-- FROZEN-STATEMENT-END
