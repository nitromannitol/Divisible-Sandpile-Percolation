import Sandpile.Support.KillRep
import Sandpile.Support.ExplKilledValue
import Sandpile.Frozen.MeanLocalization
import Sandpile.External.LocalCLT

/-!
# Killed optimal-stopping value stability on a cube

External input: the stability of KILLED optimal-stopping values under uniform
convergence of bounded rewards, together with the invariance principle for the
killed stopped walk, in the form `rem:dlt4-killed-scaling` cites it.

The remark reads (`sandpile.tex:1929-1931`): "The same proof applies, without
change, to the values killed on exiting the lattice box `Q(⌊Ru⌋,R)`."  The step
of that proof which is not a theorem of the paper is the one quoted in
`Sandpile/External/ContStoppingStability.lean`, at `sandpile.tex:1900-1907`:

  "This is the standard stability of optimal-stopping values under uniform
   convergence of bounded rewards and the invariance principle for the stopped
   walk \citep[Theorem~3 and Corollary~4]{CoquetToldo}."

Killing the two problems changes the statement, because the killed value is a
supremum over a smaller family of stopping rules, so the killed form is
registered here as its own input rather than derived from the unkilled one.  The
source is the same: Coquet and Toldo, *Convergence of values in optimal stopping
and convergence of optimal stopping times*, Electronic Journal of Probability 12
(2007), 207-228, Theorem 3 and Corollary 4, applied to the walk killed on exiting
`Q(⌊Rx⌋,R)` and to the motion killed on exiting `x+[-1,1]^d`.  The lattice box
and the cube correspond under the parabolic rescaling: a site `y` lies in
`Q(⌊Rx⌋,R)` exactly when `|y_i-⌊Rx⌋_i| ≤ ⌊R⌋` for every `i`, so `y/R` is within
`1+O(1/R)` of `x` in every coordinate.

This result is assumed here, not proved.

Modelling.  Every clause is the clause of
`Sandpile.External.ContinuumStoppingStability`, with the two values replaced by
their killed forms: the walk value is `Sandpile.killedStoppingSup` on the box
`Sandpile.supBox (⌊Rx⌋) R`, the supremum of `E_{⌊Rx⌋}F(τ,X)` over the walk
stopping times `τ ≤ ⌊R^2T⌋` which have not left the box strictly before they
stop; and the Brownian value is `Sandpile.Continuum.brownianDiscountCube` at
half-width `1`, the supremum over the stopping rules which have not left
`x+[-1,1]^d` strictly before they stop.  The rewards, their uniform bound, the
uniform convergence, the compact set of starting points, the two horizons and the
quantifier order are unchanged.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- Stability of cube-killed optimal-stopping values under uniform convergence of
bounded rewards, together with the invariance principle for the killed stopped
walk (`sandpile.tex:1929-1931` through `sandpile.tex:1900-1907`; Coquet-Toldo,
Theorem 3 and Corollary 4).  Assumed, not proved. -/
def Sandpile.External.CubeStoppingStability : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
      (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB) →
    ∀ T₀ T₁ : ℝ, 0 < T₀ → T₀ ≤ T₁ →
    ∀ K : Set (Sandpile.Continuum.Space d), IsCompact K →
    ∀ G : ℝ → Sandpile.Continuum.Space d → ℝ,
      Continuous (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) →
    ∀ G' : ℝ → ℝ → Sandpile.Continuum.Space d → ℝ,
    ∀ M : ℝ,
      (∀ (s : ℝ) (y : Sandpile.Continuum.Space d), |G s y| ≤ M) →
      (∀ (R s : ℝ) (y : Sandpile.Continuum.Space d), |G' R s y| ≤ M) →
      (∀ ε : ℝ, 0 < ε → ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ R : ℝ, R₁ ≤ R →
        ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ y : Sandpile.Continuum.Space d,
          |G' R s y - G s y| ≤ ε) →
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        ∀ T ∈ Set.Icc T₀ T₁, ∀ x ∈ K,
          |Sandpile.killedStoppingSup (Sandpile.supBox (fun i => ⌊R * x i⌋) R)
                ⌊R ^ 2 * T⌋₊ (fun i => ⌊R * x i⌋)
                (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                  G' R (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                    (Sandpile.External.Lclt.scaledSite R (X k))) -
              Sandpile.Continuum.brownianDiscountCube (B x) PB (fun s y => -G s y) T 1 x| ≤ ε
-- FROZEN-STATEMENT-END
