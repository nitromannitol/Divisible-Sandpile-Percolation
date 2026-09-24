/-
Pinsker's inequality, cited by name in Step 3 of the proof of
`prop:fixed-scale-crossings` at `sandpile.tex:2390`:

  "Since `𝔗_M` determines `E_R(θ)`, Pinsker's inequality gives
   `P_{L/R}(E_R(θ)) - P_0(E_R(θ)) ≤ (L/(2𝔪R))√(E_0 𝒩)`."

The inequality bounds the total variation distance of two probability measures
by the square root of half their relative entropy.  Only the form the paper uses
is recorded: on a single measurable set, and against an upper bound `δ` for the
relative entropy rather than against the relative entropy itself.  That form
carries no junk value: a relative entropy of `∞` cannot satisfy the hypothesis,
since `ENNReal.ofReal δ` is finite, so the conclusion is never asserted through a
`toReal` that has collapsed.

The relative entropy is Mathlib's `InformationTheory.klDiv`, which is `∞` unless
the first measure is absolutely continuous with respect to the second with
integrable log-likelihood ratio, and is otherwise
`∫ log(dμ/dν) dμ + ν(univ) - μ(univ)`, the paper's `D(μ‖ν)` for probability
measures.

It is a classical inequality, it is not proved in the paper, and it belongs in
the shared library; it is requested there, and this Prop is discharged when it
lands.
-/
import Sandpile.Support.CrossField
import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory Set

-- FROZEN-STATEMENT-BEGIN
/-- Pinsker's inequality on one measurable set, in the bounded form the level
loss uses.  Assumed, not proved. -/
def Sandpile.External.Pinsker : Prop :=
  ∀ (T : Type) [MeasurableSpace T] (μ ν : Measure T) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (A : Set T), MeasurableSet A →
    ∀ δ : ℝ, 0 ≤ δ → InformationTheory.klDiv μ ν ≤ ENNReal.ofReal δ →
      |μ.real A - ν.real A| ≤ Real.sqrt (δ / 2)
-- FROZEN-STATEMENT-END
