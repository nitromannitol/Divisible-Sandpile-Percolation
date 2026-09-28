import Sandpile.Support.CrossFKG

/-!
# The FKG circuit probability of Step 1

The circuit probability of Step 1 of `prop:fixed-scale-crossings` (`sandpile.tex:2213-2235`):
the FKG inequality applied to the four sides of a circuit, each of which has probability at
least `c`.

  "`eq:fixed-scale-zero-crossing` and the FKG inequality give a uniformly positive probability
   of a `{𝒳₁ ≥ 0}` circuit in every annulus."

The four sides are the crossing events of the four rectangles of the annulus; they are
increasing events of the field, so FKG (`fkg_prod_const_le`) bounds the probability of their
intersection below by the product of their probabilities, giving `c ^ 4` for the circuit
(`circuit_probability`, `circuit_probability_annulus`).
-/

open MeasureTheory Set

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- FKG for a finite family of upper events each of probability at least `c`:
the probability of the intersection is at least `c ^ card`. -/
theorem fkg_prod_const_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hmeas : ∀ u, Measurable (X u))
    (hass : Sandpile.Continuum.IsAssociatedField P X) {ι : Type} [DecidableEq ι]
    (A : ι → Set Ω) (hA : ∀ i, UpperEvent X (A i)) (s : Finset ι) {c : ℝ}
    (hc : 0 ≤ c) (hcA : ∀ i, c ≤ P.real (A i)) :
    c ^ s.card ≤ P.real (⋂ i ∈ s, A i) := by
  have hprod : c ^ s.card ≤ ∏ i ∈ s, P.real (A i) := by
    have h1 : ∏ i ∈ s, c ≤ ∏ i ∈ s, P.real (A i) :=
      Finset.prod_le_prod (fun i _ => hc) (fun i _ => hcA i)
    rwa [Finset.prod_const] at h1
  exact le_trans hprod (Sandpile.Support.fkg_prod_le hmeas hass A hA s)

/-- The circuit probability of Step 1 of `prop:fixed-scale-crossings`
(`sandpile.tex:2229-2232`): the four sides of a circuit are increasing events of
the field, each of probability at least `c`, so FKG bounds the probability of
the circuit below by `c ^ 4`.  The four sides are the crossing events of the
four rectangles of the annulus `B(x,4ρ) \ B(x,ρ)`; that they are four is the
geometry, and it enters here only as `Fin 4`. -/
theorem circuit_probability {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Sandpile.Continuum.Space 2 → Ω → ℝ}
    (hmeas : ∀ u, Measurable (X u)) (hass : Sandpile.Continuum.IsAssociatedField P X)
    (a b : Fin 4 → Fin 2 → ℝ) (dir : Fin 4 → Fin 2) (lev : Fin 4 → ℝ) {c : ℝ}
    (hc : 0 ≤ c)
    (hcA : ∀ i, c ≤ P.real (crossApprox X (a i) (b i) (dir i) (lev i))) :
    c ^ 4 ≤ P.real (⋂ i, crossApprox X (a i) (b i) (dir i) (lev i)) := by
  have h := fkg_prod_const_le (P := P) (X := X) hmeas hass
    (fun i => crossApprox X (a i) (b i) (dir i) (lev i))
    (fun i => upperEvent_crossApprox (X := X) (a i) (b i) (dir i) (lev i)) Finset.univ hc
    (fun i => hcA i)
  simpa using h


/-- The circuit probability of the four sides of an annulus, from the FKG
inequality: the four crossing events are increasing events of the field, each of
probability at least `c`, so their intersection has probability at least `c ^ 4`. -/
theorem circuit_probability_annulus {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Sandpile.Continuum.Space 2 → Ω → ℝ}
    (hmeas : ∀ u, Measurable (X u)) (hass : Sandpile.Continuum.IsAssociatedField P X)
    (a b : Fin 4 → Fin 2 → ℝ) (dir : Fin 4 → Fin 2) (lev : Fin 4 → ℝ) {c : ℝ}
    (hc : 0 ≤ c)
    (hcA : ∀ i, c ≤ P.real (crossApprox X (a i) (b i) (dir i) (lev i))) :
    c ^ 4 ≤ P.real (⋂ i, crossApprox X (a i) (b i) (dir i) (lev i)) := by
  exact Sandpile.Support.circuit_probability hmeas hass a b dir lev hc hcA

end Sandpile.Support
