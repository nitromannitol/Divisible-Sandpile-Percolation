import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# One-Coordinate Split of a Finite Product Measure

A measure-preserving one-coordinate split of a finite product
and the corresponding conditional integral formula.

This module builds the measurable equivalence `measurableFunSplitAt i` peeling
one coordinate `i` off a product type `I → α`, shows it carries the product
measure `Measure.pi μ` to the product of `μ i` with the product measure over
the remaining coordinates, and deduces a Fubini-type formula expressing an
integral over `Measure.pi μ` as an iterated integral over the split.
-/

open MeasureTheory Set

noncomputable section

namespace Sandpile

variable {I α : Type*} [DecidableEq I] [MeasurableSpace α]

/-- The measurable equivalence splitting a function `I → α` into its `i`-th coordinate and the
remaining coordinates, built from `Equiv.funSplitAt` with measurability of both directions
checked coordinatewise. -/
def measurableFunSplitAt (i : I) : (I → α) ≃ᵐ α × ({j : I // j ≠ i} → α) where
  toEquiv := Equiv.funSplitAt i α
  measurable_toFun := (measurable_pi_apply i).prodMk (measurable_pi_iff.mpr
    (fun j => measurable_pi_apply (j : I)))
  measurable_invFun := by
    apply measurable_pi_iff.mpr
    intro j
    by_cases h : j = i
    · subst j
      simpa [Equiv.funSplitAt, Equiv.piSplitAt] using
        (measurable_fst : Measurable (fun p : α × ({j : I // j ≠ i} → α) => p.1))
    · simpa [Equiv.funSplitAt, Equiv.piSplitAt, h, Function.comp_def] using
        (measurable_pi_apply (⟨j, h⟩ : {j : I // j ≠ i})).comp measurable_snd

/-- `measurableFunSplitAt i` sends `x` to the pair of its `i`-th coordinate and the function of
its remaining coordinates, unfolding directly to the underlying `Equiv.funSplitAt`. -/
@[simp] lemma measurableFunSplitAt_apply (i : I) (x : I → α) :
    measurableFunSplitAt i x = (x i, fun j : {j : I // j ≠ i} => x j) := rfl

/-- The inverse of `measurableFunSplitAt i`, evaluated back at coordinate `i`, recovers the first
component `p.1` of the split pair. -/
@[simp] lemma measurableFunSplitAt_symm_self (i : I)
    (p : α × ({j : I // j ≠ i} → α)) : (measurableFunSplitAt i).symm p i = p.1 := by
  simp [measurableFunSplitAt, Equiv.funSplitAt, Equiv.piSplitAt]

/-- The inverse of `measurableFunSplitAt i`, evaluated at any coordinate `j ≠ i`, recovers the
corresponding value `p.2 j` of the second component. -/
@[simp] lemma measurableFunSplitAt_symm_other (i : I)
    (p : α × ({j : I // j ≠ i} → α)) (j : {j : I // j ≠ i}) :
    (measurableFunSplitAt i).symm p j = p.2 j := by
  simp [measurableFunSplitAt, Equiv.funSplitAt, Equiv.piSplitAt, j.property]

/-- `measurableFunSplitAt i` carries the finite product measure `Measure.pi μ` to the product of
`μ i` with the product measure over the remaining coordinates, proved by matching the measures of
rectangles via `Fintype.prod_eq_mul_prod_subtype_ne`. -/
lemma measurePreserving_funSplitAt [Fintype I] (μ : I → Measure α)
    [∀ i, SigmaFinite (μ i)] (i : I) :
    MeasurePreserving (measurableFunSplitAt (α := α) i) (Measure.pi μ)
      ((μ i).prod (Measure.pi fun j : {j : I // j ≠ i} => μ j)) := by
  let e := (measurableFunSplitAt (α := α) i).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (Measure.pi_eq fun s _ => ?_).symm⟩
  have hp : e ⁻¹' pi univ s = s i ×ˢ pi univ (fun j : {j : I // j ≠ i} => s j) := by
    ext p
    simp only [mem_preimage, mem_pi, mem_univ, forall_const, mem_prod]
    constructor
    · intro h
      exact ⟨by simpa [e] using h i, fun j => by simpa [e] using h j⟩
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst j
        simpa [e] using h1
      · change (measurableFunSplitAt i).symm p j ∈ s j
        rw [measurableFunSplitAt_symm_other i p (⟨j, hj⟩ : {j : I // j ≠ i})]
        exact h2 ⟨j, hj⟩
  rw [e.map_apply, hp, Measure.prod_prod, Measure.pi_pi]
  exact (Fintype.prod_eq_mul_prod_subtype_ne (fun j => μ j (s j)) i).symm

/-- Fubini for the finite product measure along the split at coordinate `i`: an integral of an
integrable `f` over `Measure.pi μ` equals the iterated integral over the remaining coordinates of
the integral over `μ i`, obtained by transporting via `measurePreserving_funSplitAt` and applying
`integral_prod_symm`. -/
lemma integral_pi_splitAt [Fintype I] (μ : I → Measure α)
    [∀ i, SigmaFinite (μ i)] (i : I) {f : (I → α) → ℝ}
    (hf : Integrable f (Measure.pi μ)) :
    (∫ x, f x ∂Measure.pi μ) =
      ∫ r, ∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂μ i
        ∂Measure.pi (fun j : {j : I // j ≠ i} => μ j) := by
  have hm := (measurePreserving_funSplitAt μ i).symm
  rw [← hm.integral_comp' f]
  apply integral_prod_symm
  exact (hm.integrable_comp_emb (measurableFunSplitAt i).symm.measurableEmbedding).mpr hf

end Sandpile
