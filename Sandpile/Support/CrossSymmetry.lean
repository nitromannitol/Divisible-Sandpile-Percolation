/-
The two symmetries of `sandpile.tex:2103-2104` used in Step 1 of
`prop:fixed-scale-crossings`:

  "The unit-scale field `𝒳_1` is stationary, sign-symmetric, invariant under
   rotations by `π/2` and coordinate reflections",

in the form the crossing events need: the sign flip turns a superlevel crossing
into a sublevel crossing at the opposite level, and the coordinate interchange
turns a left-right crossing of a rectangle into a bottom-top crossing of the
transposed rectangle.  Together with the planar duality these are what give the
square estimate `P(H_{[-R,R]^2}(0)) ≥ 1/2` of `sandpile.tex:2235-2236`.

As everywhere in this chain the crossing events are compared as outer measures;
that is legitimate because both maps are involutions of the space of planar
fields, so each is a measurable equivalence and carries every set, measurable or
not, to a set of the same measure.

WARNING.  The statements below about `μ` of a crossing event on the space of ALL
planar functions are correct but empty: every such outer measure is one
(`Sandpile/Support/CrossVacuity.lean`).  Only the geometry of this module,
`crosses_swap` and the interchange of the two coordinates, is used.  The
symmetry of a field in the form the crossing estimates use it is
`crossingSet_swap` of `Sandpile/Support/CrossDuality.lean`, an equality of
subsets of the probability space carrying the field, and the invariance in law
is `Sandpile.Continuum.IsSymmetricField` of `Sandpile/Support/CrossField.lean`.
-/
import Sandpile.Support.CrossTranslate

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- Interchange of the two coordinates of the plane. -/
def swapPoint (u : Sandpile.Continuum.Space 2) : Sandpile.Continuum.Space 2 :=
  WithLp.toLp 2 (fun i : Fin 2 => u ⟨1 - (i : ℕ), by omega⟩)

/-- Interchange of the two indices. -/
def swapIdx (i : Fin 2) : Fin 2 := ⟨1 - (i : ℕ), by omega⟩

theorem swapPoint_apply (u : Sandpile.Continuum.Space 2) (k : Fin 2) :
    (swapPoint u) k = u (swapIdx k) := rfl

theorem swapIdx_swapIdx (i : Fin 2) : swapIdx (swapIdx i) = i := by
  ext
  simp only [swapIdx]
  omega

theorem swapIdx_zero : swapIdx 0 = 1 := rfl

theorem swapIdx_one : swapIdx 1 = 0 := rfl

theorem swapPoint_swapPoint (u : Sandpile.Continuum.Space 2) :
    swapPoint (swapPoint u) = u := by
  ext k
  rw [swapPoint_apply, swapPoint_apply, swapIdx_swapIdx]

theorem continuous_swapPoint : Continuous swapPoint := by
  unfold swapPoint
  fun_prop

/-- A left-right crossing of the rectangle, for the field read through the
coordinate interchange, is a bottom-top crossing of the transposed rectangle. -/
theorem crosses_swap {a b : Fin 2 → ℝ} {i : Fin 2}
    {S : Set (Sandpile.Continuum.Space 2)}
    (h : Crosses a b i (swapPoint ⁻¹' S)) :
    Crosses (fun k => a (swapIdx k)) (fun k => b (swapIdx k)) (swapIdx i) S := by
  obtain ⟨Γ, hsub, hcomp, hconn, ⟨p, hp, hpa⟩, ⟨q, hq, hqb⟩⟩ := h
  refine ⟨swapPoint '' Γ, ?_, hcomp.image continuous_swapPoint,
    hconn.image _ continuous_swapPoint.continuousOn,
    ⟨swapPoint p, ⟨p, hp, rfl⟩, ?_⟩, ⟨swapPoint q, ⟨q, hq, rfl⟩, ?_⟩⟩
  · rintro w ⟨u, huΓ, rfl⟩
    obtain ⟨h1, h2⟩ := hsub huΓ
    refine ⟨h1, ?_⟩
    intro k
    rw [swapPoint_apply]
    exact h2 (swapIdx k)
  · rw [swapPoint_apply, swapIdx_swapIdx, hpa]
    simp only [swapIdx_swapIdx]
  · rw [swapPoint_apply, swapIdx_swapIdx, hqb]
    simp only [swapIdx_swapIdx]

/-- The coordinate interchange turns the horizontal crossing event of a
rectangle into the vertical crossing event of the transposed rectangle. -/
theorem crossingEvent_transpose (a b : Fin 2 → ℝ) (level : ℝ) :
    (Sandpile.Continuum.fieldTranspose) ⁻¹'
        (Sandpile.Continuum.crossingEvent a b level)
      = Sandpile.Continuum.crossingEventVert (fun k => a (swapIdx k))
          (fun k => b (swapIdx k)) level := by
  ext X
  constructor
  · intro hX
    have h : Crosses a b 0 (swapPoint ⁻¹' {u | level ≤ X u}) := hX
    have hfwd := crosses_swap h
    rw [swapIdx_zero] at hfwd
    exact hfwd
  · intro hX
    have h : Crosses (fun k => a (swapIdx k)) (fun k => b (swapIdx k)) 1
        {u | level ≤ X u} := hX
    have hback := crosses_swap (a := fun k => a (swapIdx k))
      (b := fun k => b (swapIdx k)) (i := 1)
      (S := swapPoint ⁻¹' {u | level ≤ X u})
      (by
        have hset : swapPoint ⁻¹' (swapPoint ⁻¹' {u | level ≤ X u})
            = {u | level ≤ X u} := by
          ext u
          simp only [Set.mem_preimage, swapPoint_swapPoint]
        rw [hset]
        exact h)
    have hA : (fun k => a (swapIdx (swapIdx k))) = a := by
      funext k; rw [swapIdx_swapIdx]
    have hB : (fun k => b (swapIdx (swapIdx k))) = b := by
      funext k; rw [swapIdx_swapIdx]
    rw [hA, hB, swapIdx_one] at hback
    exact hback

/-- The sign flip turns a crossing of the superlevel set at `level` into a
crossing of the sublevel set at `-level`. -/
theorem crossingEvent_negate (a b : Fin 2 → ℝ) (level : ℝ) :
    (Sandpile.Continuum.fieldNegate) ⁻¹'
        (Sandpile.Continuum.crossingEvent a b level)
      = {X : Sandpile.Continuum.Space 2 → ℝ | Crosses a b 0 {u | X u ≤ -level}} := by
  have hset : ∀ X : Sandpile.Continuum.Space 2 → ℝ,
      {u : Sandpile.Continuum.Space 2 | level ≤ -X u} = {u | X u ≤ -level} := by
    intro X
    ext u
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h; linarith
    · intro h; linarith
  ext X
  constructor
  · intro hX
    have h : Crosses a b 0 {u | level ≤ -X u} := hX
    rw [hset X] at h
    exact h
  · intro hX
    have h : Crosses a b 0 {u | X u ≤ -level} := hX
    show Crosses a b 0 {u | level ≤ -X u}
    rw [hset X]
    exact h

/-- The vertical crossing of the transposed rectangle has the same probability
as the horizontal crossing of the rectangle, for a law invariant under the
coordinate interchange. -/
theorem measure_crossingEventVert_transpose
    (μ : Measure (Sandpile.Continuum.Space 2 → ℝ))
    (hsym : Sandpile.Continuum.IsSymmetricContinuumLaw μ) (a b : Fin 2 → ℝ) (level : ℝ) :
    μ (Sandpile.Continuum.crossingEventVert (fun k => a (swapIdx k))
        (fun k => b (swapIdx k)) level)
      = μ (Sandpile.Continuum.crossingEvent a b level) := by
  rw [← crossingEvent_transpose a b level]
  refine measure_preimage_eq_of_inverse hsym.2.1 hsym.2.1 ?_ ?_ _
  · intro X
    funext u
    simp only [Sandpile.Continuum.fieldTranspose]
    exact congrArg X (swapPoint_swapPoint u)
  · intro X
    funext u
    simp only [Sandpile.Continuum.fieldTranspose]
    exact congrArg X (swapPoint_swapPoint u)

/-- The sublevel crossing at `-level` has the same probability as the superlevel
crossing at `level`, for a sign-symmetric law. -/
theorem measure_crossing_sublevel
    (μ : Measure (Sandpile.Continuum.Space 2 → ℝ))
    (hsym : Sandpile.Continuum.IsSymmetricContinuumLaw μ) (a b : Fin 2 → ℝ) (level : ℝ) :
    μ {X : Sandpile.Continuum.Space 2 → ℝ | Crosses a b 0 {u | X u ≤ -level}}
      = μ (Sandpile.Continuum.crossingEvent a b level) := by
  rw [← crossingEvent_negate a b level]
  refine measure_preimage_eq_of_inverse hsym.2.2.2 hsym.2.2.2 ?_ ?_ _
  · intro X
    funext u
    simp [Sandpile.Continuum.fieldNegate]
  · intro X
    funext u
    simp [Sandpile.Continuum.fieldNegate]

end Sandpile.Support
