import Sandpile.Support.CrossBasic

/-!
# Translation invariance of the crossing events

Translation of the planar crossings of `sandpile.tex:2112-2118`, and the
resulting translation invariance of the crossing events for a stationary
planar law (`sandpile.tex:2103-2104`: "The unit-scale field `𝒳_1` is
stationary, sign-symmetric, invariant under rotations by `π/2` and coordinate
reflections").

Stationarity is used in the proof of `prop:fixed-scale-crossings` to compare the
origin-anchored rectangles of the continuum RSW input with the rectangles
`[-θR,θR]×[0,2R]` the proposition is about.  Because the crossing events need
not be measurable, the invariance is proved for the outer measure, which is
possible because a translation of the field is invertible: a measure-preserving
map with a measure-preserving inverse pushes every set, measurable or not, to a
set of the same measure.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A crossing of the translated set is a crossing of the translated rectangle. -/
theorem crosses_translate {v : Sandpile.Continuum.Space 2} {a b : Fin 2 → ℝ} {i : Fin 2}
    {S : Set (Sandpile.Continuum.Space 2)}
    (h : Crosses a b i ((fun u => u + v) ⁻¹' S)) :
    Crosses (fun k => a k + v k) (fun k => b k + v k) i S := by
  obtain ⟨Γ, hsub, hcomp, hconn, ⟨p, hp, hpa⟩, ⟨q, hq, hqb⟩⟩ := h
  have hcont : Continuous (fun u : Sandpile.Continuum.Space 2 => u + v) :=
    continuous_id.add continuous_const
  refine ⟨(fun u => u + v) '' Γ, ?_, hcomp.image hcont,
    hconn.image _ hcont.continuousOn, ⟨p + v, ⟨p, hp, rfl⟩, ?_⟩,
    ⟨q + v, ⟨q, hq, rfl⟩, ?_⟩⟩
  · rintro w ⟨u, huΓ, rfl⟩
    obtain ⟨h1, h2⟩ := hsub huΓ
    refine ⟨h1, ?_⟩
    intro k
    have := h2 k
    simp only [PiLp.add_apply]
    constructor
    · linarith [this.1]
    · linarith [this.2]
  · simp only [PiLp.add_apply, hpa]
  · simp only [PiLp.add_apply, hqb]

/-- The crossing of a rectangle and of its translate are the same event for the
translated field. -/
theorem crossingEvent_shift (v : Sandpile.Continuum.Space 2) (a b : Fin 2 → ℝ)
    (level : ℝ) :
    (Sandpile.Continuum.fieldShift v) ⁻¹' (Sandpile.Continuum.crossingEvent a b level)
      = Sandpile.Continuum.crossingEvent (fun k => a k + v k) (fun k => b k + v k) level := by
  ext X
  constructor
  · intro hX
    exact crosses_translate (v := v) hX
  · intro hX
    have hback := crosses_translate (v := -v)
      (a := fun k => a k + v k) (b := fun k => b k + v k) (i := 0)
      (S := (fun u : Sandpile.Continuum.Space 2 => u + v) ⁻¹' {u | level ≤ X u})
      (by
        have hset : (fun u : Sandpile.Continuum.Space 2 => u + -v) ⁻¹'
            ((fun u : Sandpile.Continuum.Space 2 => u + v) ⁻¹' {u | level ≤ X u})
            = {u | level ≤ X u} := by
          ext u; simp
        rw [hset]
        exact hX)
    have hA : (fun k => a k + v k + (-v) k) = a := by
      funext k; simp only [PiLp.neg_apply]; ring
    have hB : (fun k => b k + v k + (-v) k) = b := by
      funext k; simp only [PiLp.neg_apply]; ring
    rw [hA, hB] at hback
    exact hback

/-- A measure-preserving map with a measure-preserving inverse preserves the
outer measure of every set. -/
theorem measure_preimage_eq_of_inverse {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → α} (hf : MeasurePreserving f μ μ) (hg : MeasurePreserving g μ μ)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x) (s : Set α) :
    μ (f ⁻¹' s) = μ s := by
  let e : MeasurableEquiv α α := ⟨⟨f, g, hgf, hfg⟩, hf.measurable, hg.measurable⟩
  have hemb : MeasurableEmbedding f := e.measurableEmbedding
  have hmap := hemb.map_apply μ s
  rw [hf.map_eq] at hmap
  exact hmap.symm

/-- Translation invariance of the crossing probability for a stationary law. -/
theorem measure_crossingEvent_shift
    (μ : Measure (Sandpile.Continuum.Space 2 → ℝ))
    (hsym : Sandpile.Continuum.IsSymmetricContinuumLaw μ)
    (v : Sandpile.Continuum.Space 2) (a b : Fin 2 → ℝ) (level : ℝ) :
    μ (Sandpile.Continuum.crossingEvent (fun k => a k + v k) (fun k => b k + v k) level)
      = μ (Sandpile.Continuum.crossingEvent a b level) := by
  rw [← crossingEvent_shift v a b level]
  refine measure_preimage_eq_of_inverse (hsym.1 v) (hsym.1 (-v)) ?_ ?_ _
  · intro X
    funext u
    simp [Sandpile.Continuum.fieldShift, add_assoc]
  · intro X
    funext u
    simp [Sandpile.Continuum.fieldShift, add_assoc]

end Sandpile.Support
