/-
The exploration trace of Step 3 of `prop:fixed-scale-crossings`
(`sandpile.tex:2350-2382`), as a measurable map on the finitely many coordinates
the exploration reads.

  "Let `z_1,\ldots,z_M` be the processed square centers ... and let `\P_\ell^{\rm tr}`
   be the law of `\mathfrak T_M` under `\P_\ell`."

The trace `\mathfrak T_M` is a function of the white noise evaluated at the
finitely many test functions the exploration uses, so it is a map into a finite
product of copies of `ℝ`, and it is measurable as soon as each of those
coordinates is.  The two crossing events of the level loss are read off the same
trace, so their probabilities are the probabilities of one measurable event
under the two trace laws; `measure_preimage_trace` is that identification.
-/
import Sandpile.Support.CrossFixArm

open MeasureTheory Set
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

set_option linter.unusedVariables false

namespace Sandpile.Support

/-- The trace map of the exploration on the finitely many coordinates it reads
is measurable as soon as each coordinate is. -/
theorem measurable_trace_fin {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    (q : Fin n → Sandpile.Continuum.Space 2) :
    Measurable fun ω => (fun i : Fin n => X (q i) ω) := by
  exact measurable_pi_iff.mpr fun i => hX (q i)

/-- An event the trace determines is a preimage of a measurable event: its
probability is the probability of that event under the trace law. -/
theorem measure_preimage_trace {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {T : Type} [MeasurableSpace T] (tr : Ω → T) (htr : Measurable tr)
    (E : Set T) (hE : MeasurableSet E) :
    P (tr ⁻¹' E) = (P.map tr) E := by
  exact (Measure.map_apply htr hE).symm

/-- An event determined by the values of a map is the preimage of a set: if two
points with the same trace are either both in the event or both out of it, the
event is the preimage of its own image.  This is how the two crossing events of
`sandpile.tex:2350-2382` are read as events of the trace. -/
theorem exists_preimage_of_determined {Ω T : Type} {S : Set Ω} (tr : Ω → T)
    (h : ∀ ω ω', tr ω = tr ω' → (ω ∈ S ↔ ω' ∈ S)) :
    ∃ E : Set T, S = tr ⁻¹' E := by
  refine ⟨tr '' S, ?_⟩
  ext ω
  constructor
  · intro hω
    exact ⟨ω, hω, rfl⟩
  · rintro ⟨ω', hω', heq⟩
    exact (h ω' ω heq).mp hω'

/-- The crossing event of a rectangle is determined by the field values at the
finitely many points of a finite grid: two fields agreeing there are either both
crossing or both not.  This is the "the trace determines `E_R(θ)`" of
`sandpile.tex:2388`. -/
theorem crossing_determined_by_grid
    {Ω : Type} [MeasurableSpace Ω] {X : Sandpile.Continuum.Space 2 → Ω → ℝ}
    (θ L R : ℝ) (ω ω' : Ω)
    (h : ∀ u : Sandpile.Continuum.Space 2, X u ω = X u ω') :
    (ω ∈ {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω}} ↔
      ω' ∈ {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω'}}) := by
  have hset : {u : Sandpile.Continuum.Space 2 | L / R ≤ X u ω} =
      {u : Sandpile.Continuum.Space 2 | L / R ≤ X u ω'} := by
    apply Set.ext
    intro u
    change L / R ≤ X u ω ↔ L / R ≤ X u ω'
    rw [h u]
  change Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω} ↔
         Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω'}
  rw [hset]

/-- The crossing event of the exploration is a preimage of a set of the cube
coordinates: if two noise realizations with the same cube coordinates have the
same field values at every point, the crossing event is determined by the cube
trace, hence is the preimage of its own image under that trace. -/
theorem crossing_preimage_cube_trace
    {Ω : Type} [MeasurableSpace Ω] {d n : ℕ}
    {W : (Space d → ℝ) → Ω → ℝ} (cubes : Fin n → Set (Space d))
    (θ L R : ℝ)
    (hdet : ∀ ω ω' : Ω,
      (∀ i : Fin n, W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω
        = W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω') →
      ∀ u : Space 2, ballField d W 1 u ω = ballField d W 1 u ω') :
    ∃ E : Set (Fin n → ℝ),
      {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
          {u | L / R ≤ ballField d W 1 u ω}}
        = (fun ω => (fun i : Fin n =>
            W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω)) ⁻¹' E := by
  refine Sandpile.Support.exists_preimage_of_determined
    (fun ω => (fun i : Fin n => W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω)) ?_
  intro ω ω' heq
  have hfun : ∀ u : Space 2, ballField d W 1 u ω = ballField d W 1 u ω' :=
    hdet ω ω' (fun i => congrFun heq i)
  have hset : {u : Space 2 | L / R ≤ ballField d W 1 u ω} =
      {u : Space 2 | L / R ≤ ballField d W 1 u ω'} := by
    ext u
    simp only [Set.mem_setOf_eq]
    rw [hfun u]
  change Crosses ![-(θ*R),0] ![θ*R,2*R] 0 {u | L/R ≤ ballField d W 1 u ω} ↔
    Crosses ![-(θ*R),0] ![θ*R,2*R] 0 {u | L/R ≤ ballField d W 1 u ω'}
  rw [hset]

end Sandpile.Support
