import Sandpile.Support.PlanarLaw
import Sandpile.Continuum.Kernel

/-! # Continuum planar crossing vocabulary

Continuum planar vocabulary for the fixed-scale crossing argument
(`sandpile.tex:2105-2135`): the symmetries of a continuous planar random
field, positive association of its law, and the rectangle crossing
events, in the shape of the lattice vocabulary of
`Sandpile/Support/PlanarLaw.lean`.

The paper's continuum RSW input (Köhler-Schindler and Tassion, Theorem 1
and Comment 1, cited at `sandpile.tex:2218`) is stated for a stationary
planar process with sign symmetry, rotation by $\pi/2$ and coordinate
reflection invariance, and positive association.  The field is a random
continuous function on the plane; the crossing events are the compact
connected crossings of `Sandpile.Frozen.FixedScaleCrossings.Crosses`.
-/

open MeasureTheory Set

namespace Sandpile.Continuum

/-- Translation of a continuous planar field by `v`. -/
noncomputable def fieldShift (v : Space 2) (X : Space 2 → ℝ) : Space 2 → ℝ :=
  fun u => X (u + v)

/-- Coordinate interchange of a continuous planar field. -/
noncomputable def fieldTranspose (X : Space 2 → ℝ) : Space 2 → ℝ :=
  fun u => X (WithLp.toLp 2 (fun i : Fin 2 => u ⟨1 - (i : ℕ), by omega⟩))

/-- First-coordinate reflection of a continuous planar field. -/
noncomputable def fieldReflect (X : Space 2 → ℝ) : Space 2 → ℝ :=
  fun u => X (WithLp.toLp 2 (fun i : Fin 2 => if (i : ℕ) = 0 then -(u 0) else u i))

/-- Sign flip of a continuous planar field. -/
noncomputable def fieldNegate (X : Space 2 → ℝ) : Space 2 → ℝ :=
  fun u => -X u

/-- The law of a continuous planar field is stationary and invariant under
coordinate interchange, first-coordinate reflection, and sign flip. -/
def IsSymmetricContinuumLaw (μ : Measure (Space 2 → ℝ)) : Prop :=
  (∀ v : Space 2, MeasurePreserving (fieldShift v) μ μ) ∧
    MeasurePreserving fieldTranspose μ μ ∧ MeasurePreserving fieldReflect μ μ ∧
    MeasurePreserving fieldNegate μ μ

/-- The law of a continuous planar field is positively associated:
increasing events correlate nonnegatively. -/
def IsAssociatedContinuumLaw (μ : Measure (Space 2 → ℝ)) : Prop :=
  ∀ A B : Set (Space 2 → ℝ), IsUpperSet A → IsUpperSet B → MeasurableSet A →
    MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B)

end Sandpile.Continuum

namespace Sandpile.Frozen.FixedScaleCrossings

/-- The identification of `sandpile.tex:2081`: `u\in\R^2` is read as `(u,0)` in
`ℝ^3`.  For `d = 2` this is the identity. -/
def planePoint {d : ℕ} (u : Sandpile.Continuum.Space 2) : Sandpile.Continuum.Space d :=
  WithLp.toLp 2 (fun i : Fin d => if h : (i : ℕ) < 2 then u ⟨(i : ℕ), h⟩ else 0)

/-- The kernel of `\mathcal X_s(u)` in `sandpile.tex:2076-2088`: the Green
function of the ball of radius `s` about `u`, in dimension two and in dimension
three. -/
noncomputable def ballKernel (d : ℕ) (s : ℝ) (u : Sandpile.Continuum.Space 2)
    (z : Sandpile.Continuum.Space d) : ℝ :=
  if ‖(planePoint u : Sandpile.Continuum.Space d) - z‖ < s then
    (if d = 2 then
      (1 / (2 * Real.pi)) * Real.log (s / ‖(planePoint u : Sandpile.Continuum.Space d) - z‖)
    else
      (1 / (4 * Real.pi)) *
        (1 / ‖(planePoint u : Sandpile.Continuum.Space d) - z‖ - 1 / s))
  else 0

/-- The planar ball field `\mathcal X_s` of `sandpile.tex:2076-2088`. -/
noncomputable def ballField {Ω : Type*} (d : ℕ)
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ) (s : ℝ)
    (u : Sandpile.Continuum.Space 2) (ω : Ω) : ℝ :=
  W (ballKernel d s u) ω

/-- The axis-parallel rectangle with corners `a` and `b`. -/
def rectSet (a b : Fin 2 → ℝ) : Set (Sandpile.Continuum.Space 2) :=
  {p | ∀ i : Fin 2, a i ≤ p i ∧ p i ≤ b i}

/-- `S` crosses the rectangle with corners `a`, `b` in the coordinate direction
`i`, in the sense of `sandpile.tex:2112-2118`: the set contains a compact
connected subset of the rectangle joining the two opposite sides. -/
def Crosses (a b : Fin 2 → ℝ) (i : Fin 2) (S : Set (Sandpile.Continuum.Space 2)) : Prop :=
  ∃ Γ : Set (Sandpile.Continuum.Space 2), Γ ⊆ S ∩ rectSet a b ∧ IsCompact Γ ∧ IsConnected Γ ∧
    (∃ p ∈ Γ, p i = a i) ∧ (∃ q ∈ Γ, q i = b i)

end Sandpile.Frozen.FixedScaleCrossings

namespace Sandpile.Continuum
/-- The horizontal crossing event of the rectangle with corners `a`, `b`
at `level`: the superlevel set `{X ≥ level}` crosses in the first
coordinate direction. -/
def crossingEvent (a b : Fin 2 → ℝ) (level : ℝ) : Set (Space 2 → ℝ) :=
  {X | Sandpile.Frozen.FixedScaleCrossings.Crosses a b 0 {u | level ≤ X u}}

/-- The vertical crossing event of the rectangle with corners `a`, `b`
at `level`: the superlevel set `{X ≥ level}` crosses in the second
coordinate direction. -/
def crossingEventVert (a b : Fin 2 → ℝ) (level : ℝ) : Set (Space 2 → ℝ) :=
  {X | Sandpile.Frozen.FixedScaleCrossings.Crosses a b 1 {u | level ≤ X u}}

end Sandpile.Continuum