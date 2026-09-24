/-
The rescaled linear field `Z_R` and its standard interpolation `Z_R^{\rm lin}`
of `sandpile.tex:1833-1839`, the objects of
`prop:dlt4-heat-potential-invariance`.

These two definitions are the running-text definitions the proposition is about;
they are kept here, rather than beside the frozen statement, so that the
support modules that prove the proposition can use them without importing the
frozen statement itself.  The fully qualified names are unchanged.
-/
import Sandpile.Walk
import Sandpile.Continuum.Kernel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Frozen.HeatPotentialInvariance

/-- The value of `Z_R` at a mesh point of `R^{-2}ℤ_+ × R^{-1}ℤ^d`, from
`sandpile.tex:1834-1836`:
`Z_R(r,w) = R^{d/2-2}\sum_{z} g_{\lfloor R^2r\rfloor}(\lfloor Rw\rfloor,z)\zeta(z)`,
here with the time index `k = ⌊R^2 r⌋` and the space index `z = ⌊Rw⌋` given
directly. -/
noncomputable def meshValue (d : ℕ) (R : ℝ) (ζ : Sandpile.Site d → ℝ) (k : ℕ)
    (z : Sandpile.Site d) : ℝ :=
  R ^ ((d : ℝ) / 2 - 2) * ∑' y : Sandpile.Site d, Sandpile.greenTime d k z y * ζ y

/-- `Z_R^{\rm lin}` of `sandpile.tex:1838-1839`: "the standard interpolation of
$Z_R$ from the mesh $R^{-2}\Z_+\times R^{-1}\Z^d$", taken to be multilinear
interpolation on the cells of that mesh. -/
noncomputable def linInterp (d : ℕ) (R : ℝ) (ζ : Sandpile.Site d → ℝ) (r : ℝ)
    (w : Sandpile.Continuum.Space d) : ℝ :=
  let a : ℕ := ⌊R ^ 2 * r⌋₊
  let s : ℝ := R ^ 2 * r - (a : ℝ)
  let b : Sandpile.Site d := fun i => ⌊R * w i⌋
  let t : Fin d → ℝ := fun i => R * w i - (b i : ℝ)
  ∑ ε : Fin d → Bool,
    (∏ i : Fin d, if ε i then t i else 1 - t i) *
      ((1 - s) * meshValue d R ζ a (fun i => b i + if ε i then 1 else 0) +
        s * meshValue d R ζ (a + 1) (fun i => b i + if ε i then 1 else 0))

end Sandpile.Frozen.HeatPotentialInvariance
