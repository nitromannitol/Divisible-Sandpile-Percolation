/-
The two objects of `ssec:scaling-dlt4` that the statements of that subsection
read: the rescaled odometer of `sandpile.tex:1817-1821` and the continuum value
`𝒰 = 𝒰_Z` of `eq:continuum-membrane-stopping-value`, quoted at
`sandpile.tex:1824-1825`.

They are named here, and not in the file of a statement that uses them, so that
the modules proving those statements can name them without importing the
statement's own file.
-/
import Sandpile.Continuum.Stopping
import Sandpile.Law

open MeasureTheory
open scoped NNReal

namespace Sandpile.Continuum

/-- The rescaled odometer of `sandpile.tex:1817-1821`: "For $T>0,\ x\in\R^d$,
define the rescaled odometer by
$\mathcal U_R(T,x)\coloneqq R^{-(2-d/2)}u_{\lfloor R^2T\rfloor}(\lfloor Rx\rfloor)$,
with the floor taken coordinatewise." -/
noncomputable def rescaledOdometer (d : ℕ) (R T : ℝ) (x : Sandpile.Continuum.Space d)
    (σ : Sandpile.Site d → ℝ) : ℝ :=
  R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ (fun i => ⌊R * x i⌋)

/-- The continuum value `𝒰 = 𝒰_Z` of `eq:continuum-membrane-stopping-value`,
"$\mathcal U_Z(T,x)=Z(T,x)+\sup_{\tau\leq T}\mathbf E_x^{\rm BM}[-Z(T-\tau,B_\tau)]$",
with `Z` the continuous version of the Gaussian heat potential of
`eq:dlt4-linear-gaussian-potential`, frozen at the sample point `ω` of the
white-noise space. -/
noncomputable def continuumValue {ΩW ΩB : Type*} [MeasurableSpace ΩB] (d : ℕ)
    (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (PB : Measure ΩB) (T : ℝ) (x : Sandpile.Continuum.Space d) (ω : ΩW) : ℝ :=
  Sandpile.Continuum.brownianValue (B x) PB (fun t z => Z t z ω) T x

end Sandpile.Continuum
