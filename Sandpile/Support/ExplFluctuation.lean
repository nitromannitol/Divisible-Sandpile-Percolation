import Sandpile.Law
import Sandpile.Continuum.Membrane

/-!
# Diffusive Odometer Fluctuation

The diffusively rescaled odometer fluctuation of Theorem 1.3(iii)(c)-(d),
`sandpile.tex:275-296`, paired with a test function.

It lives in its own module because it is a definition, not a theorem: the
support chain that proves the two parts of Theorem 1.3 it appears in must be
able to name it without importing the file that states those parts.
-/

namespace Sandpile.Continuum

/-- The diffusively rescaled odometer fluctuation of Theorem 1.3(iii)(c)-(d),
paired with a test function: the functional
`\varphi\mapsto R^{(d-4)/2}\bigl(u_{\lfloor TR^2\rfloor}-\E u_{\lfloor TR^2\rfloor}(0)\bigr)^{(R)}
(\varphi)`, where `P` supplies the mean `\E u_t(0)`. -/
noncomputable def diffusiveFluctuation {d : ℕ} (P : MeasureTheory.Measure (Site d → ℝ))
    (T R : ℝ) (σ : Site d → ℝ) (φ : Space d → ℝ) : ℝ :=
  R ^ (((d : ℝ) - 4) / 2) *
    latticePairing R
      (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x - Sandpile.meanOdometer P ⌊T * R ^ 2⌋₊) φ

end Sandpile.Continuum
