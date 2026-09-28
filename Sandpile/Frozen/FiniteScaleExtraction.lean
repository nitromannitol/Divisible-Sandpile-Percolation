import Sandpile.Continuum.WhiteNoise
import Sandpile.External.ContinuumRSW
import Sandpile.External.PittGaussianFKG
import Sandpile.External.GaussianLawCovarianceProved
import Sandpile.Support.LimUnconditional
import Sandpile.Support.LimScaleZeroOne

/-!
# Finite-scale extraction from fixed-scale crossings

This file proves the frozen statement of `lem:finite-scale-extraction` (`sandpile.tex:2451-2461`):
given `N ≥ 1` axis-parallel rectangles with a prescribed coordinate crossing direction each, for
every `ε > 0` there are `c > 0` and finitely many rational scales `s₁, …, s_k ∈ (0,1)` such that
the intersection of the crossing events for `4c` against `max_i 𝒳_{s_i}` has probability at least
`1 - ε`. The ball field `𝒳_s(u)` (`ballField`) is the planar white noise `W` tested against the
Green-function kernel of the ball of radius `s` about `u` (`ballKernel`), in dimension `d = 2` or
`d = 3` with points of the plane read as `(u, 0)` (`planePoint`); a set crosses a rectangle
(`Crosses`) when it contains a compact connected subset meeting both faces perpendicular to the
prescribed direction. The proof rescales the fixed-scale crossing estimate
`prop:fixed-scale-crossings`, whose own proof applies the continuum RSW theorem of
Köhler-Schindler and Tassion, carried here as the explicit hypothesis
`Sandpile.External.ContinuumRSW`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Frozen.FiniteScaleExtraction

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

end Sandpile.Frozen.FiniteScaleExtraction

set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.finite_scale_extraction
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (N : ℕ) (hN : 1 ≤ N)
    (a b : Fin N → Fin 2 → ℝ) (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i)
    (dir : Fin N → Fin 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℝ) (k : ℕ) (s : Fin k → ℚ), 0 < c ∧ 0 < k ∧
      (∀ i : Fin k, 0 < s i ∧ s i < 1) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P,
          Continuous (fun u : Sandpile.Continuum.Space 2 =>
            Sandpile.Frozen.FiniteScaleExtraction.ballField d W s u ω)) →
      ENNReal.ofReal (1 - ε) ≤ P {ω | ∀ j : Fin N,
        Sandpile.Frozen.FiniteScaleExtraction.Crosses (a j) (b j) (dir j)
          {u : Sandpile.Continuum.Space 2 | 4 * c ≤
            ⨆ i : Fin k, Sandpile.Frozen.FiniteScaleExtraction.ballField d W (s i : ℝ) u ω}}
-- FROZEN-STATEMENT-END
:= by
  exact Sandpile.Support.finite_scale_extraction_of_scale_crossing hRSWc hPitt
    Sandpile.External.gaussianLawDeterminedByCovariance hd
    (Sandpile.Support.scaleCrossingAS hd) a b hab dir ε hε
