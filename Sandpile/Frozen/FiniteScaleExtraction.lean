/-
Lemma of Section 4 of sandpile.tex, frozen.  `sandpile.tex:2451-2461`
(label `lem:finite-scale-extraction`):

  "[Finite-scale extraction]  Fix $N\geq1$ axis-parallel rectangles
   $\mathcal R_1,\ldots,\mathcal R_N$ in the plane and a coordinate crossing
   direction for each rectangle.  For every $\varepsilon>0$, there are $c>0$
   and rational scales $s_1,\ldots,s_k\in(0,1)$ such that
   \[
     \P\left(
     \bigcap_{j=1}^N H_{\mathcal R_j}(4c;\max_{1\leq i\leq k}\mathcal X_{s_i})
     \right)\geq1-\varepsilon\, ."

The objects are those of `ssec:admissible` and of the paragraph opening the
subsubsection.

`sandpile.tex:2074-2088`: "Fix $d=2$ or $d=3$.  For $u\in\R^2$ and $0<s\leq1$,
let
\[
  \mathcal X_s(u)\coloneqq
  \begin{cases}
  \int_{\R^2}\frac1{2\pi}\log\frac{s}{|u-z|}\mathbf 1_{\{|u-z|<s\}}\mathcal W(dz),& d=2\, ,\\
  \int_{\R^3}\frac1{4\pi}\left(\frac1{|(u,0)-z|}-\frac1s\right)\mathbf 1_{\{|(u,0)-z|<s\}}\mathcal W(dz),& d=3\, .
  \end{cases}
\]"
That is `ballField` below, the white noise tested against `ballKernel`.

`sandpile.tex:2404-2406`: "Recall that $H_{\mathcal R}(\ell)$ is the event that
$\{\mathcal X_1\geq\ell\}$ crosses the rectangle $\mathcal R$ in the prescribed
coordinate direction.  For a planar field $F$, we write $H_{\mathcal R}(\ell;F)$
for the same event with $F$ in place of $\mathcal X_1$."  Crossing itself is
`sandpile.tex:2112-2118`: "the set contains a compact connected subset joining
the two opposite sides", inside the rectangle.  That is `Crosses` below,
applied to the level set `{u : 4c ≤ max_i 𝒳_{s_i}(u)}`.

Modelling choices.

The rectangles are given by their corner vectors `a j`, `b j`, nondegenerate,
and the prescribed direction by `dir j : Fin 2`; crossing in direction `i`
means meeting both the face `p i = a i` and the face `p i = b i`.

`c` and the scales depend only on the rectangles, the directions, and `ε`, so
they are bound before the space carrying the white noise; Mathlib 4.32
constructs no white noise, so that space is quantified over, and taken in
`Type` so that it can be bound inside the existential.

The list of scales is a function `s : Fin k → ℚ` with `k ≥ 1`; the paper writes
`s_1,\ldots,s_k`, which presumes at least one scale, and `k ≥ 1` is what keeps
`⨆ i : Fin k` from taking the junk value `sSup ∅ = 0`.  The supremum of a
finite nonempty family of reals is its maximum, so `⨆` is the paper's `\max`.

The intersection over `j` is a universally quantified conjunction inside the
event.  The event need not be measurable: `P` of a set is its outer measure,
and the comparison is made in `ℝ≥0∞` with `ENNReal.ofReal (1 - ε)`, which
avoids any `toReal` junk.

The proof of the lemma rests on the rescaled crossing estimate of
`sandpile.tex:2429-2436`, which is `prop:fixed-scale-crossings` rescaled, and
that proposition's proof applies the continuum form of the RSW theorem of
Köhler-Schindler and Tassion at `sandpile.tex:2218`.  By standing convention R1 the
cited comparison is an explicit hypothesis, `Sandpile.External.ContinuumRSW`,
and nothing more.  Added at version 3, together with the restatement of that
comparison on the field.
-/
import Sandpile.Continuum.WhiteNoise
import Sandpile.External.ContinuumRSW
import Sandpile.External.PittGaussianFKG
import Sandpile.External.GaussianLawCovarianceProved
import Sandpile.Support.LimUnconditional
import Sandpile.Support.LimScaleZeroOne

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
