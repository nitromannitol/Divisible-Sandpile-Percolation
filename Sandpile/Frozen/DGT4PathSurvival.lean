/-
Lemma of sandpile.tex, frozen.  `sandpile.tex:5513-5530`
(label `lem:dgt4-path-survival`):

  "Let $T>0$, $\kappa>0$, and $n_R\coloneqq\lfloor R^2T\rfloor$, and suppose
   that for every $\varepsilon\in(0,1)$, as $R\to\infty$,
     $\max_{\lceil\varepsilon n_R\rceil\leq m\leq n_R}
      \left\{\left|\frac{m\P(J(0)>\E u_{m-1}(0))}{G(0,0)\kappa}-1\right|
      +m\P\bigl(\{u_m(0)=0\}\mathbin{\triangle}\{J(0)>\E u_{m-1}(0)\}\bigr)\right\}
      \longrightarrow0$.
   Then
     $R^{-2}\sum_{j=0}^{n_R-1}\mathbf E_0\left|\P(S_{n_R,j}(X)=1\mid X)
      -\left(1-\frac{j}{R^2T}\right)^\kappa\right|\longrightarrow0$.
   Moreover, there is $C<\infty$ so that for each $\delta\in(0,T)$ there are
   $\varepsilon_R(\delta)\geq0$ with $\varepsilon_R(\delta)\to0$ as
   $R\to\infty$ and, uniformly over $0\leq i,j\leq n_R-\delta R^2$ and all
   deterministic nearest-neighbor paths $X=(X_0,\ldots,X_i)$ and
   $Y=(Y_0,\ldots,Y_j)$,
     $\bigl|\Cov(S_{n_R,i}(X),S_{n_R,j}(Y)\mid X,Y)\bigr|
      \leq\frac{C}{\delta R^2}\sum_{r=0}^i\sum_{h=0}^j\one_{\{X_r=Y_h\}}
      +\varepsilon_R(\delta)$."

Modelling decisions.

`S_{n,j}(X)` is defined at `sandpile.tex:5448-5451`: "$S_{n,j}(X)\coloneqq
\one_{\{u_{n-r}(X_r)>0\text{ for every }0\leq r\leq j\}}$, the indicator that
the odometer stays positive along the first $j$ steps of $X$"; it is `survival`
below, real valued and written with `Set.indicator` so that no decidability
instance is needed.  `n - r` is truncated subtraction in `ℕ`, and the lemma is
only ever used with `r ≤ j < n`, where it agrees with the paper.

`J` is defined at `sandpile.tex:5454-5455`: "Set $J=-V_\infty$ in
case~\textup{(a)} and $J=-G(0,0)\zeta$ in case~\textup{(b)}", with
`V_∞(x) = ∑_z G(x,z)ζ(z)` of `sandpile.tex:4834-4836`.  It is quantified over,
subject to `IsThresholdField`, which is exactly that disjunction; the Gaussian
branch also records that the one-site law is Gaussian, since that is what makes
`J = -V_∞` a Gaussian field with the correlation gap the proof uses.  The
lemma is stated for a general `J` of this shape rather than under the
subsection's case dichotomy because `sandpile.tex:6310-6315` applies it to a law
in neither case, with `J(x) = -G(0,0)ζ(x)`.

`P(S_{n,j}(X)=1 | X)` conditions on the walk, which is independent of the
scenery, so it is the scenery integral with the path held fixed; `E_0` is then
an integral over path space against `Sandpile.walkLaw d 0`.  Likewise
`Cov(·,· | X,Y)` for deterministic paths `X, Y` is the covariance over the
scenery alone, written as `E[fg] - E[f]E[g]`.

Both "max over a finite range tends to zero" statements are unfolded into
`∀ η > 0, ∀ᶠ R, ∀ m in the range, … ≤ η`, since a `sSup` or `Finset.sup'` over a
range carries a junk value; this preserves the paper's quantifier order, `ε`
fixed first and then the limit in `R`.  The two summands of the hypothesis are
nonnegative, so bounding their sum by `η` is exactly the paper's statement.

"Deterministic nearest-neighbor path `X = (X_0,…,X_i)`" is `IsNNPath i X`, a
condition on the first `i` steps only; the values of `X` beyond time `i` are
unconstrained and unused, since `survival σ n i X` looks only at `X_0,…,X_i`.

The proof of Step 1 in the Gaussian branch of `IsThresholdField` cites the
normal comparison inequality of Li and Shao (`sandpile.tex:5512`), so the
statement carries that cited result as the explicit hypothesis `hNormal`; in the
independent branch the factorization is exact and needs nothing
(`Sandpile.centeredMassLaw_threshold_factorization`).  The covariance decay
`eq:dgt4-intersection-first-moment` the same step uses is the already present
`hGreenHigh`.

The scenery is written in the mass normalization: the integration variable is
`σ` with law `Sandpile.centeredMassLaw d ν`, so `ζ = Sandpile.scenery d σ` has
one-site law `ν` and `u_n` is `Sandpile.odometer σ n`.  `E u_m(0)` is
`Sandpile.meanOdometer`, and the symmetric difference is `symmDiff`.
-/
import Sandpile.Law
import Sandpile.Walk
import Sandpile.Support.InfiniteGreenField
import Sandpile.External.GreenBoundsHigh
import Sandpile.External.NormalComparison
import Sandpile.Support.LinStep3Core

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Frozen.DGT4PathSurvival

/-- `S_{n,j}(X)` of `sandpile.tex:5443-5446`: "$S_{n,j}(X)\coloneqq
\one_{\{u_{n-r}(X_r)>0\text{ for every }0\leq r\leq j\}}$, the indicator that the
odometer stays positive along the first $j$ steps of $X$." -/
noncomputable def survival {d : ℕ} (σ : Sandpile.Site d → ℝ) (n j : ℕ)
    (X : ℕ → Sandpile.Site d) : ℝ :=
  Set.indicator {Y : ℕ → Sandpile.Site d | ∀ r ≤ j, 0 < Sandpile.odometer σ (n - r) (Y r)}
    (fun _ => 1) X

-- `V_∞(x) = ∑_{z∈ℤ^d} G(x,z)ζ(z)` of `sandpile.tex:4829-4831`
-- (`eq:dgt4-infinite-green-field`), as the box limit of the finite partial
-- sums (see Sandpile/Support/InfiniteGreenField.lean).
export Sandpile (infiniteGreenField)

/-- `J` of `sandpile.tex:5449-5450`: "Set $J=-V_\infty$ in case~\textup{(a)} and
$J=-G(0,0)\zeta$ in case~\textup{(b)}."  The Gaussian branch also records that
the one-site law is Gaussian, which is what makes `-V_∞` a Gaussian field. -/
def IsThresholdField {d : ℕ} (ν : Measure ℝ)
    (J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ) : Prop :=
  (∀ σ x, J σ x = -(Sandpile.green d 0 0 * Sandpile.scenery d σ x)) ∨
    ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧
      ∀ σ x, J σ x = -infiniteGreenField (Sandpile.scenery d σ) x)

/-- `X` is a deterministic nearest-neighbor path `(X_0,…,X_n)`. -/
def IsNNPath {d : ℕ} (n : ℕ) (X : ℕ → Sandpile.Site d) : Prop :=
  ∀ r < n, ∃ i : Fin d, X (r + 1) = X r + Sandpile.unit i ∨ X (r + 1) = X r - Sandpile.unit i

end Sandpile.Frozen.DGT4PathSurvival

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_path_survival
    (hNormal : Sandpile.External.NormalComparison)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ)
    (hJ : Sandpile.Frozen.DGT4PathSurvival.IsThresholdField ν J)
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (hthresholds : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ R : ℝ in atTop, ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
        |(m : ℝ) * ((Sandpile.centeredMassLaw d ν)
              {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
            (Sandpile.green d 0 0 * κ) - 1| +
          (m : ℝ) * ((Sandpile.centeredMassLaw d ν)
            (symmDiff {σ | Sandpile.odometer σ m 0 = 0}
              {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) <
                J σ 0})).toReal ≤ η) :
    Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, Sandpile.Frozen.DGT4PathSurvival.survival σ ⌊R ^ 2 * T⌋₊ j X
                ∂(Sandpile.centeredMassLaw d ν)) -
              (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ| ∂(Sandpile.walkLaw d 0))
      atTop (𝓝 0) ∧
    ∃ C : ℝ, ∀ δ : ℝ, δ ∈ Set.Ioo 0 T →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun atTop (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 → (j : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Sandpile.Site d,
            Sandpile.Frozen.DGT4PathSurvival.IsNNPath i X →
            Sandpile.Frozen.DGT4PathSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.Frozen.DGT4PathSurvival.survival σ ⌊R ^ 2 * T⌋₊ i X *
                  Sandpile.Frozen.DGT4PathSurvival.survival σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν)) -
                (∫ σ, Sandpile.Frozen.DGT4PathSurvival.survival σ ⌊R ^ 2 * T⌋₊ i X
                  ∂(Sandpile.centeredMassLaw d ν)) *
                (∫ σ, Sandpile.Frozen.DGT4PathSurvival.survival σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν))| ≤
              C / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun R
-- FROZEN-STATEMENT-END
:= by
  haveI : NeZero d := ⟨by omega⟩
  -- the Green bounds, the mean-zero hypothesis and the nondegeneracy of the one-site law
  -- are the standing hypotheses of the subsection; the two conclusions use only the
  -- atomlessness (through the Gaussian branch) and the finite variance.
  have _hmean := hmean
  have _hvar := hvar
  refine ⟨Sandpile.tendsto_averaged_survival_of_thresholds hNormal hd ν hatom hvar' J hJ T hT κ hκ
      hthresholds, 4 * (κ * Sandpile.green d 0 0), fun δ hδ => ?_⟩
  obtain ⟨efun, h0, htend, hbd⟩ :=
    Sandpile.exists_cov_bound hNormal hd ν hatom hvar' J hJ T hT κ hκ hthresholds δ hδ
  exact ⟨efun, h0, htend, fun R i j hi hj X Y _ _ => hbd R i j hi hj X Y⟩
