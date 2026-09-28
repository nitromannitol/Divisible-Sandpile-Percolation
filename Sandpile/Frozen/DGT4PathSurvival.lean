import Sandpile.Law
import Sandpile.Walk
import Sandpile.Support.InfiniteGreenField
import Sandpile.External.GreenBoundsHigh
import Sandpile.External.NormalComparison
import Sandpile.Support.LinStep3Core

/-!
# The path-survival lemma, frozen

Lemma of `sandpile.tex`, frozen (`sandpile.tex:5540-5557`, label `lem:dgt4-path-survival`): given
that a certain maximum over a range of times tends to zero as `R → ∞` (matching the survival
probability `P(J(0) > E u_{m-1}(0))` to `G(0,0)κ/m` and the event `{u_m(0) = 0}` to `{J(0) >
E u_{m-1}(0)}`), the averaged path-survival probability converges to the power-law profile
`(1 - j/(R²T))^κ`, and the survival indicators along two deterministic paths have a covariance
bound decaying like `C/(δR²)` away from their overlap, up to a vanishing error. `survival` is the
indicator `S_{n,j}(X)` that the odometer stays positive along the first `j` steps of a path,
`IsThresholdField` transcribes the disjunction defining `J` (either `-V_∞`, the infinite Green
field, or `-G(0,0)ζ` in the Gaussian branch), and `IsNNPath` is a deterministic nearest-neighbor
path condition on its first steps. The Gaussian branch of the proof cites the normal comparison
inequality of Li and Shao, carried as the hypothesis `hNormal`.
-/

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
