/-
Lemma of sandpile.tex, frozen.  `sandpile.tex:5686-5731`
(label `lem:dgt4-linearization-from-survival`):

  "Suppose that the scenery variables are independent and identically
   distributed, atomless, centered, and have finite positive variance.
   Fix $T>0$, let $n_R\coloneqq\lfloor R^2T\rfloor$, and let
   $q_{R,j}\in[0,1]$ be deterministic for $0\leq j<n_R$.  Suppose that as
   $R\to\infty$,
     $R^{-2}\sum_{j=0}^{n_R-1}\mathbf E_0\left|\P(S_{n_R,j}(X)=1\mid X)
      -q_{R,j}\right|\longrightarrow0$,
   and that there is $C<\infty$ such that, for every $\delta\in(0,T)$, there are
   deterministic numbers $\varepsilon_R(\delta)\geq0$ with
   $\varepsilon_R(\delta)\to0$ as $R\to\infty$ and, uniformly over
   $0\leq i,j\leq n_R-\delta R^2$ and all deterministic nearest-neighbor paths
   $X=(X_0,\ldots,X_i)$ and $Y=(Y_0,\ldots,Y_j)$,
     $\left|\Cov(S_{n_R,i}(X),S_{n_R,j}(Y)\mid X,Y)\right|
      \leq\frac{C}{\delta R^2}\sum_{r=0}^i\sum_{h=0}^j\one_{\{X_r=Y_h\}}
      +\varepsilon_R(\delta)$.
   Then, for every $\varphi\in C_c^\infty(\R^d)$,
     $\E\Bigl[\Bigl(R^{(d-4)/2}\bigl(u_{n_R}-\E u_{n_R}(0)
      -\sum_{j=0}^{n_R-1}q_{R,j}P^j\zeta\bigr)^{(R)}(\varphi)\Bigr)^2\Bigr]
      \longrightarrow0$.
   Consequently, for every $s>(d-4)/2$,
     $R^{(d-4)/2}\left(u_{n_R}-\E u_{n_R}(0)
      -\sum_{j=0}^{n_R-1}q_{R,j}P^j\zeta\right)^{(R)}\xrightarrow{\P}0$
   in $H^{-s}_{\rm loc}(\R^d)$."

Modelling decisions.

`S_{n,j}(X)` of `sandpile.tex:5448-5451` is repeated here as `survival`, the
same definition as in `Sandpile/Frozen/DGT4PathSurvival.lean`, and the
nearest-neighbor path condition as `IsNNPath`.  As there,
`P(S_{n,j}(X)=1 | X)` is the scenery integral with the path held fixed, `E_0` is
an integral against `Sandpile.walkLaw d 0`, and `Cov(·,· | X,Y)` for
deterministic paths is `E[fg] - E[f]E[g]` over the scenery.

The deterministic array `q_{R,j}` is a function `q : ℝ → ℕ → ℝ`, constrained to
`[0,1]` exactly on the paper's index range `0 ≤ j < n_R`; outside that range its
values are never used, since every sum runs over `Finset.range ⌊R^2T⌋₊`.

`d ≥ 5` is fixed, as everywhere in this subsection; the paper's `R^{(d-4)/2}`
and the threshold `s > (d-4)/2` use it.

The second conclusion is convergence in probability to zero in
`H^{-s}_{loc}(ℝ^d)`, which is not `Sandpile.Continuum.TendstoInNegSobolev`
(that is convergence in distribution to a Gaussian field); it is written out as
its definition, "on every bounded domain the `H^{-s}(D)` norm exceeds `ε` with
probability tending to zero", using `Sandpile.Continuum.negSobolevNorm` and
`Sandpile.Continuum.IsDomain`.  The norm is `ℝ≥0∞`-valued, so `ε` is compared
through `ENNReal.ofReal`, and the probability is a `toReal`.

Step 1 of the proof uses both intersection moments
(`eq:dgt4-tested-intersection-moments`, `sandpile.tex:5703-5709`).  The first is
proved from `hGreenHigh` (`Sandpile.lintegral_interCount`); the second is the
result the paper cites from Lawler, so the statement carries it as the explicit
hypothesis `hInter`.  The `H^{-s}_loc` clause is proved through
`lem:sobolev-tightness`, whose tightness criterion is cited from Furlan and
Mourrat, so the statement also carries `hBesov`, at the probability space of the
scenery.  That clause upgrades the tested `L^2` estimate of the first
conclusion to convergence in probability of the whole `H^{-s}(D)` dual norm,
which needs the classical Rellich-Kondrachov compact embedding between
negative Sobolev orders; the paper does not prove this classical fact, so the
statement carries it as the explicit hypothesis `hRK`
(`Sandpile.External.RellichKondrachovNegSobolev`).

The scenery is written in the mass normalization: the integration variable is
`σ` with law `Sandpile.centeredMassLaw d ν`, so `ζ = Sandpile.scenery d σ` has
one-site law `ν` and `u_n` is `Sandpile.odometer σ n`; `E u_{n_R}(0)` is
`Sandpile.meanOdometer` and `P^j ζ` is `Sandpile.avg^[j] ζ`.
-/
import Sandpile.Law
import Sandpile.Walk
import Sandpile.Continuum.Membrane
import Sandpile.External.GreenBoundsHigh
import Sandpile.External.IntersectionSecondMomentProved
import Sandpile.External.ContinuumBesovTightness
import Sandpile.External.RellichKondrachovNegSobolev
import Sandpile.Support.LinJacobianFirstConjunct
import Sandpile.Support.Dgt4ALinNegSobolev

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Frozen.DGT4LinearizationFromSurvival

/-- `S_{n,j}(X)` of `sandpile.tex:5443-5446`: "$S_{n,j}(X)\coloneqq
\one_{\{u_{n-r}(X_r)>0\text{ for every }0\leq r\leq j\}}$, the indicator that the
odometer stays positive along the first $j$ steps of $X$." -/
noncomputable def survival {d : ℕ} (σ : Sandpile.Site d → ℝ) (n j : ℕ)
    (X : ℕ → Sandpile.Site d) : ℝ :=
  Set.indicator {Y : ℕ → Sandpile.Site d | ∀ r ≤ j, 0 < Sandpile.odometer σ (n - r) (Y r)}
    (fun _ => 1) X

/-- `X` is a deterministic nearest-neighbor path `(X_0,…,X_n)`. -/
def IsNNPath {d : ℕ} (n : ℕ) (X : ℕ → Sandpile.Site d) : Prop :=
  ∀ r < n, ∃ i : Fin d, X (r + 1) = X r + Sandpile.unit i ∨ X (r + 1) = X r - Sandpile.unit i

end Sandpile.Frozen.DGT4LinearizationFromSurvival

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_linearization_from_survival
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hRK : Sandpile.External.RellichKondrachovNegSobolev) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (T : ℝ) (hT : 0 < T) (q : ℝ → ℕ → ℝ)
    (hq : ∀ (R : ℝ) (j : ℕ), j < ⌊R ^ 2 * T⌋₊ → q R j ∈ Set.Icc (0 : ℝ) 1)
    (hsurvival : Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ
                  ⌊R ^ 2 * T⌋₊ j X ∂(Sandpile.centeredMassLaw d ν)) - q R j|
            ∂(Sandpile.walkLaw d 0)) atTop (𝓝 0))
    (hcov : ∃ C : ℝ, ∀ δ : ℝ, δ ∈ Set.Ioo 0 T →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun atTop (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 → (j : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Sandpile.Site d,
            Sandpile.Frozen.DGT4LinearizationFromSurvival.IsNNPath i X →
            Sandpile.Frozen.DGT4LinearizationFromSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ i X *
                  Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν)) -
                (∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ
                    ⌊R ^ 2 * T⌋₊ i X ∂(Sandpile.centeredMassLaw d ν)) *
                (∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ
                    ⌊R ^ 2 * T⌋₊ j Y ∂(Sandpile.centeredMassLaw d ν))| ≤
              C / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun R) :
    (∀ φ : Sandpile.Continuum.Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ →
        Tendsto (fun R : ℝ =>
            ∫ σ, (R ^ (((d : ℝ) - 4) / 2) *
              Sandpile.Continuum.latticePairing R
                (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
                  Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
                  ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
                    q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
              ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 0)) ∧
      ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
        ∀ D : Set (Sandpile.Continuum.Space d), Sandpile.Continuum.IsDomain D →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun R : ℝ =>
                ((Sandpile.centeredMassLaw d ν)
                  {σ | ENNReal.ofReal ε < Sandpile.Continuum.negSobolevNorm d s D
                    (fun φ => R ^ (((d : ℝ) - 4) / 2) *
                      Sandpile.Continuum.latticePairing R
                        (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
                          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
                          ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
                            q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)}).toReal)
              atTop (𝓝 0)
-- FROZEN-STATEMENT-END
:= by
  have hInter : Sandpile.External.IntersectionSecondMoment :=
    Sandpile.External.intersectionSecondMoment
  have hGreenHigh : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
  haveI : NeZero d := ⟨by omega⟩
  haveI : NullSingletonClass ν := ⟨fun z => hatom z⟩
  have _hvar := hvar
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hsqν : Integrable (fun z : ℝ => z ^ 2) ν := by simpa using hLp.integrable_sq
  obtain ⟨C, hcovC⟩ := hcov
  -- The first conclusion, `eq:dgt4-linearization-from-paths`, is the tested `L²` estimate.
  have hL2 := fun φ hφ => Sandpile.tendsto_l2_frozen_pairing hd hGreenHigh hInter ν hmean hsqν φ hφ
    T hT q C hsurvival hcovC
  -- The `H^{-s}_loc` conclusion upgrades it via tightness and the Rellich-Kondrachov net.
  exact ⟨hL2, Sandpile.Support.tendsto_negSobolevNorm_zero_of_linearization hd hGreenHigh hBesov
    hRK ν hmean hsqν T hT q hq hL2⟩
