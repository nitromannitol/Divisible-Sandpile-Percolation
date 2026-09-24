/-
Proposition of sandpile.tex, frozen.  `sandpile.tex:4782-4798`
(label `prop:dgt4-linearization`):

  "Fix $T>0$ and let $n_R\coloneqq\lfloor R^2T\rfloor$.  For every
   $\varphi\in C_c^\infty(\R^d)$,
     $\E\Bigl[\Bigl(R^{(d-4)/2}\bigl(u_{n_R}-\E u_{n_R}(0)
      -\sum_{j=0}^{n_R-1}(1-\frac{j}{R^2T})^\kappa P^j\zeta\bigr)^{(R)}(\varphi)
      \Bigr)^2\Bigr]\longrightarrow0$."

The standing hypotheses are those of `sandpile.tex:4641-4643`: "Throughout the
remainder of this subsection, we assume the hypotheses of
Theorem~\ref{thm:dgt4-diffusive-membrane}, and $\kappa$ denotes the exponent
defined there."  They are therefore transcribed here in full, exactly as in
`Sandpile/Frozen/DGT4DiffusiveMembrane.lean`: `d ≥ 5`, the scenery i.i.d.,
atomless, centred, of finite positive variance, and either Gaussian with
`κ = 1`, or bounded above with regularly varying lower tail of index `-α`,
`α > 2`, and `κ = 1 - 1/α`.  The disjunction pins `κ` in each branch.

Modelling decisions.

The scenery is written in the mass normalization: the integration variable is
`σ` with law `Sandpile.centeredMassLaw d ν`, so `ζ = Sandpile.scenery d σ` has
one-site law `ν` and `u_n` is `Sandpile.odometer σ n`.  `E u_{n_R}(0)` is
`Sandpile.meanOdometer`.  `P^j ζ` is `Sandpile.avg^[j] ζ`, and the sum
`∑_{j=0}^{n_R-1}` is over `Finset.range ⌊R^2T⌋₊`.

`(·)^{(R)}(φ)` is `Sandpile.Continuum.latticePairing R`, applied to the lattice
field in the large parentheses; the whole difference is formed on the lattice
before pairing, exactly as the paper writes it.  `φ ∈ C_c^∞(ℝ^d)` is
`Sandpile.Continuum.IsTestFn Set.univ φ`.

The paper proves this proposition (`sandpile.tex:5853-5864`) by applying
`lem:dgt4-path-survival` and then `lem:dgt4-linearization-from-survival` to the
time weights `q_{R,j} = (1 - j/(R^2T))^κ`.  Through that chain the proof reaches
five results cited from outside the paper, so the statement carries them as
explicit hypotheses: the Green bounds and the normal comparison inequality of
`lem:dgt4-path-survival`, the Gaussian concentration inequality that the
threshold field of `sandpile.tex:5454-5455` rests on in the Gaussian case, and
the intersection second moment and the Besov tightness criterion of
`lem:dgt4-linearization-from-survival`.

The convergence is as `R → ∞` through the reals, so the limit is
`Tendsto … atTop (𝓝 0)` on `ℝ`; `⌊R^2T⌋` is `Nat.floor`, whose junk value at
negative arguments is never seen since the filter is `atTop` and `T > 0`.
-/
import Sandpile.Law
import Sandpile.Walk
import Sandpile.Continuum.Membrane
import Sandpile.External.GreenBoundsHigh
import Sandpile.External.GaussianLipschitzConcentration
import Sandpile.External.NormalComparison
import Sandpile.External.IntersectionSecondMoment
import Sandpile.External.ContinuumBesovTightness
import Sandpile.Support.LinJacobianFirstConjunct
import Sandpile.Support.Dgt4LinAllPaths
import Sandpile.Support.Dgt4AFinal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_linearization
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hNormal : Sandpile.External.NormalComparison)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (κ : ℝ)
    (hcase :
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧ κ = 1) ∨
      (∃ α : ℝ, 2 < α ∧ (∃ M : ℝ, ν (Set.Ioi M) = 0) ∧
        (∀ lam : ℝ, 0 < lam →
          Tendsto (fun r : ℝ => (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
            atTop (𝓝 (lam ^ (-α)))) ∧
        κ = 1 - 1 / α))
    (T : ℝ) (hT : 0 < T)
    (φ : Sandpile.Continuum.Space d → ℝ) (hφ : Sandpile.Continuum.IsTestFn Set.univ φ) :
    Tendsto (fun R : ℝ =>
        ∫ σ, (R ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
              ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
                (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ *
                  (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
          ∂(Sandpile.centeredMassLaw d ν))
      atTop (𝓝 0)
-- FROZEN-STATEMENT-END
:= by
  have _besov := hBesov
  haveI : NeZero d := ⟨by omega⟩
  haveI : NullSingletonClass ν := ⟨fun z => hatom z⟩
  have hκ : 0 < κ := by
    rcases hcase with ⟨-, hκ1⟩ | ⟨α, hα, -, -, hκ2⟩
    · rw [hκ1]; norm_num
    · rw [hκ2]
      have h1 : 1 / α < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      linarith
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hsqν : Integrable (fun z : ℝ => z ^ 2) ν := by simpa using hLp.integrable_sq
  have hct := Sandpile.caseThresholdField_of_hcase hGreenHigh hGaussConc d hd ν hatom hmean
    hvar hvar' κ hcase
  have hsurv := (Sandpile.dgt4_linearization_inputs_of hGreenHigh hNormal d hd ν hatom hmean
    hvar hvar' T hT κ hκ hct).1
  obtain ⟨C, hcov⟩ :=
    Sandpile.dgt4_linearization_cov_all_of hNormal hd ν hatom hvar' T hT κ hκ hct
  -- The covariance bound is available for every pair of paths; the tested estimate asks for it
  -- only along nearest-neighbour pairs, which is where the walk lives.
  exact Sandpile.tendsto_l2_frozen_pairing hd hGreenHigh hInter ν hmean hsqν φ hφ T hT
    (fun R j => (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ) C hsurv
    (fun δ hδ => by
      obtain ⟨εfun, hε0, hεt, hεb⟩ := hcov δ hδ
      exact ⟨εfun, hε0, hεt, fun R i j hi hj X Y _ _ => hεb R i j hi hj X Y⟩)
