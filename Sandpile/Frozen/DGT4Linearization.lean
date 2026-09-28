import Sandpile.Law
import Sandpile.Walk
import Sandpile.Continuum.Membrane
import Sandpile.External.GreenBoundsHigh
import Sandpile.External.GaussianLipschitzConcentration
import Sandpile.External.NormalComparison
import Sandpile.External.IntersectionSecondMomentProved
import Sandpile.External.ContinuumBesovTightness
import Sandpile.Support.LinJacobianFirstConjunct
import Sandpile.Support.Dgt4LinAllPaths
import Sandpile.Support.Dgt4AFinal

/-!
# Linearization of the rescaled odometer above dimension four

This file proves the frozen statement of `prop:dgt4-linearization` (`sandpile.tex:4809-4825`):
for `d ≥ 5` and scenery satisfying the standing hypotheses of `thm:dgt4-diffusive-membrane`, the
rescaled and time-weighted difference between the odometer `u_{n_R}` and its linear approximation
`∑_{j=0}^{n_R-1} (1 - j/(R²T))^κ P^j ζ` converges to zero in `L²` after pairing against any test
function `φ`, as `R → ∞` with `n_R = ⌊R²T⌋`. The scenery is carried in the mass normalization, so
`P^j ζ` is `Sandpile.avg^[j] (Sandpile.scenery d σ)` and the pairing `(·)^{(R)}(φ)` is
`Sandpile.Continuum.latticePairing R`. The proof chains the path-survival estimate of
`lem:dgt4-path-survival` with `lem:dgt4-linearization-from-survival`, and along the way carries
the Green bounds, the normal comparison inequality, the Gaussian concentration inequality for the
threshold field, the intersection second moment, and the Besov tightness criterion as explicit
hypotheses.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_linearization
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hNormal : Sandpile.External.NormalComparison)
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
  have hInter : Sandpile.External.IntersectionSecondMoment :=
    Sandpile.External.intersectionSecondMoment
  have hGreenHigh : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
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
