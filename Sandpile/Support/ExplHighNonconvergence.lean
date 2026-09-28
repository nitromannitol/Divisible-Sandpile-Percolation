import Sandpile.Support.ContManyLimits
import Sandpile.Frozen.DGT4ManyLimits

/-!
# Theorem 1.3(iii)(d) from the sharper many-limits theorem

Theorem 1.3(iii)(d) of `sandpile.tex` (`sandpile.tex:290-296`) assembled from
`thm:dgt4-many-limits` (`sandpile.tex:5900-5928`), which the proof of `thm:main-explosion` names
at `sandpile.tex:308-309`: "part (iii)(d) is Theorem~\ref{thm:dgt4-many-limits}".

The sharper theorem produces the scenery, the scale sequence `R_k`, and for each `κ ∈ [3/2,2]` an
extraction along which the diffusively rescaled fluctuations converge to `ℋ_{κ,T}`; Theorem
1.3(iii)(d) asks only for the scenery, an uncountable family of distinct subsequential limits, and
nonconvergence. `Sandpile.Support.high_nonconvergence_of_sub` already derives the second and third
from the subsequential convergence at variance one, so all that is left is to unpack the existential
of the sharper theorem and feed its clauses in: the index set is `[3/2,2]`, the covariance
assignment is injective because the variances differ on a test function, and the tightness
clause is the odometer's own.

The two cited inputs the chain reaches are carried explicitly. The local central limit theorem
enters `thm:dgt4-many-limits` itself, and the tightness criterion of Furlan and Mourrat enters
through `lem:sobolev-tightness`; both are `External` `Prop`s of this repository.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- **Theorem 1.3(iii)(d) from `thm:dgt4-many-limits`.**  `hML` is the exact
conclusion of the sharper theorem; everything else is proved here. -/
theorem high_nonconvergence_of_many_limits
    (hHeatKernel : Sandpile.External.HeatKernelBounds)
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hd : 5 ≤ d)
    (hML : ∃ ν : Measure ℝ, ∃ _ : IsProbabilityMeasure ν,
      ∫ z, z ∂ν = 0 ∧ variance (id : ℝ → ℝ) ν = 1 ∧
      (∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
        ν = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z)) ∧
      (∃ c C θ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ ∧
        Integrable (fun z => Real.exp (θ * |z|)) ν ∧
        ∀ᶠ r : ℝ in atTop,
          c * r ≤ -Real.log (ν (Set.Iic (-r))).toReal ∧
            -Real.log (ν (Set.Iic (-r))).toReal ≤ C * r) ∧
      (∃ Rseq : ℕ → ℝ, StrictMono Rseq ∧ Tendsto Rseq atTop atTop ∧
        ∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
          ∃ kl : ℕ → ℕ, StrictMono kl ∧
            ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
              Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
                (fun (L : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
                  Rseq (kl ⌊L⌋₊) ^ (((d : ℝ) - 4) / 2) *
                    Sandpile.Continuum.latticePairing (Rseq (kl ⌊L⌋₊))
                      (fun x => Sandpile.odometer σ ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊ x -
                        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν)
                          ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊) φ)
                (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T)) ∧
      ∀ T : ℝ, 0 < T → ∀ κ κ' : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
        κ' ∈ Set.Icc ((3 : ℝ) / 2) 2 → κ ≠ κ' →
        ∃ φ : Sandpile.Continuum.Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ ∧
          Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T φ φ ≠
            Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ' T φ φ) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ [_i : IsProbabilityMeasure ν],
      (∫ z, z ∂ν = 0) ∧ variance id ν = 1 ∧
      (∃ p : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ (∀ z : ℝ, 0 < p z) ∧
        ν = volume.withDensity fun z => ENNReal.ofReal (p z)) ∧
      (∃ θ₀ : ℝ, 0 < θ₀ ∧ Integrable (fun z => Real.exp (θ₀ * |z|)) ν) ∧
      ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
        Sandpile.Continuum.TightInNegSobolev d s (Sandpile.centeredMassLaw d ν)
            (Sandpile.Continuum.diffusiveFluctuation (Sandpile.centeredMassLaw d ν) T) ∧
          (∃ (I : Set ℝ) (K : ℝ → (Sandpile.Continuum.Space d → ℝ) →
              (Sandpile.Continuum.Space d → ℝ) → ℝ),
            ¬ I.Countable ∧
              (∀ κ ∈ I, ∀ κ' ∈ I, κ ≠ κ' →
                ∃ φ : Sandpile.Continuum.Space d → ℝ,
                  Sandpile.Continuum.IsTestFn Set.univ φ ∧
                    gaussianReal 0 (Real.toNNReal (K κ φ φ)) ≠
                      gaussianReal 0 (Real.toNNReal (K κ' φ φ))) ∧
              ∀ κ ∈ I, ∃ Rs : ℕ → ℝ, Tendsto Rs atTop atTop ∧
                ∀ φ : Sandpile.Continuum.Space d → ℝ,
                  Sandpile.Continuum.IsTestFn Set.univ φ →
                    TendstoInDistribution
                      (fun (k : ℕ) (σ : Sandpile.Site d → ℝ) =>
                        Sandpile.Continuum.diffusiveFluctuation
                          (Sandpile.centeredMassLaw d ν) T (Rs k) σ φ)
                      atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
                      (gaussianReal 0 (Real.toNNReal (K κ φ φ)))) ∧
          ¬ ∃ K : (Sandpile.Continuum.Space d → ℝ) →
              (Sandpile.Continuum.Space d → ℝ) → ℝ,
            Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
              (Sandpile.Continuum.diffusiveFluctuation (Sandpile.centeredMassLaw d ν) T) K := by
  classical
  obtain ⟨ν, hprob, hmean, hvar, ⟨f, hfpos, hfsmooth, hfdens⟩, ⟨c, C, θ, hc, hC, hθ, hexp, _htail⟩,
    ⟨Rseq, _hRmono, hRtop, hsub⟩, _hdist⟩ := hML
  refine ⟨ν, hprob, ?_⟩
  intro _i
  refine ⟨hmean, hvar, ⟨f, hfsmooth, hfpos, hfdens⟩, ⟨θ, hθ, hexp⟩, ?_⟩
  intro T hT s hs
  exact high_nonconvergence_of_sub hHeatKernel hGreenHigh hLocalCLT hBesov hd ν hvar θ hθ hexp
    Rseq hRtop hsub T hT s hs

end Sandpile.Support
