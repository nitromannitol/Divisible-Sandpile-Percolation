/-
`thm:dgt4-many-limits` (`sandpile.tex:5900-5928`) granted its one remaining
input, the subsequential convergence of the rescaled centred odometer along a
single sequence of scales.

Four of the six clauses are the scenery's own, and are supplied by
`exists_scenery_law`: the logistic law rescaled to variance one has mean zero, a
strictly positive smooth density, an exponential moment and the two-sided linear
logarithmic lower tail the theorem asks for.  The fifth clause, the
subsequential convergence in `H^{-s}_loc`, is the hypothesis here; the paper
obtains it from `prop:dgt4-contact-asymptotics` by extracting, for each
`κ ∈ [3/2,2]`, a subsequence of one fixed sequence of scales.  The sixth, the
pairwise distinctness of the laws of the limit fields, is
`exists_testFn_weightedMembraneCov_ne`: the variance of `ℋ_{κ,T}(φ)` at a
nonnegative test function is strictly decreasing in `κ`, so two distinct
exponents give two covariances that already differ on the diagonal.
-/
import Sandpile.Support.ContCovKappa
import Sandpile.Support.ContHighNonconvergence
import Sandpile.Continuum.Membrane
import Sandpile.Law

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- **`thm:dgt4-many-limits` from the subsequential convergence.**  The scenery
and its four analytic properties are carried in; the convergence along the
subsequences is the hypothesis; the distinctness of the limit laws is proved
here from the strict monotonicity of the covariance in the exponent. -/
theorem dgt4_many_limits_of (d : ℕ) (hd : 1 ≤ d)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : variance (id : ℝ → ℝ) ν = 1)
    (hdens : ∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
      ν = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z))
    (htail : ∃ c C θ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ ∧
      Integrable (fun z => Real.exp (θ * |z|)) ν ∧
      ∀ᶠ r : ℝ in atTop,
        c * r ≤ -Real.log (ν (Set.Iic (-r))).toReal ∧
          -Real.log (ν (Set.Iic (-r))).toReal ≤ C * r)
    (hsub : ∃ Rseq : ℕ → ℝ, StrictMono Rseq ∧ Tendsto Rseq atTop atTop ∧
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
              (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T)) :
    ∃ ν : Measure ℝ, ∃ _ : IsProbabilityMeasure ν,
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
            Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ' T φ φ := by
  refine ⟨ν, hprob, hmean, hvar, hdens, htail, hsub, ?_⟩
  intro T hT κ κ' hκ hκ' hne
  rw [hvar]
  exact exists_testFn_weightedMembraneCov_ne d hd hT one_pos
    (le_trans (by norm_num) hκ.1) (le_trans (by norm_num) hκ'.1) hne

/-- **Theorem 1.3(iii)(d) from the subsequential convergence alone.**  The
derivation of `ContHighNonconvergence` needs two inputs, the subsequential
convergence and the distinctness of the limit covariances; the second is now
proved, so the nonconvergence rests on the first alone. -/
theorem high_nonconvergence_of_sub
    (hHeatKernel : Sandpile.External.HeatKernelBounds)
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hd : 5 ≤ d) (ν : MeasureTheory.Measure ℝ) [IsProbabilityMeasure ν]
    (hvar : variance (id : ℝ → ℝ) ν = 1)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (Rseq : ℕ → ℝ) (hRtop : Tendsto Rseq atTop atTop)
    (hsub : ∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
      ∃ kl : ℕ → ℕ, StrictMono kl ∧
        ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
          Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
            (fun (L : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Space d → ℝ) =>
              Rseq (kl ⌊L⌋₊) ^ (((d : ℝ) - 4) / 2) *
                Sandpile.Continuum.latticePairing (Rseq (kl ⌊L⌋₊))
                  (fun x => Sandpile.odometer σ ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊ x -
                    Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν)
                      ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊) φ)
            (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T))
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : ((d : ℝ) - 4) / 2 < s) :
    Sandpile.Continuum.TightInNegSobolev d s (Sandpile.centeredMassLaw d ν)
        (Sandpile.Continuum.diffusiveFluctuation (Sandpile.centeredMassLaw d ν) T) ∧
      (∃ (I : Set ℝ) (K : ℝ → (Space d → ℝ) → (Space d → ℝ) → ℝ),
        ¬ I.Countable ∧
          (∀ κ ∈ I, ∀ κ' ∈ I, κ ≠ κ' →
            ∃ φ : Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ ∧
              gaussianReal 0 (Real.toNNReal (K κ φ φ)) ≠
                gaussianReal 0 (Real.toNNReal (K κ' φ φ))) ∧
          ∀ κ ∈ I, ∃ Rs : ℕ → ℝ, Tendsto Rs atTop atTop ∧
            ∀ φ : Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ →
              TendstoInDistribution
                (fun (k : ℕ) (σ : Sandpile.Site d → ℝ) =>
                  Sandpile.Continuum.diffusiveFluctuation
                    (Sandpile.centeredMassLaw d ν) T (Rs k) σ φ)
                atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
                (gaussianReal 0 (Real.toNNReal (K κ φ φ)))) ∧
      ¬ ∃ K : (Space d → ℝ) → (Space d → ℝ) → ℝ,
        Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
          (Sandpile.Continuum.diffusiveFluctuation (Sandpile.centeredMassLaw d ν) T) K := by
  refine high_nonconvergence_of hHeatKernel hGreenHigh hLocalCLT hBesov hd ν θ hθ hexp
    Rseq hRtop hsub ?_ T hT s hs
  intro T' hT' κ κ' hκ hκ' hne
  rw [hvar]
  exact exists_testFn_weightedMembraneCov_ne d (le_trans (by norm_num) hd) hT' one_pos
    (le_trans (by norm_num) hκ.1) (le_trans (by norm_num) hκ'.1) hne

end Sandpile.Support
