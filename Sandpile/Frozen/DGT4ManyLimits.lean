import Sandpile.Law
import Sandpile.Walk
import Sandpile.Continuum.Membrane
import Sandpile.External.GreenBoundsHigh
import Sandpile.External.LocalCLT
import Sandpile.External.LocalCLTProved
import Sandpile.External.IntersectionSecondMomentProved
import Sandpile.Support.Dgt4AManyLimitsAssembly

/-!
# Many superdiffusive limits, frozen

Theorem 1.3(iii)(d) of `sandpile.tex`, in sharper form, frozen (`sandpile.tex:5971-5999`, label
`thm:dgt4-many-limits`): for `d ≥ 5` there exists an i.i.d. scenery whose one-site law `ν` has mean
zero, variance one, a strictly positive `C^∞` density, an exponential moment, and a two-sided
linear log-tail bound `c r ≤ -log P(ζ(0) ≤ -r) ≤ C r` for large `r`, together with a sequence
`R_k ↑ ∞` such that for every `κ ∈ [3/2, 2]` there is a subsequence `R_{k_ℓ}` along which the
rescaled, recentred odometer converges in `H^{-s}_loc(ℝ^d)` to the weighted membrane field
`ℋ_{κ,T}` with covariance `Sandpile.Continuum.weightedMembraneCov d 1 κ T`, and the laws
`ℋ_{κ,T}` for distinct `κ ∈ [3/2,2]` are pairwise distinct. The scenery is produced (an existential
in `ν`, then in `R_k`, then for each `κ` in the extraction `k_ℓ`) rather than quantified over;
subsequential convergence is expressed by reindexing `Sandpile.Continuum.TendstoInNegSobolev`'s
family through `⌊L⌋`, and pairwise distinctness of the Gaussian laws is stated as distinctness of
their covariances on some test function.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_many_limits
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ)) :
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
            Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ' T φ φ
-- FROZEN-STATEMENT-END
:= by
  have hInter : Sandpile.External.IntersectionSecondMoment :=
    Sandpile.External.intersectionSecondMoment
  have hHeat : Sandpile.External.HeatKernelBounds := Sandpile.External.heatKernelBounds
  have hGreenHigh : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
  obtain ⟨ν, hprob, hmean, hvar, hdens, htail, hstep3, hdistinct⟩ :=
    Sandpile.Support.dgt4_many_limits_assembled d hd hGreenHigh hInter hHeat
      Sandpile.External.localCLT hBesov
  exact ⟨ν, hprob, hmean, hvar, hdens, htail, hstep3, hdistinct⟩
