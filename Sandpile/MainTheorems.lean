import Sandpile.Frozen.Nontriviality
import Sandpile.Frozen.CriticalLevels
import Sandpile.Frozen.MeanGrowthLow
import Sandpile.Frozen.BrownianScalingLimit
import Sandpile.Frozen.MeanGrowthFour
import Sandpile.Frozen.FourFirstOrder
import Sandpile.Frozen.FourGaussian
import Sandpile.Frozen.FourSobolev
import Sandpile.Frozen.HighFirstOrder
import Sandpile.Frozen.HighTail
import Sandpile.Frozen.HighSobolevLimit
import Sandpile.Frozen.HighNonconvergence

/-!
# Main results

The main theorems of the formalization of *Quantitative explosion and percolation of the
divisible sandpile* (Bou-Rabee and Panagiotis, arXiv:2609.02829), stated here in full: the
percolation of the toppled set below mean one (`thm:main-nontriviality`), the percolation of
the critical level sets (`thm:main-critical-level-percolation`), and the ten parts of the
critical growth and scaling theorem (`thm:main-explosion`) as they are registered in
`ledger/manifest.yaml`.

Each theorem below restates its certified counterpart in `Sandpile/Frozen/` and is proved by
`exact` of it, so the statements displayed in this file are the certified ones.  The
hypotheses whose types are named `Sandpile.External.*` are results the paper cites without
proof; they are assumed, not proved, and are listed with their statements in `ASSUMPTIONS.md`.
Six cited inputs are also proved in this repository (the files
`Sandpile/External/*Proved.lean`): the `d ≥ 5` Green estimates, the finite-time variance scale,
the heat-kernel bounds, the optimal-stopping representation, the Gaussian-law-by-covariance
fact, and Pinsker's inequality.  Of these, the first three appear as explicit hypotheses of
theorems below at earlier versions; since each is now proved unconditionally, no theorem here
carries it as a hypothesis any longer.  The optimal-stopping representation is used, and
discharged the same way, inside the certified proofs of `thm:RW` and two lemmas that feed
these theorems; it was never itself a hypothesis of a theorem in this file.  The
Gaussian-law-by-covariance fact and Pinsker's inequality are used only inside the certified
proofs and are not hypotheses of any theorem in this file either.

* `Sandpile.percolation_below_criticality`: for `d ≥ 2` and a family of laws `μ_ρ` of mean `ρ`
  with a uniform variance lower bound and a uniform exponential moment on `[ρ₀, 1)`, there is
  `ρ₊ ∈ [ρ₀, 1)` such that the toppled set contains an infinite component almost surely for
  every `ρ ∈ (ρ₊, 1)`.
* `Sandpile.critical_level_percolation`: at mean one, for every `t ≥ t₀` the level set
  `{x : u_t(x) > c h(t)}` contains an infinite component almost surely, with `c` and `t₀`
  uniform over the laws with the given variance and exponential-moment bounds.
* `Sandpile.mean_growth_le_three`: in `d ≤ 3`, `t^{-(4-d)/4} E u_t(0)` converges to a positive
  limit.
* `Sandpile.brownian_scaling_limit`: in `d ≤ 3`, the rescaled and interpolated odometer at time
  `⌊TR²⌋` converges in finite-dimensional distributions to the value of a Brownian
  optimal-stopping problem, and is tight in the uniform norm on compact sets.
* `Sandpile.mean_growth_four`: in `d = 4`, `c log t ≤ E u_t(0) ≤ C log t` for `t ≥ 2`.
* `Sandpile.four_first_order`: in `d = 4`, `u_t(x) / E u_t(0) → 1` in `L²` and almost surely.
* `Sandpile.four_gaussian`: in `d = 4`, `(u_t(0) - E u_t(0)) / √(log t)` converges in
  distribution to a centred Gaussian of variance `4 Var(ζ(0))/π²`, and the variance converges to
  the same constant.
* `Sandpile.four_sobolev`: in `d = 4`, the centred odometer is tight in every negative Sobolev
  space at diffusive times, and at polynomial superdiffusive times converges, modulo constants,
  to the four-dimensional membrane model.
* `Sandpile.high_first_order`: in `d ≥ 5`, `u_t(x) / E u_t(0) → 1` in `L²` and almost surely,
  and `E u_t(0) ≥ c (log t)^{2/d}` eventually.
* `Sandpile.high_tail`: in `d ≥ 5`, under a lower tail of order `exp(-s^γ)`, `E u_t(0)` is of
  order `(log t)^{1/min{γ, d/2}}`.
* `Sandpile.high_sobolev_limit`: in `d ≥ 5`, the rescaled centred odometer converges in
  `H^{-s}_loc` to a weighted membrane field, for Gaussian masses and for bounded-above atomless
  masses with a regularly varying lower tail.
* `Sandpile.high_nonconvergence`: in `d ≥ 5`, there is a smooth positive density with an
  exponential moment whose rescaled fluctuations are tight but have uncountably many distinct
  subsequential limits, and so do not converge.

All twelve reduce to the standard axioms (`propext`, `Classical.choice`, `Quot.sound`); see
`Sandpile/Meta/AxiomsAudit.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

/-- **Theorem 1.1** (`thm:main-nontriviality`).  The certified statement is
`Sandpile.Frozen.percolation_below_criticality`. -/
theorem Sandpile.percolation_below_criticality
    (hBallGreen : Sandpile.External.BallGreenBounds)
    (hRSW : Sandpile.External.PlanarRSW)
    (hLSS : Sandpile.External.LSSDomination)
    (hBoundary : Sandpile.External.ExteriorBoundaryConnected)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hOcc : Sandpile.External.BallOccupationDensity)
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hCube : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (μ : ℝ → Measure ℝ) (hprob : ∀ ρ, IsProbabilityMeasure (μ ρ))
    (hmean : ∀ ρ ∈ Set.Ioc (0 : ℝ) 1, ∫ s, s ∂(μ ρ) = ρ)
    (ρ₀ ν₀ θ₀ K₀ : ℝ) (hρ₀ : ρ₀ ∈ Set.Ioo (0 : ℝ) 1) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀)
    (hvar : ∀ ρ ∈ Set.Ico ρ₀ 1, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (μ ρ))
    (hexpint : ∀ ρ ∈ Set.Ico ρ₀ 1, Integrable (fun s => Real.exp (θ₀ * |s - ρ|)) (μ ρ))
    (hexp : ∀ ρ ∈ Set.Ico ρ₀ 1, ∫ s, Real.exp (θ₀ * |s - ρ|) ∂(μ ρ) ≤ K₀) :
    ∃ ρPlus ∈ Set.Ico ρ₀ 1, ∀ ρ ∈ Set.Ioo ρPlus 1,
      ∀ᵐ σ ∂(Sandpile.massLaw d (μ ρ)),
        Sandpile.HasInfiniteComponent (Sandpile.toppledSet σ) := by
  exact Sandpile.Frozen.percolation_below_criticality hBallGreen hRSW hLSS hBoundary hRSWc hPitt
    hOcc hLocalCLT hCube d hd μ hprob hmean ρ₀ ν₀ θ₀ K₀ hρ₀ hν₀ hθ₀ hvar hexpint hexp

/-- **Theorem 1.2** (`thm:main-critical-level-percolation`).  The certified statement is
`Sandpile.Frozen.critical_level_percolation`. -/
theorem Sandpile.critical_level_percolation
    (hBallGreen : Sandpile.External.BallGreenBounds)
    (hRSW : Sandpile.External.PlanarRSW)
    (hLSS : Sandpile.External.LSSDomination)
    (hBoundary : Sandpile.External.ExteriorBoundaryConnected)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hOcc : Sandpile.External.BallOccupationDensity)
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hCube : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.massLaw d μ),
          Sandpile.HasInfiniteComponent
            {x | c * Sandpile.criticalScale d t < Sandpile.odometer σ t x} := by
  exact Sandpile.Frozen.critical_level_percolation hBallGreen hRSW hLSS
    hBoundary hRSWc hPitt hOcc hLocalCLT hCube d hd ν₀ θ₀ K₀ hν₀ hθ₀

/-- **Theorem 1.3(i)(a)** (`thm:main-explosion`).  The certified statement is
`Sandpile.Frozen.mean_growth_le_three`. -/
theorem Sandpile.mean_growth_le_three
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (hOS : ∀ (ΩB : Type) [MeasurableSpace ΩB], Sandpile.External.ContinuumOptimalStopping ΩB)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 L) := by
  exact Sandpile.Frozen.mean_growth_le_three hLocalCLT hStab hOS d hd hd3 ν hprob
    hmean hvar hvar' θ₀ hθ₀ hexp

/-- **Theorem 1.3(i)(b)** (`thm:main-explosion`).  The certified statement is
`Sandpile.Frozen.brownian_scaling_limit`. -/
theorem Sandpile.brownian_scaling_limit
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W P)
    (Z : ℝ → Sandpile.Continuum.Space d → Ω → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[P] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hZgrow : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P, ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k)
    (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω' → Sandpile.Continuum.Space d)
    (hB : ∀ x : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d x (B x) P')
    (hBc : ∀ (y : Sandpile.Continuum.Space d) (ω : Ω'), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (T : ℝ) (hT : 0 < T) :
    (∀ (m : ℕ) (x : Fin m → Sandpile.Continuum.Space d),
        TendstoInDistribution
          (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (j : Fin m) =>
            Sandpile.Continuum.multilinearInterp R
              (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) (x j))
          atTop
          (fun (ω : Ω) (j : Fin m) =>
            Sandpile.Continuum.brownianValue (B (x j)) P'
              (fun t y => Z t y ω)
              T (x j))
          (fun _ => Sandpile.centeredMassLaw d ν) P) ∧
      ∀ K : Set (Sandpile.Continuum.Space d), IsCompact K →
        (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
          Sandpile.centeredMassLaw d ν
              {σ | ∃ z ∈ K, M < |Sandpile.Continuum.multilinearInterp R
                (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z|} ≤
            ENNReal.ofReal ε) ∧
        (∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
          Sandpile.centeredMassLaw d ν
              {σ | ∃ z ∈ K, ∃ z' ∈ K, dist z z' < δ ∧
                η < |Sandpile.Continuum.multilinearInterp R
                    (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z -
                  Sandpile.Continuum.multilinearInterp R
                    (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) z'|} ≤
            ENNReal.ofReal ε) := by
  exact Sandpile.Frozen.brownian_scaling_limit hLocalCLT hStab d hd hd3 ν hmean hvar hvar' θ₀
    hθ₀ hexp Ω P W hW Z hZmod hZcont hZgrow Ω' P' B hB hBc hBm T hT

/-- **Theorem 1.3(ii)(a), first clause** (`thm:main-explosion`).  The certified statement is
`Sandpile.Frozen.mean_growth_four`. -/
theorem Sandpile.mean_growth_four
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℕ, 2 ≤ t →
      c * Real.log t ≤ Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t ∧
        Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t ≤ C * Real.log t := by
  exact Sandpile.Frozen.mean_growth_four ν hprob hmean hvar hvar' θ₀ hθ₀ hexp

/-- **Theorem 1.3(ii)(a), second clause** (`thm:main-explosion`).  The certified statement is
`Sandpile.Frozen.four_first_order`. -/
theorem Sandpile.four_first_order
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∀ x : Sandpile.Site 4,
      Tendsto (fun t : ℕ => ∫ σ, (Sandpile.odometer σ t x /
        Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t - 1) ^ 2
          ∂(Sandpile.centeredMassLaw 4 ν)) atTop (𝓝 0) ∧
      ∀ᵐ σ ∂(Sandpile.centeredMassLaw 4 ν),
        Tendsto (fun t : ℕ => Sandpile.odometer σ t x /
          Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t) atTop (𝓝 1) := by
  exact Sandpile.Frozen.four_first_order ν hprob hmean hvar hvar' θ₀ hθ₀ hexp

/-- **Theorem 1.3(ii)(b)** (`thm:main-explosion`).  The certified statement is
`Sandpile.Frozen.four_gaussian`. -/
theorem Sandpile.four_gaussian
    (hPaired : Sandpile.External.PairedLocalCLTFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    TendstoInDistribution
      (fun (t : ℕ) (σ : Sandpile.Site 4 → ℝ) =>
        (Sandpile.odometer σ t 0 - Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t) /
          Real.sqrt (Real.log t))
      atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal (4 * variance id ν / Real.pi ^ 2))) ∧
    Tendsto (fun t : ℕ =>
      variance (fun σ => Sandpile.odometer σ t 0) (Sandpile.centeredMassLaw 4 ν) / Real.log t)
      atTop (𝓝 (4 * variance id ν / Real.pi ^ 2)) := by
  exact Sandpile.Frozen.four_gaussian hPaired ν hmean hvar hvar' θ₀ hθ₀ hexp

/-- **Theorem 1.3(ii)(c)** (`thm:main-explosion`).  The certified statement is
`Sandpile.Frozen.four_sobolev`. -/
theorem Sandpile.four_sobolev
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site 4 → ℝ))
    (hMembrane : Sandpile.External.MembraneScalingLimitFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : 0 < s) :
    Sandpile.Continuum.TightInNegSobolev 4 s (Sandpile.centeredMassLaw 4 ν)
        (fun (R : ℝ) (σ : Sandpile.Site 4 → ℝ) =>
          Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊)) ∧
      ∀ D : Set (Sandpile.Continuum.Space 4), Sandpile.Continuum.IsDomain D →
        ∀ w : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsAveragingDensity D w →
          ∀ α : ℝ, 2 < α →
            (∀ φ : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsTestFn D φ →
                TendstoInDistribution
                  (fun (R : ℝ) (σ : Sandpile.Site 4 → ℝ) =>
                    Sandpile.Continuum.omegaRep D w
                      (Sandpile.Continuum.latticePairing R
                        (fun x => Sandpile.odometer σ ⌊R ^ α⌋₊ x -
                          Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)) φ)
                  atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw 4 ν)
                  (gaussianReal 0 (Real.toNNReal
                    (Sandpile.Continuum.omegaRep D w
                      (fun φ' => Sandpile.Continuum.omegaRep D w
                        (Sandpile.Continuum.membraneCov4 (variance id ν) φ') φ) φ)))) ∧
              ∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
                Sandpile.centeredMassLaw 4 ν
                    {σ | M < Sandpile.Continuum.negSobolevNorm 4 s D
                      (Sandpile.Continuum.omegaRep D w
                        (Sandpile.Continuum.latticePairing R
                          (fun x => Sandpile.odometer σ ⌊R ^ α⌋₊ x -
                            Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))} ≤
                  ENNReal.ofReal ε := by
  exact Sandpile.Frozen.four_sobolev hBesov hMembrane ν hmean hvar hvar'
    θ₀ hθ₀ hexp T hT s hs

/-- **Theorem 1.3(iii)(a)** (`thm:main-explosion`).  The certified statement is
`Sandpile.Frozen.high_first_order`. -/
theorem Sandpile.high_first_order
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    (∀ x : Sandpile.Site d,
      Tendsto (fun t : ℕ => ∫ σ, (Sandpile.odometer σ t x /
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t - 1) ^ 2
          ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 0) ∧
      ∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
        Tendsto (fun t : ℕ => Sandpile.odometer σ t x /
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 1)) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℕ in atTop,
      c * (Real.log t) ^ ((2 : ℝ) / d) ≤ Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t
    := by
  exact Sandpile.Frozen.high_first_order d hd ν hprob hmean hvar hvar' θ₀ hθ₀ hexp

/-- **Theorem 1.3(iii)(b)** (`thm:main-explosion`).  The certified statement is
`Sandpile.Frozen.high_tail`. -/
theorem Sandpile.high_tail
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (γ : ℝ) (hγ : 1 ≤ γ) (hγd : γ ≠ (d : ℝ) / 2)
    (htail : ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ᶠ s : ℝ in atTop,
      a * s ^ γ ≤ -Real.log (ν (Set.Iic (-s))).toReal ∧
        -Real.log (ν (Set.Iic (-s))).toReal ≤ b * s ^ γ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ t : ℕ in atTop,
      c * (Real.log t) ^ (1 / min γ ((d : ℝ) / 2)) ≤
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t ∧
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t ≤
          C * (Real.log t) ^ (1 / min γ ((d : ℝ) / 2)) := by
  exact Sandpile.Frozen.high_tail d hd ν hprob hmean hvar hvar' θ₀ hθ₀ hexp γ hγ hγd
    htail

/-- **Theorem 1.3(iii)(c)** (`thm:main-explosion`).  The certified statement is
`Sandpile.Frozen.high_sobolev_limit`. -/
theorem Sandpile.high_sobolev_limit
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hNormal : Sandpile.External.NormalComparison)
    (hLocalCLT : Sandpile.External.LocalCLT)
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤) :
    (∀ v : ℝ≥0, ν = gaussianReal 0 v →
        ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
          Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
            (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
              R ^ (((d : ℝ) - 4) / 2) *
                Sandpile.Continuum.latticePairing R
                  (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
                    Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ)
            (Sandpile.Continuum.weightedMembraneCov d (variance id ν) 1 T)) ∧
      ((∀ z : ℝ, ν {z} = 0) → (∃ b : ℝ, ν (Set.Ioi b) = 0) →
        ∀ α : ℝ, 2 < α →
          (∀ lam : ℝ, 0 < lam →
              Tendsto (fun r : ℝ =>
                  (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
                atTop (𝓝 (lam ^ (-α)))) →
          ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
            Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
              (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
                R ^ (((d : ℝ) - 4) / 2) *
                  Sandpile.Continuum.latticePairing R
                    (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
                      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ)
              (Sandpile.Continuum.weightedMembraneCov d (variance id ν) (1 - 1 / α) T)) := by
  exact Sandpile.Frozen.high_sobolev_limit hGaussConc hNormal
    hLocalCLT d hd hBesov ν hmean hvar hvar'

/-- **Theorem 1.3(iii)(d)** (`thm:main-explosion`).  The certified statement is
`Sandpile.Frozen.high_nonconvergence`. -/
theorem Sandpile.high_nonconvergence
    (hLocalCLT : Sandpile.External.LocalCLT)
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ)) :
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
  exact Sandpile.Frozen.high_nonconvergence hLocalCLT d hd hBesov
