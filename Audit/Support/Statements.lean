import Mathlib
import Audit.Support.Vocabulary

/-!
# The audited statements in the challenge environment

Each audited statement, elaborated as a proposition in exactly the environment
of the challenges: this module imports only Mathlib and the vocabulary.
`Audit/StatementRegression.lean` checks that each solution theorem has
exactly this type, so that no repository name or instance leaks into a
solution statement.
-/

namespace SandpileAudit.Statements

open SandpileAudit
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

-- The hypothesis names are kept so that the text matches the challenges.
set_option linter.unusedVariables false

/-- The statement of `Audit/Nontriviality/Challenge.lean`. -/
def percolation_below_criticality : Prop :=
  ∀
    (hBallGreen : External.BallGreenBounds)
    (hRSW : External.PlanarRSW)
    (hLSS : External.LSSDomination)
    (hBoundary : External.ExteriorBoundaryConnected)
    (hRSWc : External.ContinuumRSW)
    (hPitt : External.PittGaussianFKG)
    (hOcc : External.BallOccupationDensity)
    (hLocalCLT : External.LocalCLT)
    (hCube : External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (μ : ℝ → Measure ℝ) (hprob : ∀ ρ, IsProbabilityMeasure (μ ρ))
    (hmean : ∀ ρ ∈ Set.Ioc (0 : ℝ) 1, ∫ s, s ∂(μ ρ) = ρ)
    (ρ₀ ν₀ θ₀ K₀ : ℝ) (hρ₀ : ρ₀ ∈ Set.Ioo (0 : ℝ) 1) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀)
    (hvar : ∀ ρ ∈ Set.Ico ρ₀ 1, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (μ ρ))
    (hexpint : ∀ ρ ∈ Set.Ico ρ₀ 1, Integrable (fun s => Real.exp (θ₀ * |s - ρ|)) (μ ρ))
    (hexp : ∀ ρ ∈ Set.Ico ρ₀ 1, ∫ s, Real.exp (θ₀ * |s - ρ|) ∂(μ ρ) ≤ K₀),
    ∃ ρPlus ∈ Set.Ico ρ₀ 1, ∀ ρ ∈ Set.Ioo ρPlus 1,
      ∀ᵐ σ ∂(massLaw d (μ ρ)),
        HasInfiniteComponent (toppledSet σ)

/-- The statement of `Audit/CriticalLevels/Challenge.lean`. -/
def critical_level_percolation : Prop :=
  ∀
    (hBallGreen : External.BallGreenBounds)
    (hGreenHigh : External.GreenBoundsHigh)
    (hVarScale : External.VarianceScale)
    (hRSW : External.PlanarRSW)
    (hLSS : External.LSSDomination)
    (hBoundary : External.ExteriorBoundaryConnected)
    (hRSWc : External.ContinuumRSW)
    (hPitt : External.PittGaussianFKG)
    (hOcc : External.BallOccupationDensity)
    (hLocalCLT : External.LocalCLT)
    (hCube : External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀),
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(massLaw d μ),
          HasInfiniteComponent
            {x | c * criticalScale d t < odometer σ t x}

/-- The statement of `Audit/MeanGrowthLow/Challenge.lean`. -/
def mean_growth_le_three : Prop :=
  ∀
    (hLocalCLT : External.LocalCLT)
    (hStab : External.ContinuumStoppingStability.{0})
    (hVarScale : External.VarianceScale)
    (hOS : ∀ (ΩB : Type) [MeasurableSpace ΩB], External.ContinuumOptimalStopping ΩB)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν),
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        meanOdometer (centeredMassLaw d ν) t) atTop (𝓝 L)

/-- The statement of `Audit/BrownianScalingLimit/Challenge.lean`. -/
def brownian_scaling_limit : Prop :=
  ∀
    (hLocalCLT : External.LocalCLT)
    (hStab : External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (Continuum.Space d → ℝ) → Ω → ℝ)
    (hW : Continuum.IsWhiteNoise d W P)
    (Z : ℝ → Continuum.Space d → Ω → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Continuum.Space d),
      Z t x =ᵐ[P] fun ω =>
        Continuum.gaussianPotential d (variance id ν) W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × Continuum.Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Continuum.Space d))))
    (hZgrow : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P, ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Continuum.Space d)),
        |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k)
    (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (B : Continuum.Space d → ℝ≥0 → Ω' → Continuum.Space d)
    (hB : ∀ x : Continuum.Space d, Continuum.IsBrownian d x (B x) P')
    (hBc : ∀ (y : Continuum.Space d) (ω : Ω'), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (T : ℝ) (hT : 0 < T),
    (∀ (m : ℕ) (x : Fin m → Continuum.Space d),
        TendstoInDistribution
          (fun (R : ℝ) (σ : Site d → ℝ) (j : Fin m) =>
            Continuum.multilinearInterp R
              (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) (x j))
          atTop
          (fun (ω : Ω) (j : Fin m) =>
            Continuum.brownianValue (B (x j)) P'
              (fun t y => Z t y ω)
              T (x j))
          (fun _ => centeredMassLaw d ν) P) ∧
      ∀ K : Set (Continuum.Space d), IsCompact K →
        (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
          centeredMassLaw d ν
              {σ | ∃ z ∈ K, M < |Continuum.multilinearInterp R
                (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z|} ≤
            ENNReal.ofReal ε) ∧
        (∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
          centeredMassLaw d ν
              {σ | ∃ z ∈ K, ∃ z' ∈ K, dist z z' < δ ∧
                η < |Continuum.multilinearInterp R
                    (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z -
                  Continuum.multilinearInterp R
                    (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z'|} ≤
            ENNReal.ofReal ε)

/-- The statement of `Audit/MeanGrowthFour/Challenge.lean`. -/
def mean_growth_four : Prop :=
  ∀
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν),
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℕ, 2 ≤ t →
      c * Real.log t ≤ meanOdometer (centeredMassLaw 4 ν) t ∧
        meanOdometer (centeredMassLaw 4 ν) t ≤ C * Real.log t

/-- The statement of `Audit/FourFirstOrder/Challenge.lean`. -/
def four_first_order : Prop :=
  ∀
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν),
    ∀ x : Site 4,
      Tendsto (fun t : ℕ => ∫ σ, (odometer σ t x /
        meanOdometer (centeredMassLaw 4 ν) t - 1) ^ 2
          ∂(centeredMassLaw 4 ν)) atTop (𝓝 0) ∧
      ∀ᵐ σ ∂(centeredMassLaw 4 ν),
        Tendsto (fun t : ℕ => odometer σ t x /
          meanOdometer (centeredMassLaw 4 ν) t) atTop (𝓝 1)

/-- The statement of `Audit/FourGaussian/Challenge.lean`. -/
def four_gaussian : Prop :=
  ∀
    (hPaired : External.PairedLocalCLTFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν),
    TendstoInDistribution
      (fun (t : ℕ) (σ : Site 4 → ℝ) =>
        (odometer σ t 0 - meanOdometer (centeredMassLaw 4 ν) t) /
          Real.sqrt (Real.log t))
      atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal (4 * variance id ν / Real.pi ^ 2))) ∧
    Tendsto (fun t : ℕ =>
      variance (fun σ => odometer σ t 0) (centeredMassLaw 4 ν) / Real.log t)
      atTop (𝓝 (4 * variance id ν / Real.pi ^ 2))

/-- The statement of `Audit/FourSobolev/Challenge.lean`. -/
def four_sobolev : Prop :=
  ∀
    (hHeatKernel : External.HeatKernelBounds)
    (hVarScale : External.VarianceScale)
    (hBesov : External.ContinuumBesovTightness (Site 4 → ℝ))
    (hMembrane : External.MembraneScalingLimitFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : 0 < s),
    Continuum.TightInNegSobolev 4 s (centeredMassLaw 4 ν)
        (fun (R : ℝ) (σ : Site 4 → ℝ) =>
          Continuum.latticePairing R
            (fun x => odometer σ ⌊T * R ^ 2⌋₊ x -
              meanOdometer (centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊)) ∧
      ∀ D : Set (Continuum.Space 4), Continuum.IsDomain D →
        ∀ w : Continuum.Space 4 → ℝ, Continuum.IsAveragingDensity D w →
          ∀ α : ℝ, 2 < α →
            (∀ φ : Continuum.Space 4 → ℝ, Continuum.IsTestFn D φ →
                TendstoInDistribution
                  (fun (R : ℝ) (σ : Site 4 → ℝ) =>
                    Continuum.omegaRep D w
                      (Continuum.latticePairing R
                        (fun x => odometer σ ⌊R ^ α⌋₊ x -
                          meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)) φ)
                  atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw 4 ν)
                  (gaussianReal 0 (Real.toNNReal
                    (Continuum.omegaRep D w
                      (fun φ' => Continuum.omegaRep D w
                        (Continuum.membraneCov4 (variance id ν) φ') φ) φ)))) ∧
              ∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
                centeredMassLaw 4 ν
                    {σ | M < Continuum.negSobolevNorm 4 s D
                      (Continuum.omegaRep D w
                        (Continuum.latticePairing R
                          (fun x => odometer σ ⌊R ^ α⌋₊ x -
                            meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))} ≤
                  ENNReal.ofReal ε

/-- The statement of `Audit/HighFirstOrder/Challenge.lean`. -/
def high_first_order : Prop :=
  ∀
    (hGreenHigh : External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν),
    (∀ x : Site d,
      Tendsto (fun t : ℕ => ∫ σ, (odometer σ t x /
        meanOdometer (centeredMassLaw d ν) t - 1) ^ 2
          ∂(centeredMassLaw d ν)) atTop (𝓝 0) ∧
      ∀ᵐ σ ∂(centeredMassLaw d ν),
        Tendsto (fun t : ℕ => odometer σ t x /
          meanOdometer (centeredMassLaw d ν) t) atTop (𝓝 1)) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℕ in atTop,
      c * (Real.log t) ^ ((2 : ℝ) / d) ≤ meanOdometer (centeredMassLaw d ν) t

/-- The statement of `Audit/HighTail/Challenge.lean`. -/
def high_tail : Prop :=
  ∀
    (hGreenHigh : External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (γ : ℝ) (hγ : 1 ≤ γ) (hγd : γ ≠ (d : ℝ) / 2)
    (htail : ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ᶠ s : ℝ in atTop,
      a * s ^ γ ≤ -Real.log (ν (Set.Iic (-s))).toReal ∧
        -Real.log (ν (Set.Iic (-s))).toReal ≤ b * s ^ γ),
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ t : ℕ in atTop,
      c * (Real.log t) ^ (1 / min γ ((d : ℝ) / 2)) ≤
          meanOdometer (centeredMassLaw d ν) t ∧
        meanOdometer (centeredMassLaw d ν) t ≤
          C * (Real.log t) ^ (1 / min γ ((d : ℝ) / 2))

/-- The statement of `Audit/HighSobolevLimit/Challenge.lean`. -/
def high_sobolev_limit : Prop :=
  ∀
    (hHeatKernel : External.HeatKernelBounds)
    (hGreenHigh : External.GreenBoundsHigh)
    (hGaussConc : External.GaussianLipschitzConcentration)
    (hNormal : External.NormalComparison)
    (hInter : External.IntersectionSecondMoment)
    (hLocalCLT : External.LocalCLT)
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : External.ContinuumBesovTightness (Site d → ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤),
    (∀ v : ℝ≥0, ν = gaussianReal 0 v →
        ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
          Continuum.TendstoInNegSobolev d s (centeredMassLaw d ν)
            (fun (R : ℝ) (σ : Site d → ℝ) (φ : Continuum.Space d → ℝ) =>
              R ^ (((d : ℝ) - 4) / 2) *
                Continuum.latticePairing R
                  (fun x => odometer σ ⌊T * R ^ 2⌋₊ x -
                    meanOdometer (centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ)
            (Continuum.weightedMembraneCov d (variance id ν) 1 T)) ∧
      ((∀ z : ℝ, ν {z} = 0) → (∃ b : ℝ, ν (Set.Ioi b) = 0) →
        ∀ α : ℝ, 2 < α →
          (∀ lam : ℝ, 0 < lam →
              Tendsto (fun r : ℝ =>
                  (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
                atTop (𝓝 (lam ^ (-α)))) →
          ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
            Continuum.TendstoInNegSobolev d s (centeredMassLaw d ν)
              (fun (R : ℝ) (σ : Site d → ℝ) (φ : Continuum.Space d → ℝ) =>
                R ^ (((d : ℝ) - 4) / 2) *
                  Continuum.latticePairing R
                    (fun x => odometer σ ⌊T * R ^ 2⌋₊ x -
                      meanOdometer (centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ)
              (Continuum.weightedMembraneCov d (variance id ν) (1 - 1 / α) T))

/-- The statement of `Audit/HighNonconvergence/Challenge.lean`. -/
def high_nonconvergence : Prop :=
  ∀
    (hInter : External.IntersectionSecondMoment)
    (hLocalCLT : External.LocalCLT)
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : External.ContinuumBesovTightness (Site d → ℝ)),
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ [_i : IsProbabilityMeasure ν],
      (∫ z, z ∂ν = 0) ∧ variance id ν = 1 ∧
      (∃ p : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ (∀ z : ℝ, 0 < p z) ∧
        ν = volume.withDensity fun z => ENNReal.ofReal (p z)) ∧
      (∃ θ₀ : ℝ, 0 < θ₀ ∧ Integrable (fun z => Real.exp (θ₀ * |z|)) ν) ∧
      ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
        Continuum.TightInNegSobolev d s (centeredMassLaw d ν)
            (Continuum.diffusiveFluctuation (centeredMassLaw d ν) T) ∧
          (∃ (I : Set ℝ) (K : ℝ → (Continuum.Space d → ℝ) →
              (Continuum.Space d → ℝ) → ℝ),
            ¬ I.Countable ∧
              (∀ κ ∈ I, ∀ κ' ∈ I, κ ≠ κ' →
                ∃ φ : Continuum.Space d → ℝ,
                  Continuum.IsTestFn Set.univ φ ∧
                    gaussianReal 0 (Real.toNNReal (K κ φ φ)) ≠
                      gaussianReal 0 (Real.toNNReal (K κ' φ φ))) ∧
              ∀ κ ∈ I, ∃ Rs : ℕ → ℝ, Tendsto Rs atTop atTop ∧
                ∀ φ : Continuum.Space d → ℝ,
                  Continuum.IsTestFn Set.univ φ →
                    TendstoInDistribution
                      (fun (k : ℕ) (σ : Site d → ℝ) =>
                        Continuum.diffusiveFluctuation
                          (centeredMassLaw d ν) T (Rs k) σ φ)
                      atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw d ν)
                      (gaussianReal 0 (Real.toNNReal (K κ φ φ)))) ∧
          ¬ ∃ K : (Continuum.Space d → ℝ) →
              (Continuum.Space d → ℝ) → ℝ,
            Continuum.TendstoInNegSobolev d s (centeredMassLaw d ν)
              (Continuum.diffusiveFluctuation (centeredMassLaw d ν) T) K

end SandpileAudit.Statements
