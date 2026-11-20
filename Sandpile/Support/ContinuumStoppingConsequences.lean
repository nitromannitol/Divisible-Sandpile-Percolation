import Sandpile.External.ContinuumStoppingStabilityProved
import Sandpile.Support.MeanWithoutOptimalStopping

/-!
# Consequences of continuum stopping stability

The Brownian scaling limit, self-similarity, and low-dimensional mean and
variance asymptotics follow from the proved stopping stability theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

/-- The parabolic Brownian scaling limit. -/
theorem Sandpile.brownian_scaling_limit_proved
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
  exact Sandpile.Frozen.brownian_scaling_limit Sandpile.External.continuumStoppingStability_holds
    d hd hd3 ν hmean hvar hvar' θ₀ hθ₀ hexp Ω P W hW Z hZmod hZcont hZgrow Ω' P' B hB hBc hBm T hT

/-- Self-similarity of the continuum value. -/
theorem Sandpile.continuum_value_self_similar_proved
    (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[PW] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hZgrow : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k)
    {ΩB : Type u} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (hBc : ∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) :
    (∃ U : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ,
      (∀ T : ℝ, 0 < T → ∀ x : Sandpile.Continuum.Space d,
        Measurable (U T x) ∧
        U T x =ᵐ[PW] fun ω =>
          Sandpile.Continuum.continuumValue d Z B PB T x ω) ∧
      ∀ T : ℝ, 0 < T → ∀ x : Sandpile.Continuum.Space d,
        PW.map (U T x) = PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 0 ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧
      (∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
        Integrable (fun σ => Real.exp (θ *
          Sandpile.Continuum.rescaledOdometer d R 1 0 σ))
          (Sandpile.centeredMassLaw d ν) ∧
        ∫ σ, Real.exp (θ *
          Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
          ∂(Sandpile.centeredMassLaw d ν) ≤ M) ∧
      Integrable (fun ω => Real.exp (θ *
        Sandpile.Continuum.continuumValue d Z B PB 1 0 ω)) PW) ∧
    (∀ T : ℝ, 0 < T → ∀ x : Sandpile.Continuum.Space d, ∀ p : ℝ, 0 < p →
      Integrable (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB T x ω ^ p) PW ∧
      Integrable (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω ^ p) PW ∧
      ∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB T x ω ^ p ∂PW =
        T ^ (p * (4 - (d : ℝ)) / 4) *
          ∫ ω, Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω ^ p ∂PW ∧
      0 < ∫ ω, Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω ^ p ∂PW) := by
  exact Sandpile.Support.continuum_value_self_similar_without_optimal_stopping
    Sandpile.External.continuumStoppingStability_holds d hd0 hd ν hmean hvar hvar' θ₀ hθ₀ hexp
    PW W hW Z hZmod hZcont hZgrow PB B hB hBc hBm

/-- Mean and variance asymptotics below dimension four. -/
theorem Sandpile.dlt4_mean_asymptotic_proved
    (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[PW] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hZgrow : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k)
    {ΩB : Type u} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (hBc : ∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (T : ℝ) (hT : 0 < T) (x : Sandpile.Continuum.Space d) :
    (∀ R : ℝ, 1 ≤ R →
        MemLp (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ) 2
          (Sandpile.centeredMassLaw d ν)) ∧
      (∀ t : ℕ, MemLp (fun σ => Sandpile.odometer σ t 0) 2 (Sandpile.centeredMassLaw d ν)) ∧
      MemLp (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB T x ω) 2 PW ∧
      MemLp (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω) 2 PW ∧
      Tendsto (fun R : ℝ => ∫ σ, Sandpile.Continuum.rescaledOdometer d R T x σ
          ∂(Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB T x ω ∂PW)) ∧
      (∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB T x ω ∂PW =
        T ^ ((4 - (d : ℝ)) / 4) * ∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB 1 0 ω ∂PW) ∧
      Tendsto (fun R : ℝ => variance
          (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ)
          (Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (T ^ ((4 - (d : ℝ)) / 2) * variance
          (fun ω => Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω) PW)) ∧
      0 < variance (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω) PW ∧
      Tendsto (fun t : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t /
          ((∫ ω, Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω ∂PW) * (t : ℝ) ^ ((4 - (d : ℝ)) / 4)))
        atTop (𝓝 1) ∧
      Tendsto (fun t : ℕ =>
          variance (fun σ => Sandpile.odometer σ t 0) (Sandpile.centeredMassLaw d ν) /
          (variance (fun ω => Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω) PW * (t : ℝ) ^ ((4 - (d : ℝ)) / 2)))
        atTop (𝓝 1) := by
  exact Sandpile.Support.dlt4_mean_asymptotic_from_stability
    Sandpile.External.continuumStoppingStability_holds d hd0 hd ν hmean hvar hvar' θ₀ hθ₀ hexp
    PW W hW Z hZmod hZcont hZgrow PB B hB hBc hBm T hT x

/-- Mean odometer growth below dimension four. -/
theorem Sandpile.mean_growth_le_three_proved
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 L) :=
  Sandpile.mean_growth_le_three_from_stability Sandpile.External.continuumStoppingStability_holds
    d hd hd3 ν hprob hmean hvar hvar' θ₀ hθ₀ hexp
