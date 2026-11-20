import Sandpile.MainTheorems
import Sandpile.Frozen.MeanAsymptotic

/-!
# Mean growth without the optimal-stopping input

The continuum self-similarity and mean-growth conclusions follow from the
scaling limit and do not require a finite-horizon optimal-stopping theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open Sandpile.Continuum Sandpile.Support

universe u

/-- Continuum value self-similarity from the parabolic scaling limit. -/
theorem Sandpile.Support.continuum_value_self_similar_without_optimal_stopping
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
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
        Z B PB 1 0 ω ^ p ∂PW)
:= by
  exact Sandpile.Support.continuum_value_self_similar_of_parabolic_limit
    d hd0 hd ν hvar hvar' θ₀ hθ₀ hexp PW W hW Z hZmod hZcont PB B
    (fun T hT => Sandpile.Frozen.brownian_scaling_limit hStab d hd0 hd ν hmean
      hvar hvar' θ₀ hθ₀ hexp ΩW PW W hW Z hZmod hZcont hZgrow ΩB PB B hB hBc hBm T hT)

/-- Mean asymptotics from the scaling limit. -/
theorem Sandpile.Support.dlt4_mean_asymptotic_without_optimal_stopping
    (_hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (_hVarScale : Sandpile.External.VarianceScale)
    (d : ℕ) (hd0 : 0 < d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (ΩW : Type*) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d (variance id ν) W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (hZgrow : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)),
        |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k)
    (ΩB : Type u) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Space d → ℝ≥0 → ΩB → Space d)
    (hB : ∀ y : Space d, IsBrownian d y (B y) PB)
    (hBc : ∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (T : ℝ) (hT : 0 < T) (x : Space d) :
    (∀ R : ℝ, 1 ≤ R →
        MemLp (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ) 2
          (Sandpile.centeredMassLaw d ν)) ∧
      (∀ t : ℕ, MemLp (fun σ => Sandpile.odometer σ t 0) 2 (Sandpile.centeredMassLaw d ν)) ∧
      MemLp (fun ω => continuumValue d Z B PB T x ω) 2 PW ∧
      MemLp (fun ω => continuumValue d Z B PB 1 0 ω) 2 PW ∧
      Tendsto (fun R : ℝ => ∫ σ, Sandpile.Continuum.rescaledOdometer d R T x σ
          ∂(Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (∫ ω, continuumValue d Z B PB T x ω ∂PW)) ∧
      (∫ ω, continuumValue d Z B PB T x ω ∂PW =
        T ^ ((4 - (d : ℝ)) / 4) * ∫ ω, continuumValue d Z B PB 1 0 ω ∂PW) ∧
      Tendsto (fun R : ℝ => variance
          (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ)
          (Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (T ^ ((4 - (d : ℝ)) / 2) * variance
          (fun ω => continuumValue d Z B PB 1 0 ω) PW)) ∧
      0 < variance (fun ω => continuumValue d Z B PB 1 0 ω) PW ∧
      Tendsto (fun t : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t /
          ((∫ ω, continuumValue d Z B PB 1 0 ω ∂PW) * (t : ℝ) ^ ((4 - (d : ℝ)) / 4)))
        atTop (𝓝 1) ∧
      Tendsto (fun t : ℕ =>
          variance (fun σ => Sandpile.odometer σ t 0) (Sandpile.centeredMassLaw d ν) /
          (variance (fun ω => continuumValue d Z B PB 1 0 ω) PW * (t : ℝ) ^ ((4 - (d : ℝ)) / 2)))
        atTop (𝓝 1) := by
  have hd : 1 ≤ d := hd0
  have hν2 : 0 < variance (id : ℝ → ℝ) ν := ENNReal.toReal_pos hvar.ne' hvar'.ne
  have hsq : Integrable (fun z : ℝ => z ^ 2) ν := integrable_sq_of_evariance ν hvar'
  have hib := Sandpile.Frozen.brownian_scaling_limit hStab d hd hd3 ν hmean hvar hvar'
    θ₀ hθ₀ hexp ΩW PW W hW Z hZmod hZcont hZgrow ΩB PB B hB hBc hBm 1 one_pos
  have hres := tendstoInDistribution_rescaled_one_zero d ν PW PB Z B
    (hib.1 1 (fun _ => (0 : Space d)))
  have hself := Sandpile.Support.continuum_value_self_similar_without_optimal_stopping hStab d hd0 hd3 ν hmean
    hvar hvar' θ₀ hθ₀ hexp PW W hW Z hZmod hZcont hZgrow PB B hB hBc hBm
  obtain ⟨U, hU, hUlaw⟩ := hself.1
  obtain ⟨θ, hθ, ⟨M, hM⟩, hZexp⟩ := hself.2.1
  have hmeasT : ∀ (S : ℝ), 0 < S → ∀ y : Space d,
      AEMeasurable (fun ω => continuumValue d Z B PB S y ω) PW := fun S hS y =>
    ((hU S hS y).1.aemeasurable).congr (hU S hS y).2
  have hlaw : ∀ (S : ℝ), 0 < S → ∀ y : Space d,
      PW.map (fun ω => continuumValue d Z B PB S y ω)
        = PW.map (fun ω => S ^ ((4 - (d : ℝ)) / 4) * continuumValue d Z B PB 1 0 ω) := by
    intro S hS y
    calc PW.map (fun ω => continuumValue d Z B PB S y ω)
        = PW.map (U S y) := (Measure.map_congr (hU S hS y).2).symm
      _ = PW.map (fun ω => S ^ ((4 - (d : ℝ)) / 4) * U 1 0 ω) := hUlaw S hS y
      _ = PW.map (fun ω => S ^ ((4 - (d : ℝ)) / 4) *
            continuumValue d Z B PB 1 0 ω) := by
          refine Measure.map_congr ?_
          filter_upwards [(hU 1 one_pos 0).2] with ω hω
          rw [hω]
  set C : ℝ := max M (∫ ω, Real.exp (θ * continuumValue d Z B PB 1 0 ω) ∂PW) with hC
  exact dlt4_mean_asymptotic_of_inputs d hd hd3 ν hsq PW PB W hW hν2 Z hZmod hZcont B
    hres hmeasT hlaw θ C hθ (fun R hR => (hM R hR).1)
    (fun R hR => le_trans (hM R hR).2 (le_max_left _ _)) hZexp (le_max_right _ _) T hT x

/-- Origin mean and variance limits from the scaling limit. -/
theorem Sandpile.Support.mean_variance_limit_at_origin_without_optimal_stopping
    (_hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (_hVarScale : Sandpile.External.VarianceScale)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Space d → ℝ≥0 → ΩB → Space d)
    (hB : ∀ y : Space d, IsBrownian d y (B y) PB)
    (hBc : ∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) :
    ∃ Z : ℝ → Space d → ΩW → ℝ,
      MemLp (fun ω => continuumValue d Z B PB 1 0 ω) 2 PW ∧
      (∀ᵐ ω ∂PW, 0 ≤ continuumValue d Z B PB 1 0 ω) ∧
      0 < variance (fun ω => continuumValue d Z B PB 1 0 ω) PW ∧
      0 < ∫ ω, continuumValue d Z B PB 1 0 ω ∂PW ∧
      Tendsto (fun R : ℝ => ∫ σ, Sandpile.Continuum.rescaledOdometer d R 1 0 σ
        ∂(Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (∫ ω, continuumValue d Z B PB 1 0 ω ∂PW)) ∧
      Tendsto (fun R : ℝ => variance
        (fun σ => Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
        (Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (variance (fun ω => continuumValue d Z B PB 1 0 ω) PW)) := by
  have hd0 : 0 < d := hd
  have hν2 : 0 < variance (id : ℝ → ℝ) ν := ENNReal.toReal_pos hvar.ne' hvar'.ne
  have hsq : Integrable (fun z : ℝ => z ^ 2) ν := integrable_sq_of_evariance ν hvar'
  obtain ⟨Z, hZmod, hZcont, hZgrow⟩ :=
    exists_continuous_version_growth hd hd3 hν2.le PW W hW
  have hib := Sandpile.Frozen.brownian_scaling_limit hStab d hd hd3 ν hmean hvar hvar'
    θ₀ hθ₀ hexp ΩW PW W hW Z hZmod hZcont hZgrow ΩB PB B hB hBc hBm 1 one_pos
  have hres := tendstoInDistribution_rescaled_one_zero d ν PW PB Z B
    (hib.1 1 (fun _ => (0 : Space d)))
  have hself := Sandpile.Support.continuum_value_self_similar_without_optimal_stopping hStab d hd0 hd3 ν hmean
    hvar hvar' θ₀ hθ₀ hexp PW W hW Z hZmod hZcont hZgrow PB B hB hBc hBm
  obtain ⟨θ, hθ, ⟨M, hM⟩, hZexp⟩ := hself.2.1
  set C : ℝ := max M (∫ ω, Real.exp (θ * continuumValue d Z B PB 1 0 ω) ∂PW) with hC
  obtain ⟨hZL2, hZnn, hmean0, hvar0⟩ :=
    tendsto_moments_rescaled_of_conv d hd ν hsq PW PB Z B hres θ C hθ
      (fun R hR => (hM R hR).1)
      (fun R hR => le_trans (hM R hR).2 (le_max_left _ _))
      hZexp (le_max_right _ _)
  have hVpos : 0 < variance (fun ω => continuumValue d Z B PB 1 0 ω) PW :=
    variance_continuumValue_pos PW PB W hW hd hd3 hν2 Z hZmod hZcont B hZL2
  exact ⟨Z, hZL2, hZnn, hVpos,
    integral_pos_of_ae_nonneg_of_variance_pos PW _ hZL2 hZnn hVpos, hmean0, hvar0⟩

/-- **Theorem 1.3(i)(a), fully wired.**  The rescaled mean converges to a limit in
`(0,∞)`. -/
theorem Sandpile.Support.mean_growth_le_three_without_optimal_stopping
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (hVarScale : Sandpile.External.VarianceScale)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 L) := by
  have := hprob
  refine mean_growth_le_three_of_variance_pos d ν ?_
  intro ΩW _ PW _ W hW ΩB _ PB _ B hB hBc hBm
  obtain ⟨Z, hZL2, hZnn, hVpos, hLpos, hmean0, _⟩ :=
    Sandpile.Support.mean_variance_limit_at_origin_without_optimal_stopping hLocalCLT hStab hVarScale d hd hd3 ν hmean hvar hvar'
      θ₀ hθ₀ hexp ΩW PW W hW ΩB PB B hB hBc hBm
  exact ⟨Z, hZL2, hZnn, hVpos,
    tendsto_mean_ratio_of_rescaled d ν _ (ne_of_gt hLpos) hmean0⟩

/-- Mean asymptotics with the stopping stability input. -/
theorem Sandpile.Support.dlt4_mean_asymptotic_from_stability
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
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
        atTop (𝓝 1)
:= by
  have hVarScale : Sandpile.External.VarianceScale := Sandpile.External.varianceScale
  exact Sandpile.Support.dlt4_mean_asymptotic_without_optimal_stopping Sandpile.External.localCLT hStab hVarScale
    d hd0 hd ν hmean hvar hvar' θ₀ hθ₀ hexp ΩW PW W hW Z hZmod hZcont hZgrow ΩB PB B hB hBc
    hBm T hT x

/-- Mean growth below dimension four from stopping stability. -/
theorem Sandpile.mean_growth_le_three_from_stability
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 L)
:= Sandpile.Support.mean_growth_le_three_without_optimal_stopping Sandpile.External.localCLT hStab
    Sandpile.External.varianceScale d hd hd3 ν hprob hmean hvar hvar' θ₀ hθ₀ hexp
