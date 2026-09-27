/-
`cor:dlt4-mean-asymptotic` (`sandpile.tex:2034-2052`) wired to the two frozen
statements it is derived from, on realization spaces where both apply.

`MeanAAssembly` proves the corollary's ten clauses from four inputs: the
convergence in distribution of the rescaled odometer at the origin, the
measurability and the law identity of the continuum value, and the two
exponential moments.  Here those inputs are supplied by
`thm:main-explosion`(i)(b) at `T = 1` and by the three clauses of
`prop:continuum-value-selfsimilar`, so that nothing is assumed beyond the two
statements the paper's own sentence names (`sandpile.tex:2030-2032`) and the
cited inputs those two carry.
-/
import Sandpile.Support.MeanAAssembly
import Sandpile.Support.Dgt4OriginProb
import Sandpile.Frozen.BrownianScalingLimit
import Sandpile.Frozen.ContinuumValueSelfSimilar

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

namespace Sandpile.Support

open Sandpile.Continuum

/-- **`cor:dlt4-mean-asymptotic` from `thm:main-explosion`(i)(b) and
`prop:continuum-value-selfsimilar`.** -/
theorem dlt4_mean_asymptotic_wired
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
    (hOS : Sandpile.External.ContinuumOptimalStopping ΩB)
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
  have hself := Sandpile.Frozen.continuum_value_self_similar hStab d hd0 hd3 ν hmean
    hvar hvar' θ₀ hθ₀ hexp PW W hW Z hZmod hZcont hZgrow PB hOS B hB hBc hBm
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

end Sandpile.Support
