import Sandpile.Support.MeanALimit
import Sandpile.Support.MeanAPosVar
import Sandpile.Support.MeanAInterp
import Sandpile.Support.MeanAScale
import Sandpile.Support.ContValueMemLp
import Sandpile.Support.ContLawTransfer

/-!
# Assembling `cor:dlt4-mean-asymptotic` from the scaling limit and self-similarity

`cor:dlt4-mean-asymptotic` (`sandpile.tex:2034-2052`) assembled from the two statements the
paper derives it from: the parabolic scaling limit `thm:main-explosion`(i)(b) and the
self-similarity and uniform exponential moment of `prop:continuum-value-selfsimilar`. The
corollary is stated at every `(T,x)`, but the scaling limit is only ever used at `(1,0)`,
because the rescaled odometer satisfies the parabolic scaling identities
`E𝒰_R(T,x) = T^{(4-d)/4}E𝒰_{R√T}(1,0)` and `Var𝒰_R(T,x) = T^{(4-d)/2}Var𝒰_{R√T}(1,0)` exactly
(`MeanAScale`), and the limit satisfies the corresponding identities by the law identity of
`prop:continuum-value-selfsimilar`. At `(1,0)` the rescaled odometer is the interpolated field
of part (i)(b) read at the origin with no interpolation error (`MeanAInterp`), so the two
limits at a general `(T,x)` follow from the two limits at `(1,0)`. The positivity of the
limiting variance is `MeanAPosVar`, and the positivity of the limiting mean follows from it and
the nonnegativity of the value.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- **The scaling limit at `(1,0)`, as a statement about the rescaled odometer.**
Clause 1 of `thm:main-explosion`(i)(b) at `T = 1`, one point, the origin,
projected to the real line and restricted to the scales `R ≥ 1`.  At the origin
the interpolated field IS the rescaled odometer, so nothing is approximated. -/
theorem tendstoInDistribution_rescaled_one_zero {ΩW ΩB : Type*} [MeasurableSpace ΩW]
    [MeasurableSpace ΩB] (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (PW : Measure ΩW) [IsProbabilityMeasure PW] (PB : Measure ΩB)
    (Z : ℝ → Space d → ΩW → ℝ) (B : Space d → ℝ≥0 → ΩB → Space d)
    (hconvFD : TendstoInDistribution
      (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (_ : Fin 1) =>
        Sandpile.Continuum.multilinearInterp R
          (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊(1 : ℝ) * R ^ 2⌋₊ y)
          (0 : Space d))
      atTop
      (fun (ω : ΩW) (_ : Fin 1) =>
        Sandpile.Continuum.brownianValue (B 0) PB (fun t y => Z t y ω) 1 0)
      (fun _ => Sandpile.centeredMassLaw d ν) PW) :
    TendstoInDistribution
      (fun (r : Set.Ici (1 : ℝ)) (σ : Sandpile.Site d → ℝ) =>
        Sandpile.Continuum.rescaledOdometer d (r : ℝ) 1 0 σ)
      atTop (fun ω => continuumValue d Z B PB 1 0 ω)
      (fun _ => Sandpile.centeredMassLaw d ν) PW := by
  have h1 := tendstoInDistribution_comp (fun r : Set.Ici (1 : ℝ) => (r : ℝ))
    (tendsto_val_Ici_atTop 1) hconvFD
  have h2 := h1.continuous_comp (g := fun v : Fin 1 → ℝ => v 0) (continuous_apply 0)
  refine h2.congr (fun r => Filter.Eventually.of_forall fun σ => ?_)
    (Filter.Eventually.of_forall fun ω => rfl)
  have hr : (r : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one r.2)
  exact (rescaledOdometer_zero_eq_multilinearInterp d (r : ℝ) 1 hr σ).symm

/-- **`cor:dlt4-mean-asymptotic` from its two inputs.**  The convergence in
distribution of the rescaled odometer at the origin is clause 1 of
`thm:main-explosion`(i)(b) at `T = 1`; the law identity, the uniform exponential
moment and the exponential moment of the limit are clauses 1 and 2 of
`prop:continuum-value-selfsimilar`. -/
theorem dlt4_mean_asymptotic_of_inputs {ΩW ΩB : Type*} [MeasurableSpace ΩW]
    [MeasurableSpace ΩB] (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    (PW : Measure ΩW) [IsProbabilityMeasure PW] (PB : Measure ΩB)
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    {ν2 : ℝ} (hν2 : 0 < ν2)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (B : Space d → ℝ≥0 → ΩB → Space d)
    (hres : TendstoInDistribution
      (fun (r : Set.Ici (1 : ℝ)) (σ : Sandpile.Site d → ℝ) =>
        Sandpile.Continuum.rescaledOdometer d (r : ℝ) 1 0 σ)
      atTop (fun ω => continuumValue d Z B PB 1 0 ω)
      (fun _ => Sandpile.centeredMassLaw d ν) PW)
    (hmeasT : ∀ (S : ℝ), 0 < S → ∀ y : Space d,
      AEMeasurable (fun ω => continuumValue d Z B PB S y ω) PW)
    (hlaw : ∀ (S : ℝ), 0 < S → ∀ y : Space d,
      PW.map (fun ω => continuumValue d Z B PB S y ω)
        = PW.map (fun ω => S ^ ((4 - (d : ℝ)) / 4) * continuumValue d Z B PB 1 0 ω))
    (θ C : ℝ) (hθ : 0 < θ)
    (hXexp : ∀ R : ℝ, 1 ≤ R →
      Integrable (fun σ => Real.exp (θ * Sandpile.Continuum.rescaledOdometer d R 1 0 σ))
        (Sandpile.centeredMassLaw d ν))
    (hXexpC : ∀ R : ℝ, 1 ≤ R →
      ∫ σ, Real.exp (θ * Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
        ∂(Sandpile.centeredMassLaw d ν) ≤ C)
    (hZexp : Integrable (fun ω => Real.exp (θ * continuumValue d Z B PB 1 0 ω)) PW)
    (hZexpC : ∫ ω, Real.exp (θ * continuumValue d Z B PB 1 0 ω) ∂PW ≤ C)
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
  obtain ⟨hZL2, hZnn, hmean0, hvar0⟩ :=
    tendsto_moments_rescaled_of_conv d hd ν hsq PW PB Z B hres θ C hθ hXexp hXexpC hZexp hZexpC
  set L : ℝ := ∫ ω, continuumValue d Z B PB 1 0 ω ∂PW with hL
  set V : ℝ := variance (fun ω => continuumValue d Z B PB 1 0 ω) PW with hV
  have hVpos : 0 < V :=
    variance_continuumValue_pos PW PB W hW hd hd3 hν2 Z hZmod hZcont B hZL2
  have hLpos : 0 < L :=
    integral_pos_of_ae_nonneg_of_variance_pos PW _ hZL2 hZnn hVpos
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  -- clause 6, the mean identity of the limit
  have hclause6 : ∫ ω, continuumValue d Z B PB T x ω ∂PW
      = T ^ ((4 - (d : ℝ)) / 4) * L :=
    integral_continuumValue_of_map_eq d Z B PB PW T x ((4 - (d : ℝ)) / 4)
      (hmeasT T hT x) hZL2.aemeasurable (hlaw T hT x)
  -- the variance identity of the limit
  have hvarid : variance (fun ω => continuumValue d Z B PB T x ω) PW
      = (T ^ ((4 - (d : ℝ)) / 4)) ^ 2 * V :=
    variance_continuumValue_of_map_eq d Z B PB PW T x ((4 - (d : ℝ)) / 4)
      (hmeasT T hT x) hZL2.aemeasurable (hlaw T hT x)
  -- clause 5, the mean limit at `(T,x)`
  have hscale : Tendsto (fun R : ℝ => R * Real.sqrt T) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hsT
  have hmeanT : Tendsto (fun R : ℝ => ∫ σ,
      Sandpile.Continuum.rescaledOdometer d R T x σ ∂(Sandpile.centeredMassLaw d ν))
      atTop (𝓝 (T ^ ((4 - (d : ℝ)) / 4) * L)) := by
    have h1 : Tendsto (fun R : ℝ => T ^ ((4 - (d : ℝ)) / 4) *
        ∫ σ, Sandpile.Continuum.rescaledOdometer d (R * Real.sqrt T) 1 0 σ
          ∂(Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (T ^ ((4 - (d : ℝ)) / 4) * L)) := (hmean0.comp hscale).const_mul _
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (integral_rescaledOdometer_scale d ν R T hR hT x).symm
  -- clause 7, the variance limit at `(T,x)`
  have hvarT : Tendsto (fun R : ℝ => variance
      (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ)
      (Sandpile.centeredMassLaw d ν)) atTop
      (𝓝 (T ^ ((4 - (d : ℝ)) / 2) * V)) := by
    have h1 : Tendsto (fun R : ℝ => T ^ ((4 - (d : ℝ)) / 2) *
        variance (fun σ => Sandpile.Continuum.rescaledOdometer d
          (R * Real.sqrt T) 1 0 σ) (Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (T ^ ((4 - (d : ℝ)) / 2) * V)) := (hvar0.comp hscale).const_mul _
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (variance_rescaledOdometer_scale d ν R T hR hT x).symm
  obtain ⟨hratio1, hratio2⟩ :=
    dlt4_mean_asymptotic_ratios d ν L V (ne_of_gt hLpos) (ne_of_gt hVpos) hmean0 hvar0
  refine ⟨fun R _ => memLp_rescaledOdometer_centered d hd ν hsq R T x,
    fun t => memLp_odometer_nat_centered d hd ν hsq t,
    memLp_continuumValue_T d Z B PB PW T x ((4 - (d : ℝ)) / 4) hZL2
      (hmeasT T hT x) (hlaw T hT x),
    hZL2, ?_, hclause6, hvarT, hVpos, hratio1, hratio2⟩
  rw [hclause6]
  exact hmeanT

end Sandpile.Support
