/- Positive power moments of the continuum value from its exponential moment and law. -/
import Sandpile.Support.MainExplAnnulus
import Sandpile.Support.MeanAPosVar
import Sandpile.Support.ContClause3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support
open Sandpile.Continuum

/-- Exponential integrability gives every positive power moment of the value. -/
theorem integrable_rpow_continuumValue_of_exp {ΩW ΩB : Type*}
    [MeasurableSpace ΩW] [MeasurableSpace ΩB] (d : ℕ)
    (PW : Measure ΩW) [IsProbabilityMeasure PW] (PB : Measure ΩB)
    (Z : ℝ → Space d → ΩW → ℝ) (B : Space d → ℝ≥0 → ΩB → Space d)
    (T : ℝ) (x : Space d) (θ : ℝ) (hθ : 0 < θ)
    (hmeas : AEMeasurable (continuumValue d Z B PB T x) PW)
    (hnn : ∀ᵐ ω ∂PW, 0 ≤ continuumValue d Z B PB T x ω)
    (hexp : Integrable (fun ω => Real.exp (θ * continuumValue d Z B PB T x ω)) PW)
    (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun ω => continuumValue d Z B PB T x ω ^ p) PW := by
  let U := continuumValue d Z B PB T x
  haveI : IsProbabilityMeasure (PW.map U) := Measure.isProbabilityMeasure_map hmeas
  have habs : Integrable (fun ω => Real.exp (θ * |U ω|)) PW := by
    refine hexp.congr ?_
    filter_upwards [hnn] with ω hω
    rw [abs_of_nonneg hω]
  have hpush : Integrable (fun z : ℝ => Real.exp (θ * |z|)) (PW.map U) :=
    (integrable_map_measure (by fun_prop) hmeas).2 habs
  have hmom := (integrable_abs_rpow_of_exp (PW.map U) hθ hpush p hp).comp_aemeasurable hmeas
  refine hmom.congr ?_
  filter_upwards [hnn] with ω hω
  exact congrArg (fun z : ℝ => z ^ p) (abs_of_nonneg hω)

/-- The complete power-moment clause from self-similarity and one exponential moment. -/
theorem continuumValue_power_moments {ΩW ΩB : Type*}
    [MeasurableSpace ΩW] [MeasurableSpace ΩB] (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (PW : Measure ΩW) [IsProbabilityMeasure PW] (PB : Measure ΩB)
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (ν2 : ℝ) (hν2 : 0 < ν2)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (B : Space d → ℝ≥0 → ΩB → Space d)
    (hmeas : ∀ T : ℝ, 0 < T → ∀ x : Space d,
      AEMeasurable (continuumValue d Z B PB T x) PW)
    (hnn : ∀ᵐ ω ∂PW, 0 ≤ continuumValue d Z B PB 1 0 ω)
    (hlaw : ∀ T : ℝ, 0 < T → ∀ x : Space d,
      PW.map (continuumValue d Z B PB T x) =
        PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * continuumValue d Z B PB 1 0 ω))
    (θ : ℝ) (hθ : 0 < θ)
    (hexp : Integrable (fun ω => Real.exp (θ * continuumValue d Z B PB 1 0 ω)) PW)
    (T : ℝ) (hT : 0 < T) (x : Space d) (p : ℝ) (hp : 0 < p) :
    Integrable (fun ω => continuumValue d Z B PB T x ω ^ p) PW ∧
    Integrable (fun ω => continuumValue d Z B PB 1 0 ω ^ p) PW ∧
    (∫ ω, continuumValue d Z B PB T x ω ^ p ∂PW) =
      T ^ (p * (4 - (d : ℝ)) / 4) * ∫ ω, continuumValue d Z B PB 1 0 ω ^ p ∂PW ∧
    0 < ∫ ω, continuumValue d Z B PB 1 0 ω ^ p ∂PW := by
  have hi := integrable_rpow_continuumValue_of_exp d PW PB Z B 1 0 θ hθ
    (hmeas 1 one_pos 0) hnn hexp p hp.le
  have hscaled : Integrable
      (fun ω => (T ^ ((4 - (d : ℝ)) / 4) * continuumValue d Z B PB 1 0 ω) ^ p) PW := by
    refine (hi.const_mul ((T ^ ((4 - (d : ℝ)) / 4)) ^ p)).congr ?_
    filter_upwards [hnn] with ω hω
    exact (Real.mul_rpow (Real.rpow_nonneg hT.le _) hω).symm
  have hid : IdentDistrib (continuumValue d Z B PB T x)
      (fun ω => T ^ ((4 - (d : ℝ)) / 4) * continuumValue d Z B PB 1 0 ω) PW PW :=
    ⟨hmeas T hT x, (hmeas 1 one_pos 0).const_mul _, hlaw T hT x⟩
  have hiT := (hid.comp (u := fun z : ℝ => z ^ p) (by fun_prop)).integrable_iff.mpr hscaled
  refine ⟨hiT, hi, integral_rpow_scaled_of_map_eq_base PW
    (fun S ω => continuumValue d Z B PB S x ω) (continuumValue d Z B PB 1 0)
    d hT p (hmeas T hT x) (hmeas 1 one_pos 0) (hlaw T hT x), ?_⟩
  have hnonneg : ∀ᵐ ω ∂PW, 0 ≤ continuumValue d Z B PB 1 0 ω ^ p :=
    hnn.mono fun ω hω => Real.rpow_nonneg hω p
  have hdom := ae_field_le_continuumValue PW PB W hW ν2 Z hZmod hZcont B 1 zero_le_one 0
  have hunb := field_one_zero_unbounded PW W hW hd hd3 hν2 Z hZmod 0
  by_contra hpos
  have hzero : ∫ ω, continuumValue d Z B PB 1 0 ω ^ p ∂PW = 0 :=
    le_antisymm (not_lt.mp hpos) (integral_nonneg_of_ae hnonneg)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).mp hzero
  apply hunb
  apply measure_mono_null (t := {ω | ¬ (Z 1 0 ω ≤ 0)})
  · intro ω hω
    exact not_le.mpr hω
  · apply (ae_iff).mp
    filter_upwards [hz, hdom] with ω hω hdω
    by_contra hn
    have hu : 0 < continuumValue d Z B PB 1 0 ω := lt_of_lt_of_le (not_le.mp hn) hdω
    exact (ne_of_gt (Real.rpow_pos_of_pos hu p)) hω

end Sandpile.Support
