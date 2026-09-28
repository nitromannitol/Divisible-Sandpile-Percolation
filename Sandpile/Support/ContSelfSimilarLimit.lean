import Sandpile.Support.MeanAScale
import Sandpile.Support.MeanAIndex

/-!
# The self-similarity law identity from the parabolic limit

`map_rescaledOdometer_scale` is the exact discrete identity behind `prop:continuum-value-
selfsimilar`: rescaling the centred odometer at scale `R` and time `T` has the same law as
rescaling it at scale `R * √T` and time `1`, after multiplying by `T ^ ((4 - d) / 4)` and
removing the starting site `x` by translation invariance. `selfsimilar_of_rescaled_limit` passes
this discrete identity to the limit: any pointwise parabolic limit `U` of `rescaledOdometer`
inherits the self-similarity exponent `(4 - d) / 4`, i.e. the law of `U(T,x)` equals the law of
`T ^ ((4 - d) / 4) * U(1,0)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

open Sandpile.Continuum

/-- The exact parabolic identity in law, including spatial stationarity. -/
theorem map_rescaledOdometer_scale (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 < T) (x : Space d) :
    (Sandpile.centeredMassLaw d ν).map (rescaledOdometer d R T x) =
      (Sandpile.centeredMassLaw d ν).map
        (fun σ => T ^ ((4 - (d : ℝ)) / 4) *
          rescaledOdometer d (R * Real.sqrt T) 1 0 σ) := by
  let a := T ^ ((4 - (d : ℝ)) / 4) * (R * Real.sqrt T) ^ (-(2 - (d : ℝ) / 2))
  have hsite := congrArg (fun μ : Measure ℝ => μ.map (fun z => a * z))
    (map_odometer_centered_eq d ν ⌊(R * Real.sqrt T) ^ 2 * 1⌋₊
      (fun i => ⌊R * x i⌋))
  rw [Measure.map_map (by fun_prop) (Sandpile.measurable_odometer _ _),
    Measure.map_map (by fun_prop) (Sandpile.measurable_odometer _ _)] at hsite
  calc
    _ = (Sandpile.centeredMassLaw d ν).map
        (fun σ => a * Sandpile.odometer σ ⌊(R * Real.sqrt T) ^ 2 * 1⌋₊
          (fun i => ⌊R * x i⌋)) := by
      congr 1
      funext σ
      rw [rescaledOdometer_eq_scale d R T hR hT x σ]
      exact (mul_assoc _ _ _).symm
    _ = (Sandpile.centeredMassLaw d ν).map
        (fun σ => a * Sandpile.odometer σ ⌊(R * Real.sqrt T) ^ 2 * 1⌋₊ 0) := hsite
    _ = _ := by
      congr 1
      funext σ
      rw [rescaledOdometer_one_zero]
      simp only [mul_one]
      exact mul_assoc _ _ _

/-- Any pointwise parabolic limit has the self-similarity exponent `(4-d)/4`.
The convergence assumption includes almost-everywhere measurability of the limit. -/
theorem selfsimilar_of_rescaled_limit {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : ℝ → Space d → Ω → ℝ)
    (hlimit : ∀ T : ℝ, 0 < T → ∀ x : Space d,
      TendstoInDistribution (fun R : ℝ => rescaledOdometer d R T x)
        atTop (U T x) (fun _ => Sandpile.centeredMassLaw d ν) P)
    (T : ℝ) (hT : 0 < T) (x : Space d) :
    P.map (U T x) = P.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 0 ω) := by
  have hscale := tendstoInDistribution_comp (fun R : ℝ => R * Real.sqrt T)
    (tendsto_id.atTop_mul_const (Real.sqrt_pos.mpr hT)) (hlimit 1 one_pos 0)
  have hscaled := hscale.continuous_comp
    (g := fun z : ℝ => T ^ ((4 - (d : ℝ)) / 4) * z) (by fun_prop)
  have hother : TendstoInDistribution (fun R : ℝ => rescaledOdometer d R T x)
      atTop (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 0 ω)
      (fun _ => Sandpile.centeredMassLaw d ν) P := by
    refine ⟨(hlimit T hT x).forall_aemeasurable, hscaled.aemeasurable_limit, ?_⟩
    refine hscaled.tendsto.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    apply Subtype.ext
    exact (map_rescaledOdometer_scale d ν R T hR hT x).symm
  exact tendstoInDistribution_unique _ (hlimit T hT x) hother

end Sandpile.Support
