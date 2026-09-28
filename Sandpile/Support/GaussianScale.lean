import Sandpile.Support.GaussianRotation
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Variance scaling and transport of subgaussian bounds

Variance scaling of finite Gaussian products and transport of centered
exponential bounds under measure-preserving coordinate maps. `measurePreserving_stdGaussian_ofLp`
identifies the standard Gaussian on `EuclideanSpace ℝ I` with the standard Gaussian product
law on `I → ℝ` via the coordinate map `ofLp`, and `measurePreserving_gaussian_scale` and
`measurePreserving_stdGaussian_scaled_coordinates` build on it to show that scaling every
coordinate by `√v` sends the standard Gaussian product law to `gaussianReal 0 v` in each
coordinate. `hasSubgaussianMGF_of_measurePreserving` and
`hasSubgaussianMGF_centered_of_measurePreserving` transport a subgaussian MGF bound along a
measure-preserving map `T`, the second one specialized to a function recentred at its own
mean under either measure.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section
namespace Sandpile

/-- The coordinate map `ofLp : EuclideanSpace ℝ I → (I → ℝ)` pushes the standard Gaussian on
`EuclideanSpace ℝ I` forward to the standard Gaussian product law on `I → ℝ`: this is the
content of `map_pi_eq_stdGaussian` read backwards, composed with the fact that `ofLp` and
`toLp` are mutually inverse. -/
lemma measurePreserving_stdGaussian_ofLp {I : Type*} [Fintype I] :
    MeasurePreserving (fun x : EuclideanSpace ℝ I => x.ofLp)
      (stdGaussian (EuclideanSpace ℝ I)) (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  refine ⟨(PiLp.continuous_ofLp 2 (fun _ : I => ℝ)).measurable, ?_⟩
  rw [← map_pi_eq_stdGaussian, Measure.map_map (PiLp.continuous_ofLp 2 (fun _ : I => ℝ)).measurable
    (PiLp.continuous_toLp 2 (fun _ : I => ℝ)).measurable]
  simp only [Function.comp_def, Measure.map_id']

/-- Scaling by `√v` pushes the standard Gaussian `gaussianReal 0 1` forward to `gaussianReal
0 v`, since scaling a Gaussian by a constant multiplies its variance by the constant
squared. -/
lemma measurePreserving_gaussian_scale (v : ℝ≥0) :
    MeasurePreserving (fun x : ℝ => Real.sqrt (v : ℝ) * x)
      (gaussianReal 0 1) (gaussianReal 0 v) := by
  refine ⟨by fun_prop, ?_⟩
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp only [NNReal.coe_mk, mul_one, Real.sq_sqrt v.coe_nonneg]

/-- Scaling every coordinate of `EuclideanSpace ℝ I` by `√v` pushes the standard Gaussian
forward to the product law `gaussianReal 0 v` in each coordinate: composes
`measurePreserving_stdGaussian_ofLp` with the coordinatewise scaling of
`measurePreserving_gaussian_scale`. -/
lemma measurePreserving_stdGaussian_scaled_coordinates {I : Type*} [Fintype I] (v : ℝ≥0) :
    MeasurePreserving (fun x : EuclideanSpace ℝ I => fun i => Real.sqrt (v : ℝ) * x.ofLp i)
      (stdGaussian (EuclideanSpace ℝ I)) (Measure.pi (fun _ : I => gaussianReal 0 v)) := by
  exact (measurePreserving_pi (fun _ : I => gaussianReal 0 1) (fun _ : I => gaussianReal 0 v)
    (fun _ => measurePreserving_gaussian_scale v)).comp measurePreserving_stdGaussian_ofLp

/-- A subgaussian MGF bound for `f ∘ T` on `μ` transports along a measure-preserving map `T`
to a subgaussian MGF bound for `f` on `ν = T_* μ`, since the MGF of `f` under `ν` equals the
MGF of `f ∘ T` under `μ` by the pushforward identity. -/
lemma hasSubgaussianMGF_of_measurePreserving {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {T : Ω → Ω'} (hT : MeasurePreserving T μ ν)
    {f : Ω' → ℝ} (hf : Measurable f) {c : ℝ≥0}
    (h : HasSubgaussianMGF (fun x => f (T x)) c μ) : HasSubgaussianMGF f c ν := by
  apply (HasSubgaussianMGF.id_map_iff hf.aemeasurable).mp
  rw [← hT.map_eq, Measure.map_map hf hT.measurable]
  exact (HasSubgaussianMGF.id_map_iff (hf.comp hT.measurable).aemeasurable).mpr h

/-- The centred version of `hasSubgaussianMGF_of_measurePreserving`: a subgaussian bound for
`f ∘ T` centred at its own `μ`-mean transports to a subgaussian bound for `f` centred at its
own `ν`-mean, since the two means agree by the pushforward identity for integrals. -/
lemma hasSubgaussianMGF_centered_of_measurePreserving {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    {T : Ω → Ω'} (hT : MeasurePreserving T μ ν) {f : Ω' → ℝ} (hf : Measurable f) {c : ℝ≥0}
    (h : HasSubgaussianMGF (fun x => f (T x) - ∫ y, f (T y) ∂μ) c μ) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂ν) c ν := by
  have he : (∫ y, f (T y) ∂μ) = ∫ y, f y ∂ν := by
    have hh := integral_map hT.aemeasurable hf.aestronglyMeasurable
    rw [hT.map_eq] at hh
    exact hh.symm
  apply hasSubgaussianMGF_of_measurePreserving hT (hf.sub measurable_const)
  simpa only [he, Pi.sub_apply] using h

end Sandpile
