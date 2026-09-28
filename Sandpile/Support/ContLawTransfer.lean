import Sandpile.Support.MeanAValue
import Mathlib

/-!
# Moment and variance identities transferred along an identity of laws

The scaling argument of `prop:continuum-value-selfsimilar` (`sandpile.tex:1985-1993`) transfers
the law of the stopping value along the scaling of the field, and then needs the power moments
and the variance to agree once the two laws are known to be equal. `integral_rpow_of_map_eq` and
`variance_of_map_eq` give these two elementary consequences for any pair of real random variables
sharing a law, each a single rewrite with `MeasureTheory.integral_map` or
`ProbabilityTheory.variance_map`. `integral_continuumValue_of_map_eq` and
`variance_continuumValue_of_map_eq` specialize them to the continuum value `𝒰(T,x)`: when its law
equals the law of `T ^ β * 𝒰(1,0)`, its mean and variance are related to those of `𝒰(1,0)` by the
factors `T ^ β` and `(T ^ β) ^ 2`, which are the sixth and eighth clauses of
`cor:dlt4-mean-asymptotic`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

/-- **The power-moment identity from the law identity.**  If two real random
variables on the same probability space have the same law, then every power
moment agrees. -/
theorem integral_rpow_of_map_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : Ω → ℝ) (hf : AEMeasurable f P) (hg : AEMeasurable g P) (p : ℝ)
    (h : P.map f = P.map g) :
    ∫ ω, f ω ^ p ∂P = ∫ ω, g ω ^ p ∂P := by
  have hm : Measurable (fun y : ℝ => y ^ p) := by fun_prop
  rw [← integral_map hf hm.aestronglyMeasurable,
    ← integral_map hg hm.aestronglyMeasurable, h]

/-- **The variance identity from the law identity.**  If two real random
variables on the same probability space have the same law, then their variances
agree. -/
theorem variance_of_map_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : Ω → ℝ) (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (h : P.map f = P.map g) :
    variance f P = variance g P := by
  have h1 : variance f P = variance id (P.map f) := by
    simpa only [Function.comp_def, id_eq] using
      (variance_map (X := id) (μ := P) (Y := f) aemeasurable_id hf).symm
  have h2 : variance g P = variance id (P.map g) := by
    simpa only [Function.comp_def, id_eq] using
      (variance_map (X := id) (μ := P) (Y := g) aemeasurable_id hg).symm
  rw [h1, h2, h]

/-- **The mean identity from the law identity of the continuum value.**  If the law
of `𝒰(T,x)` is the law of `T^β 𝒰(1,0)`, then the means are related by the same
factor.  This is the sixth clause of `cor:dlt4-mean-asymptotic`. -/
theorem integral_continuumValue_of_map_eq {ΩW ΩB : Type*} [MeasurableSpace ΩW]
    [MeasurableSpace ΩB] (d : ℕ) (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (PB : Measure ΩB) (PW : Measure ΩW)
    (T : ℝ) (x : Sandpile.Continuum.Space d) (β : ℝ)
    (hf : AEMeasurable (fun ω =>
      Sandpile.Continuum.continuumValue d Z B PB T x ω) PW)
    (hg : AEMeasurable (fun ω =>
      Sandpile.Continuum.continuumValue d Z B PB 1 0 ω) PW)
    (hmap : PW.map (fun ω =>
        Sandpile.Continuum.continuumValue d Z B PB T x ω)
      = PW.map (fun ω => T ^ β *
        Sandpile.Continuum.continuumValue d Z B PB 1 0 ω)) :
    ∫ ω, Sandpile.Continuum.continuumValue d Z B PB T x ω ∂PW
      = T ^ β * ∫ ω,
        Sandpile.Continuum.continuumValue d Z B PB 1 0 ω ∂PW := by
  have h1 : ∫ ω, Sandpile.Continuum.continuumValue d Z B PB T x ω ∂PW
      = ∫ y, y ∂(PW.map (fun ω =>
        Sandpile.Continuum.continuumValue d Z B PB T x ω)) := by
    rw [integral_map hf measurable_id'.aestronglyMeasurable]
  have h2 : ∫ ω, T ^ β *
        Sandpile.Continuum.continuumValue d Z B PB 1 0 ω ∂PW
      = T ^ β * ∫ ω,
        Sandpile.Continuum.continuumValue d Z B PB 1 0 ω ∂PW :=
    integral_const_mul (T ^ β) _
  have h3 : ∫ ω, T ^ β *
        Sandpile.Continuum.continuumValue d Z B PB 1 0 ω ∂PW
      = ∫ y, y ∂(PW.map (fun ω => T ^ β *
        Sandpile.Continuum.continuumValue d Z B PB 1 0 ω)) := by
    rw [integral_map (hg.const_mul (T ^ β)) measurable_id'.aestronglyMeasurable]
  rw [h1, hmap, ← h3, h2]

/-- **The variance identity from the law identity of the continuum value.**  If the
law of `𝒰(T,x)` is the law of `T^β 𝒰(1,0)`, then the variances are related by the
square of the factor.  This is the eighth clause of `cor:dlt4-mean-asymptotic`. -/
theorem variance_continuumValue_of_map_eq {ΩW ΩB : Type*} [MeasurableSpace ΩW]
    [MeasurableSpace ΩB] (d : ℕ) (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (PB : Measure ΩB) (PW : Measure ΩW)
    (T : ℝ) (x : Sandpile.Continuum.Space d) (β : ℝ)
    (hf : AEMeasurable (fun ω =>
      Sandpile.Continuum.continuumValue d Z B PB T x ω) PW)
    (hg : AEMeasurable (fun ω =>
      Sandpile.Continuum.continuumValue d Z B PB 1 0 ω) PW)
    (hmap : PW.map (fun ω =>
        Sandpile.Continuum.continuumValue d Z B PB T x ω)
      = PW.map (fun ω => T ^ β *
        Sandpile.Continuum.continuumValue d Z B PB 1 0 ω)) :
    variance (fun ω =>
        Sandpile.Continuum.continuumValue d Z B PB T x ω) PW
      = (T ^ β) ^ 2 * variance (fun ω =>
        Sandpile.Continuum.continuumValue d Z B PB 1 0 ω) PW := by
  rw [variance_of_map_eq PW _ _ hf (hg.const_mul (T ^ β)) hmap]
  exact variance_const_mul (T ^ β) _ PW

end Sandpile.Support
