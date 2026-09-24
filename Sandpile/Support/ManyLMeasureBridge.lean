/-
The measure-theoretic bridge used by the Step-3 derivation of
`thm:dgt4-many-limits` (`sandpile.tex:5900-5928`): an `L²` bound on the
difference of two families gives convergence in measure of the difference, and a
family differing from a family converging in distribution to a centred Gaussian
by a term converging in measure to zero converges to the same Gaussian.
-/
import Sandpile.Support.ContDGT4Membrane

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- An `L²` bound on the difference of two families gives convergence in measure
of the difference. -/
theorem tendstoInMeasure_sub_of_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (O W : ℝ → Ω → ℝ)
    (hmem : ∀ R : ℝ, MemLp (fun ω => O R ω - W R ω) 2 P)
    (hint : ∀ R : ℝ, Integrable (fun ω => (O R ω - W R ω) ^ 2) P)
    (hlim : Tendsto (fun R : ℝ => ∫ ω, (O R ω - W R ω) ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P (fun R : ℝ => O R - W R) atTop 0 := by
  have heL : Tendsto (fun R : ℝ => eLpNorm (fun ω => O R ω - W R ω) 2 P) atTop (𝓝 0) :=
    tendsto_eLpNorm_of_tendsto_integral_sq P (fun R ω => O R ω - W R ω)
      (fun R => (hmem R).aestronglyMeasurable) hint hlim
  refine MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    (fun R => (hmem R).aestronglyMeasurable) aestronglyMeasurable_zero ?_
  simp only [sub_zero]
  exact heL

/-- A family whose difference from a family converging in distribution to a
centred Gaussian converges in measure to zero converges to the same Gaussian. -/
theorem tendstoInDistribution_of_sub_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (O W : ℝ → Ω → ℝ) (K : ℝ≥0)
    (hW : TendstoInDistribution W atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 K))
    (hsub : TendstoInMeasure P (fun R : ℝ => O R - W R) atTop 0)
    (hO : ∀ R : ℝ, AEMeasurable (O R) P) :
    TendstoInDistribution O atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 K) :=
  MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub O (id : ℝ → ℝ) hW hsub hO

end Sandpile.Support
