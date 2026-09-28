import Sandpile.Continuum.WhiteNoise

/-!
# The law of the white noise at square-integrable indices

`Sandpile.Continuum.IsWhiteNoise` asks that the finite-dimensional laws of `W` be Gaussian,
that each `W f` be centred with `∫ (W f) (W g) = ∫ f g`, and that `W` be linear in its index
almost surely. These clauses determine the law of `W` at a single square-integrable index
`f` to be the centred Gaussian of variance `∫ f * f` (`map_whiteNoise_eq_gaussianReal`), and
the law of any finite linear combination `∑ i, c i * W (f i)` to be the centred Gaussian whose
variance is the squared `L²` norm of the combination `∑ i, c i • f i` of the indices
(`map_whiteNoise_combination`), after identifying that combination with the almost-sure linear
combination of the values of `W` (`whiteNoise_finsetSum_ae`). This identifies the limiting field
in the finite-dimensional convergence of the heat-potential invariance principle.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The law of the white noise at a square-integrable index is the centred
Gaussian whose variance is the square of its `L²` norm. -/
theorem map_whiteNoise_eq_gaussianReal {Ω : Type*} [MeasurableSpace Ω]
    (W : (Space d → ℝ) → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (f : Space d → ℝ)
    (hf : MemLp f 2 (volume : Measure (Space d))) :
    P.map (W f) = gaussianReal 0 (Real.toNNReal (∫ y : Space d, f y * f y)) := by
  have hgl : ProbabilityTheory.HasGaussianLaw (W f) P :=
    hW.gaussian.hasGaussianLaw_eval f
  rw [hgl.map_eq_gaussianReal]
  have hmean : ∫ ω, W f ω ∂P = 0 := hW.mean f hf
  have hvar : variance (W f) P = ∫ y : Space d, f y * f y := by
    rw [ProbabilityTheory.variance_eq_integral (hW.meas f hf).aemeasurable, hmean]
    simp only [sub_zero]
    rw [← hW.cov f f hf hf]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => sq (W f ω))
  rw [hmean, hvar]

/-- The white noise of a finite linear combination of square-integrable indices is
almost surely the same linear combination of its values. -/
theorem whiteNoise_finsetSum_ae {Ω ι : Type*} [MeasurableSpace Ω]
    (W : (Space d → ℝ) → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (c : ι → ℝ) (f : ι → Space d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (volume : Measure (Space d))) (s : Finset ι) :
    W (∑ i ∈ s, c i • f i) =ᵐ[P] fun ω => ∑ i ∈ s, c i * W (f i) ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 := hW.smul 0 (0 : Space d → ℝ) (MeasureTheory.MemLp.zero)
      simpa using h0
  | insert a s ha ih =>
      have hmem1 : MemLp (c a • f a) 2 (volume : Measure (Space d)) := (hf a).const_smul (c a)
      have hmem2 : MemLp (∑ i ∈ s, c i • f i) 2 (volume : Measure (Space d)) :=
        MeasureTheory.memLp_finsetSum' s fun i _ => (hf i).const_smul (c i)
      have hadd := hW.add (c a • f a) (∑ i ∈ s, c i • f i) hmem1 hmem2
      have hsmul := hW.smul (c a) (f a) (hf a)
      simp only [Finset.sum_insert ha]
      filter_upwards [hadd, hsmul, ih] with ω h1 h2 h3
      rw [h1, h2, h3]

/-- **The law of a finite linear combination of the values of the white noise**:
the centred Gaussian whose variance is the square of the `L²` norm of the
combination of the indices. -/
theorem map_whiteNoise_combination {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (W : (Space d → ℝ) → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (c : ι → ℝ) (f : ι → Space d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (volume : Measure (Space d))) :
    P.map (fun ω => ∑ i, c i * W (f i) ω)
      = gaussianReal 0 (Real.toNNReal
          (∫ y : Space d, (∑ i, c i * f i y) * ∑ i, c i * f i y)) := by
  classical
  have hfun : (∑ i, c i • f i) = fun y : Space d => ∑ i, c i * f i y := by
    funext y
    simp [Finset.sum_apply]
  have hmem : MemLp (∑ i, c i • f i) 2 (volume : Measure (Space d)) :=
    MeasureTheory.memLp_finsetSum' _ fun i _ => (hf i).const_smul (c i)
  have hae := whiteNoise_finsetSum_ae W P hW c f hf Finset.univ
  have h1 : P.map (fun ω => ∑ i, c i * W (f i) ω) = P.map (W (∑ i, c i • f i)) :=
    (MeasureTheory.Measure.map_congr hae).symm
  rw [h1, map_whiteNoise_eq_gaussianReal W P hW _ hmem, hfun]

end Sandpile.Support
