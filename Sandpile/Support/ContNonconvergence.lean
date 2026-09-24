/-
The last clause of Theorem 1.3(iii)(d) (`sandpile.tex`, `thm:main-explosion`,
part (iii)(d)): the rescaled fluctuation field of the odometer does NOT converge
in `H^{-s}_loc(ℝ^d)`, because two subsequences of it converge to centred Gaussian
random distributions with different variances.

The argument is the standard one and is recorded here in the vocabulary of
`Sandpile.Continuum.TendstoInNegSobolev`: convergence of the whole family forces
every subsequence to converge to the same law, two Gaussian laws with the same
mean and different variances are different, and a family of covariances that are
already distinct on the diagonal is injective in its index.  Nothing about the
sandpile enters; the input is the two subsequential limits produced by
`thm:dgt4-many-limits` (`sandpile.tex:5900-5928`).
-/
import Sandpile.Continuum.Membrane

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.Support

open Sandpile.Continuum

/-- Two centred Gaussian limits of the same family have the same variance. -/
theorem nnreal_eq_of_two_gaussian_limits {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a b : ℝ≥0)
    (h1 : TendstoInDistribution X atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 a))
    (h2 : TendstoInDistribution X atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 b)) :
    a = b := by
  have h := MeasureTheory.tendstoInDistribution_unique X h1 h2
  rw [MeasureTheory.Measure.map_id, MeasureTheory.Measure.map_id] at h
  exact (ProbabilityTheory.gaussianReal_ext_iff.mp h).2

/-- A subsequence of a family converging in distribution converges to the same law. -/
theorem tendstoInDistribution_comp_atTop {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ → Ω → ℝ)
    (μ' : Measure ℝ) [IsProbabilityMeasure μ']
    (Rs : ℕ → ℝ) (hRs : Tendsto Rs atTop atTop)
    (h : TendstoInDistribution F atTop (id : ℝ → ℝ) (fun _ => P) μ') :
    TendstoInDistribution (fun k : ℕ => F (Rs k)) atTop (id : ℝ → ℝ) (fun _ => P) μ' :=
  ⟨fun k => h.forall_aemeasurable (Rs k), h.aemeasurable_limit, h.tendsto.comp hRs⟩

/-- **Two subsequential Gaussian limits with different variances rule out
convergence in `H^{-s}_loc`.**  This is the last clause of Theorem 1.3(iii)(d). -/
theorem not_exists_tendstoInNegSobolev_of_two_limits {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (s : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ → Ω → (Space d → ℝ) → ℝ)
    (φ : Space d → ℝ) (hφ : IsTestFn Set.univ φ)
    (a b : ℝ≥0) (hab : a ≠ b)
    (Rs Rs' : ℕ → ℝ) (hRs : Tendsto Rs atTop atTop) (hRs' : Tendsto Rs' atTop atTop)
    (h1 : TendstoInDistribution (fun (k : ℕ) (ω : Ω) => F (Rs k) ω φ) atTop (id : ℝ → ℝ)
            (fun _ => P) (gaussianReal 0 a))
    (h2 : TendstoInDistribution (fun (k : ℕ) (ω : Ω) => F (Rs' k) ω φ) atTop (id : ℝ → ℝ)
            (fun _ => P) (gaussianReal 0 b)) :
    ¬ ∃ K, TendstoInNegSobolev d s P F K := by
  rintro ⟨K, hK, -⟩
  have hfull := hK φ hφ
  have e1 : Real.toNNReal (K φ φ) = a :=
    nnreal_eq_of_two_gaussian_limits P _ _ _
      (tendstoInDistribution_comp_atTop P (fun R ω => F R ω φ) _ Rs hRs hfull) h1
  have e2 : Real.toNNReal (K φ φ) = b :=
    nnreal_eq_of_two_gaussian_limits P _ _ _
      (tendstoInDistribution_comp_atTop P (fun R ω => F R ω φ) _ Rs' hRs' hfull) h2
  exact hab (e1.symm.trans e2)

/-- The index set `[3/2, 2]` of `thm:dgt4-many-limits` is uncountable. -/
theorem not_countable_Icc_three_halves_two :
    ¬ (Set.Icc ((3 : ℝ) / 2) 2).Countable := by
  simp only [Cardinal.Real.Icc_countable_iff, not_le]
  norm_num

end Sandpile.Support
