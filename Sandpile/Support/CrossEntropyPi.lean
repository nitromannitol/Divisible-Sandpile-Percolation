import Sandpile.Support.CrossEntropy

/-!
# The finite-dimensional Cameron-Martin entropy bound

Step 3 of `prop:fixed-scale-crossings` (`sandpile.tex:2300-2400`), the finite-dimensional part
of the Cameron-Martin entropy bound: for Gaussian white noise, the relative entropy between
the unshifted law on one revealed unit cube and the law shifted by `(L/(𝔪R))dz` is
`L²/(2𝔪²R²)`. The exploration reveals `𝒩` unit cubes, and the shift is the same on each of
them, so the relative entropy of the shifted law of the revealed noise is `𝒩` times the
one-dimensional value. `Sandpile/Support/CrossEntropy.lean` has the one-dimensional value
`klDiv_gaussianReal_shift`; this module multiplies it over the finitely many coordinates the
exploration reads. The product of `n` copies of a Gaussian is carried to the product of the
first coordinate with the product of the rest by `piFinSuccAbove`, a measurable equivalence,
and the relative entropy is invariant under one (`klDiv_map_measurableEquiv`); the chain rule
`klDiv_compProd_eq_add` then splits off the first coordinate, whose relative entropy is the
one-dimensional value, and the remaining factor is the same product with one fewer coordinate.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Support

/-- The relative entropy is invariant under a measurable equivalence: the
Radon--Nikodym derivative is carried along, and the integral is the same. -/
theorem klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv (μ.map e) (ν.map e) = InformationTheory.klDiv μ ν := by
  have hiff : μ.map e ≪ ν.map e ↔ μ ≪ ν := by
    constructor
    · intro h
      have h2 : (μ.map e).map e.symm ≪ (ν.map e).map e.symm :=
        e.symm.measurableEmbedding.absolutelyContinuous_map h
      have h3 : (μ.map e).map e.symm = μ := by
        rw [Measure.map_map e.symm.measurable e.measurable, e.symm_comp_self, Measure.map_id]
      have h4 : (ν.map e).map e.symm = ν := by
        rw [Measure.map_map e.symm.measurable e.measurable, e.symm_comp_self, Measure.map_id]
      rwa [h3, h4] at h2
    · intro h
      exact e.measurableEmbedding.absolutelyContinuous_map h
  by_cases h : μ ≪ ν
  · rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (hiff.mpr h),
      InformationTheory.klDiv_eq_lintegral_klFun_of_ac h]
    rw [e.measurableEmbedding.lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
    rw [hx]
  · rw [InformationTheory.klDiv_of_not_ac h, InformationTheory.klDiv_of_not_ac]
    exact fun hc => h (hiff.mp hc)

/-- The relative entropy of a product with a common first factor is the relative
entropy of the second factors: the first factor cancels in the Radon--Nikodym
derivative. -/
theorem klDiv_prod_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν η : Measure β) [IsFiniteMeasure ν]
    [IsFiniteMeasure η] :
    InformationTheory.klDiv (μ.prod ν) (μ.prod η) = InformationTheory.klDiv ν η := by
  rw [← klDiv_map_measurableEquiv (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α)
    (μ.prod ν) (μ.prod η)]
  rw [show (⇑(MeasurableEquiv.prodComm : α × β ≃ᵐ β × α)) = Prod.swap from rfl,
    Measure.prod_swap, Measure.prod_swap]
  rw [← Measure.compProd_const (μ := ν) (ν := μ), ← Measure.compProd_const (μ := η) (ν := μ)]
  exact InformationTheory.klDiv_compProd_left ν η (Kernel.const β μ)

/-- The Cameron--Martin entropy of the shift on `n` revealed unit cubes: the
relative entropy of `n` independent one-dimensional Gaussian shifts of a common
variance is `n` times the one-dimensional value `m²/(2v)`.  This is the
`(L²/(2𝔪²R²))𝒩` of `sandpile.tex:2378-2382` with `m = L/(𝔪R)`. -/
theorem klDiv_pi_gaussianReal (n : ℕ) (v : ℝ≥0) (hv : v ≠ 0) (m : ℝ) :
    InformationTheory.klDiv (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 v)
        (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal m v)
      = ENNReal.ofReal ((n : ℝ) * (m ^ 2 / (2 * v))) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty (fun _ : Fin 0 => ProbabilityTheory.gaussianReal 0 v),
      Measure.pi_of_empty (fun _ : Fin 0 => ProbabilityTheory.gaussianReal m v)]
    rw [InformationTheory.klDiv_self]
    simp
  | succ n ih =>
    have h0 : Measure.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
        (Measure.pi fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal 0 v)
        = (ProbabilityTheory.gaussianReal 0 v).prod
          (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 v) :=
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal 0 v) 0).map_eq
    have h1 : Measure.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
        (Measure.pi fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal m v)
        = (ProbabilityTheory.gaussianReal m v).prod
          (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal m v) :=
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal m v) 0).map_eq
    rw [← klDiv_map_measurableEquiv
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      (Measure.pi fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal 0 v)
      (Measure.pi fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal m v), h0, h1]
    rw [← Measure.compProd_const (μ := ProbabilityTheory.gaussianReal 0 v)
        (ν := Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 v),
      ← Measure.compProd_const (μ := ProbabilityTheory.gaussianReal m v)
        (ν := Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal m v)]
    rw [InformationTheory.klDiv_compProd_eq_add,
      Sandpile.Support.klDiv_gaussianReal_shift hv m]
    rw [show (ProbabilityTheory.gaussianReal 0 v ⊗ₘ
          Kernel.const ℝ (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 v))
        = (ProbabilityTheory.gaussianReal 0 v).prod
          (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 v) from
      Measure.compProd_const,
      show (ProbabilityTheory.gaussianReal 0 v ⊗ₘ
          Kernel.const ℝ (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal m v))
        = (ProbabilityTheory.gaussianReal 0 v).prod
          (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal m v) from
      Measure.compProd_const]
    rw [klDiv_prod_right (ProbabilityTheory.gaussianReal 0 v)
        (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 v)
        (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal m v), ih]
    rw [Nat.cast_succ, add_mul, one_mul]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring

/-- The relative entropy of the Cameron--Martin shift on one revealed unit cube:
the unshifted law is the standard Gaussian, the shifted law has mean `L/(𝔪R)`,
and the relative entropy is `L²/(2𝔪²R²)`, which is `sandpile.tex:2376-2378`. -/
theorem klDiv_shift_unit {m L R : ℝ} (hm : 0 < m) (hR : 0 < R) :
    InformationTheory.klDiv (ProbabilityTheory.gaussianReal 0 1)
        (ProbabilityTheory.gaussianReal (L / (m * R)) 1)
      = ENNReal.ofReal (L ^ 2 / (2 * m ^ 2 * R ^ 2)) := by
  rw [Sandpile.Support.klDiv_gaussianReal_shift (v := 1) (by norm_num) (L / (m * R))]
  congr 1
  field_simp
  norm_num

/-- The chain-rule bound of Step 3 (`sandpile.tex:2378-2382`): the relative
entropy of the shifted law of the revealed noise is `𝒩` times the
one-dimensional value, where `𝒩` is the number of revealed unit cubes.  This is
the display `D(P₀^tr‖P_{L/R}^tr) ≤ (L²/(2𝔪²R²)) 𝔼₀𝒩`. -/
theorem klDiv_trace_le {n : ℕ} {m L R : ℝ} (hm : 0 < m) (hR : 0 < R) :
    InformationTheory.klDiv (Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
        (Measure.pi fun _ : Fin n =>
          ProbabilityTheory.gaussianReal (L / (m * R)) 1)
      = ENNReal.ofReal ((n : ℝ) * (L ^ 2 / (2 * m ^ 2 * R ^ 2))) := by
  rw [Sandpile.Support.klDiv_pi_gaussianReal n 1 (by norm_num) (L / (m * R))]
  congr 1
  field_simp
  norm_num

/-- The relative entropy of the trace laws of the exploration, from the two
product laws: if the unshifted trace law is the standard Gaussian product on the
`n` revealed coordinates and the shifted one is the product of Gaussians of mean
`L/(𝔪R)`, then the relative entropy is `n L²/(2𝔪²R²)`, which is the display
`sandpile.tex:2378-2382`. -/
theorem klDiv_trace_laws {n : ℕ} {m L R : ℝ}
    (hm : 0 < m) (hR : 0 < R) (μ₀ μ₁ : Measure (Fin n → ℝ))
    (h₀ : μ₀ = Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
    (h₁ : μ₁ = Measure.pi fun _ : Fin n =>
      ProbabilityTheory.gaussianReal (L / (m * R)) 1) :
    InformationTheory.klDiv μ₀ μ₁
      = ENNReal.ofReal ((n : ℝ) * (L ^ 2 / (2 * m ^ 2 * R ^ 2))) := by
  subst h₀
  subst h₁
  exact Sandpile.Support.klDiv_trace_le (n := n) (m := m) (L := L) (R := R) hm hR

end Sandpile.Support
