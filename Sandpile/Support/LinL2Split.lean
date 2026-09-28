import Mathlib

/-!
# The `L²` split into a remainder and a coefficient-replacement term

The squared difference `(A - B - C) ^ 2` between the centred tested field `A`, the weighted
linear field `B`, and a further correction `C` is bounded by `2 (A - B) ^ 2 + 2 C ^ 2`, so a
vanishing `L²` norm of `A - B` together with a vanishing `L²` norm of `C` forces a vanishing `L²`
norm of `A - B - C`. This file proves that split and its integrated consequence, together with the
second-moment bound `∫ (∑ i, d i * ζ i) ^ 2 ≤ Var (∑ i, |d i|) ^ 2` for a linear functional of an
i.i.d. centred scenery of finitely many coordinates, used for the coefficient-replacement term.
-/

open Filter Topology

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `(A - B - C)² ≤ 2 (A - B)² + 2 C²` under the integral. -/
theorem integral_sq_sub_sub_le (P : Measure Ω) (A B C : Ω → ℝ)
    (h1 : Integrable (fun ω => (A ω - B ω) ^ 2) P)
    (h2 : Integrable (fun ω => (C ω) ^ 2) P)
    (h3 : Integrable (fun ω => (A ω - B ω - C ω) ^ 2) P) :
    ∫ ω, (A ω - B ω - C ω) ^ 2 ∂P
      ≤ 2 * (∫ ω, (A ω - B ω) ^ 2 ∂P) + 2 * (∫ ω, (C ω) ^ 2 ∂P) := by
  have hpt : ∀ ω, (A ω - B ω - C ω) ^ 2 ≤ 2 * (A ω - B ω) ^ 2 + 2 * (C ω) ^ 2 := by
    intro ω
    have h : (A ω - B ω - C ω) ^ 2 = ((A ω - B ω) - C ω) ^ 2 := by ring
    rw [h]
    nlinarith [sq_nonneg ((A ω - B ω) + C ω)]
  have h2i : Integrable (fun ω => 2 * (A ω - B ω) ^ 2 + 2 * (C ω) ^ 2) P :=
    (h1.const_mul 2).add (h2.const_mul 2)
  calc ∫ ω, (A ω - B ω - C ω) ^ 2 ∂P
      ≤ ∫ ω, (2 * (A ω - B ω) ^ 2 + 2 * (C ω) ^ 2) ∂P :=
        integral_mono h3 h2i hpt
    _ = 2 * (∫ ω, (A ω - B ω) ^ 2 ∂P) + 2 * (∫ ω, (C ω) ^ 2 ∂P) := by
        rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul,
          integral_const_mul]

/-- The `L²` assembly of Step 2: two vanishing `L²` norms give a third. -/
theorem tendsto_l2_of_remainder_and_replacement (P : Measure Ω) (A B C : ℝ → Ω → ℝ)
    (hA : ∀ R, Integrable (fun ω => (A R ω - B R ω) ^ 2) P)
    (hC : ∀ R, Integrable (fun ω => (C R ω) ^ 2) P)
    (hAC : ∀ R, Integrable (fun ω => (A R ω - B R ω - C R ω) ^ 2) P)
    (h1 : Tendsto (fun R => ∫ ω, (A R ω - B R ω) ^ 2 ∂P) atTop (𝓝 0))
    (h2 : Tendsto (fun R => ∫ ω, (C R ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun R => ∫ ω, (A R ω - B R ω - C R ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hb : ∀ R, ∫ ω, (A R ω - B R ω - C R ω) ^ 2 ∂P
      ≤ 2 * (∫ ω, (A R ω - B R ω) ^ 2 ∂P) + 2 * (∫ ω, (C R ω) ^ 2 ∂P) :=
    fun R => integral_sq_sub_sub_le P (A R) (B R) (C R) (hA R) (hC R) (hAC R)
  have htop : Tendsto (fun R => 2 * (∫ ω, (A R ω - B R ω) ^ 2 ∂P)
      + 2 * (∫ ω, (C R ω) ^ 2 ∂P)) atTop (𝓝 (2 * 0 + 2 * 0)) :=
    (h1.const_mul 2).add (h2.const_mul 2)
  refine squeeze_zero (fun R => integral_nonneg fun ω => sq_nonneg _) hb ?_
  simpa using htop

/-- The sum of the squares of the coefficients is at most the square of the sum
of their absolute values. -/
theorem sum_sq_le_sq_sum_abs {N : ℕ} (d : Fin N → ℝ) :
    ∑ i, d i ^ 2 ≤ (∑ i, |d i|) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  rw [show ∑ i, d i ^ 2 = ∑ i, |d i| ^ 2 by simp [sq_abs]]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun j => |d i| * |d j|)
    (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
  simpa [sq, sq_abs] using h

/-- `eq:dgt4-linear-coefficient-replacement` (`sandpile.tex:5826-5836`): for an
i.i.d. centred scenery of finite variance, the second moment of a linear
functional of finitely many sites is at most the variance of the scenery times
the square of the sum of the absolute values of the coefficients. -/
theorem integral_sq_linear_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    {N : ℕ} (d : Fin N → ℝ) :
    ∫ ζ, (∑ i, d i * ζ i) ^ 2 ∂(Measure.pi fun _ : Fin N => ν)
      ≤ (∫ z, z ^ 2 ∂ν) * (∑ i, |d i|) ^ 2 := by
  have hmem : ∀ i : Fin N, MemLp (fun z : ℝ => d i * z) 2 ν := fun i => hsq.const_mul (d i)
  have hvar : variance (fun ξ : Fin N → ℝ => ∑ i, d i * ξ i) (Measure.pi fun _ : Fin N => ν)
      = ∑ i, variance (fun z : ℝ => d i * z) ν := by
    have h := variance_sum_pi (μ := fun _ : Fin N => ν) (X := fun i => fun z : ℝ => d i * z) hmem
    have hfun : (∑ i, fun ω : Fin N → ℝ => d i * ω i)
        = fun ξ : Fin N → ℝ => ∑ i, d i * ξ i := by
      funext ξ; simp [Finset.sum_apply]
    rw [hfun] at h
    exact h
  have hvi : variance (fun z : ℝ => z) ν = ∫ z, z ^ 2 ∂ν := by
    show variance (id : ℝ → ℝ) ν = ∫ z, z ^ 2 ∂ν
    rw [variance_eq_integral measurable_id.aemeasurable]
    simp only [id_eq]
    rw [hmean]
    simp
  have hsum : ∑ i, variance (fun z : ℝ => d i * z) ν = (∑ i, d i ^ 2) * ∫ z, z ^ 2 ∂ν := by
    rw [Finset.sum_congr rfl fun i _ => by rw [variance_const_mul, hvi], Finset.sum_mul]
  have heval : ∀ i : Fin N, ∫ ξ : Fin N → ℝ, ξ i ∂(Measure.pi fun _ : Fin N => ν) = ∫ z, z ∂ν :=
    fun i => integral_comp_eval (μ := fun _ : Fin N => ν) (i := i) (f := id)
      measurable_id.aestronglyMeasurable
  have hint : ∀ i : Fin N, Integrable (fun ξ : Fin N → ℝ => d i * ξ i)
      (Measure.pi fun _ : Fin N => ν) := by
    intro i
    have h1 : Integrable (fun ξ : Fin N → ℝ => (fun z : ℝ => d i * z) (ξ i))
        (Measure.pi fun _ : Fin N => ν) :=
      ((measurePreserving_eval (fun _ : Fin N => ν) i).integrable_comp
        (hmem i).aestronglyMeasurable).mpr ((hmem i).integrable (by norm_num))
    simpa using h1
  have hmean0 : ∫ ξ, (∑ i, d i * ξ i) ∂(Measure.pi fun _ : Fin N => ν) = 0 := by
    rw [integral_finsetSum Finset.univ (f := fun i (ξ : Fin N → ℝ) => d i * ξ i)
      (fun i _ => hint i)]
    simp only [integral_const_mul, heval, hmean, mul_zero, Finset.sum_const_zero]
  have hsqsum : ∑ i, d i ^ 2 ≤ (∑ i, |d i|) ^ 2 := sum_sq_le_sq_sum_abs d
  have hmeas : AEMeasurable (fun ξ : Fin N → ℝ => ∑ i, d i * ξ i)
      (Measure.pi fun _ : Fin N => ν) :=
    (Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)).aemeasurable
  have hsq_eq : ∫ ξ, (∑ i, d i * ξ i) ^ 2 ∂(Measure.pi fun _ : Fin N => ν)
      = variance (fun ξ : Fin N → ℝ => ∑ i, d i * ξ i) (Measure.pi fun _ : Fin N => ν) := by
    rw [variance_eq_integral hmeas, hmean0]
    simp
  rw [hsq_eq, hvar, hsum]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_right hsqsum (integral_nonneg fun z => sq_nonneg z)

end Sandpile
