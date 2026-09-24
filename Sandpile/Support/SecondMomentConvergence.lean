/-
Convergence in measure from vanishing second moments, and preservation of second
moment limits under an error tending to zero in the second moment.
-/
import LatticeProb.Prob.EfronSteinCov
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

theorem tendstoInMeasure_zero_of_second_moment {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {l : Filter ι} {F : ι → Ω → ℝ}
    (hi : ∀ᶠ n in l, Integrable (fun ω => F n ω ^ 2) μ)
    (hlim : Tendsto (fun n => ∫ ω, F n ω ^ 2 ∂μ) l (𝓝 0)) :
    TendstoInMeasure μ F l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_
    (by simpa using hlim.div_const (ε ^ 2))
  filter_upwards [hi] with n hn
  have hset : {ω | ε ≤ ‖F n ω - 0‖} = {ω | ε ^ 2 ≤ F n ω ^ 2} := by
    ext ω
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs]
    exact (sq_le_sq₀ hε.le (abs_nonneg _)).symm.trans (by rw [sq_abs])
  rw [hset, le_div_iff₀ (sq_pos_of_pos hε), mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) hn _

theorem integral_sq_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F G : Ω → ℝ}
    (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ)
    (hF2 : Integrable (fun ω => F ω ^ 2) μ) (hG2 : Integrable (fun ω => G ω ^ 2) μ) :
    (∫ ω, (F ω + G ω) ^ 2 ∂μ) = (∫ ω, F ω ^ 2 ∂μ) +
      2 * (∫ ω, F ω * G ω ∂μ) + ∫ ω, G ω ^ 2 ∂μ := by
  have hFG := LatticeProb.integrable_mul_of_sq hF hG hF2 hG2
  have he (ω : Ω) : (F ω + G ω) ^ 2 = F ω ^ 2 + 2 * (F ω * G ω) + G ω ^ 2 := by ring
  simp_rw [he]
  rw [integral_add (f := fun ω => F ω ^ 2 + 2 * (F ω * G ω))
      (hF2.add (hFG.const_mul 2)) hG2,
    integral_add hF2 (hFG.const_mul 2), integral_const_mul]

theorem tendsto_second_moment_add_zero {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {l : Filter ι} {F G : ι → Ω → ℝ}
    (hF : ∀ᶠ n in l, MemLp (F n) 2 μ) (hG : ∀ᶠ n in l, MemLp (G n) 2 μ)
    {A : ℝ} (hFlim : Tendsto (fun n => ∫ ω, F n ω ^ 2 ∂μ) l (𝓝 A))
    (hGlim : Tendsto (fun n => ∫ ω, G n ω ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (F n ω + G n ω) ^ 2 ∂μ) l (𝓝 A) := by
  have hcross : Tendsto (fun n => ∫ ω, F n ω * G n ω ∂μ) l (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using hFlim.sqrt.mul hGlim.sqrt)
    filter_upwards [hF, hG] with n hnF hnG
    rw [Real.norm_eq_abs]
    exact LatticeProb.abs_integral_mul_le hnF.1 hnG.1 hnF.integrable_sq hnG.integrable_sq
  have hsum := (hFlim.add (hcross.const_mul 2)).add hGlim
  have he : (fun n => (∫ ω, F n ω ^ 2 ∂μ) + 2 * (∫ ω, F n ω * G n ω ∂μ) +
      ∫ ω, G n ω ^ 2 ∂μ) =ᶠ[l] (fun n => ∫ ω, (F n ω + G n ω) ^ 2 ∂μ) := by
    filter_upwards [hF, hG] with n hnF hnG
    exact (integral_sq_add hnF.1 hnG.1 hnF.integrable_sq hnG.integrable_sq).symm
  simpa using hsum.congr' he

end Sandpile
