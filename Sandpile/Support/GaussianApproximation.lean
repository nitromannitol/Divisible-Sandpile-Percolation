/-
Gaussian exponential concentration passes through uniform smooth
approximations with a common Lipschitz bound.
-/
import Sandpile.Support.GaussianRotation

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
namespace Sandpile

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

lemma integral_sub_abs_le_of_uniform {f g : H → ℝ} (hf : Integrable f (stdGaussian H))
    (hg : Integrable g (stdGaussian H)) {e : ℝ} (he : ∀ x, |f x - g x| ≤ e) :
    |(∫ x, f x ∂stdGaussian H) - ∫ x, g x ∂stdGaussian H| ≤ e := by
  rw [← integral_sub hf hg]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := stdGaussian H)
      (ae_of_all _ (fun x => show ‖f x - g x‖ ≤ e by simpa only [Real.norm_eq_abs] using he x)))

lemma integral_exp_centered_le_of_uniform {f g : H → ℝ} {D D' : ℝ≥0}
    (hf : LipschitzWith D f) (hg : LipschitzWith D' g) {e : ℝ}
    (he : ∀ x, |f x - g x| ≤ e) (a : ℝ) :
    (∫ x, Real.exp (a * (f x - ∫ y, f y ∂stdGaussian H)) ∂stdGaussian H) ≤
      Real.exp (2 * |a| * e) *
        (∫ x, Real.exp (a * (g x - ∫ y, g y ∂stdGaussian H)) ∂stdGaussian H) := by
  have hiF := integrable_lipschitz_gaussian hf (μ := stdGaussian H)
  have hiG := integrable_lipschitz_gaussian hg (μ := stdGaussian H)
  have hmean := integral_sub_abs_le_of_uniform hiF hiG he
  rw [← integral_const_mul]
  apply integral_mono (integrable_exp_lipschitz_gaussian (hf.sub (LipschitzWith.const _)) a)
    ((integrable_exp_lipschitz_gaussian (hg.sub (LipschitzWith.const _)) a).const_mul _)
  intro x
  dsimp only
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb : |(f x - ∫ y, f y ∂stdGaussian H) - (g x - ∫ y, g y ∂stdGaussian H)| ≤ 2 * e := by
    have hh := abs_sub ((f x - g x)) ((∫ y, f y ∂stdGaussian H) - ∫ y, g y ∂stdGaussian H)
    have hi : (f x - ∫ y, f y ∂stdGaussian H) - (g x - ∫ y, g y ∂stdGaussian H) =
        (f x - g x) - ((∫ y, f y ∂stdGaussian H) - ∫ y, g y ∂stdGaussian H) := by ring
    rw [hi]
    exact hh.trans (by linarith [he x])
  have hh : a * ((f x - ∫ y, f y ∂stdGaussian H) -
      (g x - ∫ y, g y ∂stdGaussian H)) ≤ |a| * (2 * e) :=
    (le_abs_self (a * ((f x - ∫ y, f y ∂stdGaussian H) -
      (g x - ∫ y, g y ∂stdGaussian H)))).trans
    (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hb (abs_nonneg a))
  nlinarith

lemma hasSubgaussianMGF_of_smooth_uniform_approximation {f : H → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f)
    (happrox : ∀ e : ℝ, 0 < e → ∃ g : H → ℝ, ContDiff ℝ 1 g ∧ LipschitzWith D g ∧
      ∀ x, |f x - g x| ≤ e) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂stdGaussian H)
      ⟨Real.pi ^ 2 * (D : ℝ) ^ 2 / 4, by positivity⟩ (stdGaussian H) where
  integrable_exp_mul a := integrable_exp_lipschitz_gaussian (hf.sub (LipschitzWith.const _)) a
  mgf_le a := by
    change (∫ x, Real.exp (a * (f x - ∫ y, f y ∂stdGaussian H)) ∂stdGaussian H) ≤
      Real.exp ((Real.pi ^ 2 * (D : ℝ) ^ 2 / 4) * a ^ 2 / 2)
    let B := (Real.pi ^ 2 * (D : ℝ) ^ 2 / 4) * a ^ 2 / 2
    have hb (e : ℝ) (he : 0 < e) :
        (∫ x, Real.exp (a * (f x - ∫ y, f y ∂stdGaussian H)) ∂stdGaussian H) ≤
          Real.exp (2 * |a| * e + B) := by
      obtain ⟨g, hgc, hgl, herr⟩ := happrox e he
      have hh := integral_exp_centered_le_of_uniform hf hgl herr a
      have hc := (hasSubgaussianMGF_smooth_lipschitz hgc hgl).mgf_le a
      calc
        _ ≤ Real.exp (2 * |a| * e) *
            (∫ x, Real.exp (a * (g x - ∫ y, g y ∂stdGaussian H)) ∂stdGaussian H) := hh
        _ ≤ Real.exp (2 * |a| * e) * Real.exp B :=
          mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
        _ = _ := (Real.exp_add _ _).symm
    have hc : Continuous (fun e : ℝ => Real.exp (2 * |a| * e + B)) := by fun_prop
    have ht : Tendsto (fun e : ℝ => Real.exp (2 * |a| * e + B)) (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp B)) := by
      simpa only [mul_zero, zero_add] using (hc.tendsto (0 : ℝ)).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with e he
    exact hb e he

end Sandpile
