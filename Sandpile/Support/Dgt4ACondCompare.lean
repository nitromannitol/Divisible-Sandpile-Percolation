import Sandpile.Support.Dgt4ACovIterate
import Sandpile.Support.Dgt4AIterateConst

/-!
# Comparing a conditional expectation with its unconditional average

Because the law of the scenery is the image of `N(0, 1) ⊗ ρ` under a shift, the unconditional
average of a quantity is the average, over the conditioning level, of the conditional
expectation at that level. Consequently a quantity that is `L`-Lipschitz in the level differs
from its average over the level by at most `L` times the mean distance to that level, and the
mean distance to a level `s` is at most `|s|` plus the first absolute moment. This file also
records the elementary fact that a function Lipschitz at the origin with a bounded value
there is bounded by an affine function of its argument, and that a uniform almost-everywhere
bound on a difference of integrands passes to the integrals.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

/-- **The comparison with the unconditional average** (`sandpile.tex:5120-5122`): a quantity
whose value at the level `s` differs from its value at the level `s'` by at most `L|s-s'|`
differs from its average over the level by at most the average of `L|s-s'|`. -/
theorem abs_integral_sub_avgIntegral_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (F : ℝ → Ω → ℝ) (L : ℝ) (s : ℝ)
    (hlip : ∀ s' : ℝ, |(∫ ω, F s ω ∂μ) - ∫ ω, F s' ω ∂μ| ≤ L * |s - s'|)
    (hint : Integrable (fun s' => ∫ ω, F s' ω ∂μ) ν)
    (hintabs : Integrable (fun s' => L * |s - s'|) ν) :
    |(∫ ω, F s ω ∂μ) - ∫ s', (∫ ω, F s' ω ∂μ) ∂ν| ≤ ∫ s', L * |s - s'| ∂ν := by
  have h1 : (∫ ω, F s ω ∂μ) - ∫ s', (∫ ω, F s' ω ∂μ) ∂ν
      = ∫ s', ((∫ ω, F s ω ∂μ) - ∫ ω, F s' ω ∂μ) ∂ν := by
    rw [integral_sub (integrable_const _) hint, integral_const]
    simp
  rw [h1]
  refine (abs_integral_le_integral_abs).trans ?_
  exact integral_mono ((integrable_const _).sub hint).abs hintabs hlip

/-- **`\E|b+V_\infty(0)|=O(\E u_n(0))`** (`sandpile.tex:5125-5126`), in the form consumed by
the previous lemma: the mean distance to a level is at most the level plus the first
absolute moment. -/
theorem integral_abs_sub_le {ν : Measure ℝ} [IsProbabilityMeasure ν] (s : ℝ)
    (hint : Integrable (fun z : ℝ => |z|) ν) :
    (∫ z, |s - z| ∂ν) ≤ |s| + ∫ z, |z| ∂ν := by
  have hle : ∀ z : ℝ, |s - z| ≤ |s| + |z| := fun z => by
    calc |s - z| ≤ |s| + |(-z)| := by
          rw [sub_eq_add_neg]; exact abs_add_le _ _
      _ = |s| + |z| := by rw [abs_neg]
  have hmaj : Integrable (fun z : ℝ => |s| + |z|) ν := (integrable_const |s|).add hint
  have hint1 : Integrable (fun z : ℝ => |s - z|) ν := by
    refine Integrable.mono hmaj ((measurable_const.sub measurable_id).abs).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_abs]
    exact (hle z).trans (le_abs_self _)
  have hmono := integral_mono hint1 hmaj hle
  rwa [integral_add (integrable_const |s|) hint, integral_const, smul_eq_mul,
    probReal_univ, one_mul] at hmono

/-- **`m_n(y)\leq C(1+y)`** (`sandpile.tex:5271-5272`): a function Lipschitz at the origin
with a bounded value there is at most `C+L|y|`. -/
theorem le_of_lipschitz_at_zero {m : ℝ → ℝ} {L C : ℝ} (h0 : m 0 ≤ C)
    (hlip : ∀ u : ℝ, |m u - m 0| ≤ L * |u|) (y : ℝ) :
    m y ≤ C + L * |y| := by
  have h := (abs_le.mp (hlip y)).2
  linarith

/-- A uniform pointwise bound on a difference passes to the integrals: this is what turns the
site-by-site Lipschitz bound of `Support/Dgt4AShiftIterate.lean` into the hypothesis of
`abs_integral_sub_avgIntegral_le`. -/
theorem abs_integral_sub_integral_le_of_ae {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (f g : Ω → ℝ) (C : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ᵐ ω ∂μ, |f ω - g ω| ≤ C) :
    |(∫ ω, f ω ∂μ) - ∫ ω, g ω ∂μ| ≤ C := by
  rw [← integral_sub hf hg]
  refine (abs_integral_le_integral_abs).trans ?_
  have hC : (∫ _ω : Ω, C ∂μ) = C := by
    rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
  rw [← hC]
  exact integral_mono_ae (hf.sub hg).abs (integrable_const C) h

/-- Every averaging iterate of the Green covariance at the origin is nonnegative, so the
Lipschitz coefficient of the conditioned level carries no absolute value. -/
theorem avgIterate_greenCovariance_nonneg {d : ℕ} (hd : 1 ≤ d) (j : ℕ) :
    0 ≤ (avg^[j] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0 := by
  have h := avg_iterate_mono j (f := fun _ : Site d => (0 : ℝ))
    (g := fun y => ∑' z : Site d, green d y z * green d 0 z)
    (fun y => greenCovariance_nonneg y) 0
  rwa [avg_iterate_const hd j 0 0] at h

end Sandpile
