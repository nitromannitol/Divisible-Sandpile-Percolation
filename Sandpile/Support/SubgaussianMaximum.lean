import Sandpile.Support.GaussianIntegrability
import Sandpile.Support.CrossingContinuity
import Sandpile.Support.ExponentialMoments
import Mathlib.Probability.Moments.SubGaussian

/-!
# Expected maximum of a sub-Gaussian family

Expected maxima of finite families with a common sub-Gaussian exponential bound, without an
independence hypothesis. The chain runs through a Chernoff-type bound on the exponential moment
of the maximum: `exp_finiteMaximum_le_sum` bounds `exp(a · max f)` by the sum of `exp(a · f i)`,
`integral_exp_abs_le_of_subgaussian` bounds each `∫ exp(a|X_i|)` using the sub-Gaussian moment
generating function `HasSubgaussianMGF`, and the two combine in
`integral_exp_finiteMaximum_abs_le` to a bound linear in the family size `Fintype.card I`. The
main result `integral_finiteMaximum_abs_le` then optimizes the free parameter `a`, via Jensen's
inequality for `Real.exp` (`convexOn_exp`), to `(1 + c/2) · √(log(2·|I|))`, the standard
sub-Gaussian maximal-inequality bound.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace Sandpile

variable {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
  {μ : Measure Ω}

/-- `finiteMaximum` is `1`-Lipschitz in the sup metric on `I → ℝ`, since two maxima can differ
by at most the largest coordinatewise gap. -/
lemma lipschitzWith_finiteMaximum : LipschitzWith 1 (finiteMaximum (I := I)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  exact abs_finiteMaximum_sub_le x y (fun i => by
    simpa only [Real.dist_eq] using dist_le_pi_dist x y i)

/-- The maximum of the absolute values `|f i|` over a nonempty finite index set is nonnegative,
since `|f i| ≥ 0` at the witnessing index. -/
lemma finiteMaximum_abs_nonneg (f : I → ℝ) : 0 ≤ finiteMaximum (fun i => |f i|) := by
  let i : I := Classical.choice inferInstance
  exact (abs_nonneg (f i)).trans (le_finiteMaximum (fun j => |f j|) i)

/-- The maximum of `|f i|` is at most the sum `∑ i, |f i|`, a single term of a sum of
nonnegative terms. -/
lemma finiteMaximum_abs_le_sum (f : I → ℝ) : finiteMaximum (fun i => |f i|) ≤ ∑ i, |f i| := by
  apply (finiteMaximum_le_iff _ _).mpr
  intro i
  exact Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg (f j)) (Finset.mem_univ i)

/-- `ω ↦ finiteMaximum (fun i => |X i ω|)` is a.e.-measurable when each `X i` is, as the
composition of the continuous (hence measurable) map `lipschitzWith_finiteMaximum` with the
a.e.-measurable coordinate map `ω ↦ (fun i => |X i ω|)`. -/
lemma aemeasurable_finiteMaximum_abs {X : I → Ω → ℝ} (hX : ∀ i, AEMeasurable (X i) μ) :
    AEMeasurable (fun ω => finiteMaximum (fun i => |X i ω|)) μ := by
  exact lipschitzWith_finiteMaximum.continuous.measurable.comp_aemeasurable
    (aemeasurable_pi_lambda _ (fun i => (hX i).abs))

/-- `ω ↦ finiteMaximum (fun i => |X i ω|)` is integrable when each `X i` is, by domination with
the integrable sum `∑ i, |X i ω|` via `finiteMaximum_abs_le_sum`. -/
lemma integrable_finiteMaximum_abs {X : I → Ω → ℝ} (hX : ∀ i, Integrable (X i) μ) :
    Integrable (fun ω => finiteMaximum (fun i => |X i ω|)) μ := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ (fun i _ => (hX i).abs))
    (aemeasurable_finiteMaximum_abs (fun i => (hX i).aemeasurable)).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (finiteMaximum_abs_nonneg _)]
  exact finiteMaximum_abs_le_sum _

/-- If `X` has a sub-Gaussian moment generating function of parameter `c` (`HasSubgaussianMGF`),
then `exp(a|X|)` is integrable for every real `a`, since `exp(a|X|) ≤ exp(aX) + exp(-aX)`
(`exp_abs_le_exp_add`) and both summands are integrable by
`HasSubgaussianMGF.integrable_exp_mul`. -/
lemma integrable_exp_abs_of_subgaussian {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) (a : ℝ) : Integrable (fun ω => Real.exp (a * |X ω|)) μ := by
  refine Integrable.mono' ((hX.integrable_exp_mul a).add (hX.integrable_exp_mul (-a)))
    (Real.measurable_exp.comp_aemeasurable
      (hX.aemeasurable.abs.const_mul a)).aestronglyMeasurable ?_
  filter_upwards with ω
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply]
    using exp_abs_le_exp_add a (X ω)

/-- Under a sub-Gaussian bound `HasSubgaussianMGF X c μ`, `∫ exp(a|X|) ≤ 2·exp(c a²/2)`, obtained
by bounding `exp(a|X|)` by `exp(aX) + exp(-aX)` and applying the sub-Gaussian moment generating
function bound `HasSubgaussianMGF.mgf_le` to each term. -/
lemma integral_exp_abs_le_of_subgaussian {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) (a : ℝ) :
    (∫ ω, Real.exp (a * |X ω|) ∂μ) ≤ 2 * Real.exp ((c : ℝ) * a ^ 2 / 2) := by
  calc
    _ ≤ ∫ ω, Real.exp (a * X ω) + Real.exp (-a * X ω) ∂μ :=
      integral_mono (integrable_exp_abs_of_subgaussian hX a)
        ((hX.integrable_exp_mul a).add (hX.integrable_exp_mul (-a)))
        (fun ω => exp_abs_le_exp_add a (X ω))
    _ = (∫ ω, Real.exp (a * X ω) ∂μ) + ∫ ω, Real.exp (-a * X ω) ∂μ :=
      integral_add (hX.integrable_exp_mul a) (hX.integrable_exp_mul (-a))
    _ ≤ Real.exp ((c : ℝ) * a ^ 2 / 2) + Real.exp ((c : ℝ) * (-a) ^ 2 / 2) :=
      add_le_add (hX.mgf_le a) (hX.mgf_le (-a))
    _ = _ := by rw [neg_sq]; ring

/-- Chernoff bound for the max: `exp(a · max f) ≤ ∑ i, exp(a · f i)`, since the maximizing term
is one summand of a sum of positive terms. -/
lemma exp_finiteMaximum_le_sum (f : I → ℝ) (a : ℝ) :
    Real.exp (a * finiteMaximum f) ≤ ∑ i, Real.exp (a * f i) := by
  obtain ⟨i, hi⟩ := finiteMaximum_mem f
  rw [hi]
  exact Finset.single_le_sum (f := fun j => Real.exp (a * f j)) (fun j _ => (Real.exp_pos _).le)
    (Finset.mem_univ i)

/-- `exp(a · finiteMaximum |X i ω|)` is integrable for a finite family with a common sub-Gaussian
bound `c`, by domination with the integrable sum `∑ i, exp(a|X i ω|)` via
`exp_finiteMaximum_le_sum` and `integrable_exp_abs_of_subgaussian`. -/
lemma integrable_exp_finiteMaximum_abs {X : I → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) c μ) (a : ℝ) :
    Integrable (fun ω => Real.exp (a * finiteMaximum (fun i => |X i ω|))) μ := by
  refine Integrable.mono'
    (integrable_finsetSum Finset.univ (fun i _ => integrable_exp_abs_of_subgaussian (hX i) a))
    (Real.measurable_exp.comp_aemeasurable
      ((aemeasurable_finiteMaximum_abs
        (fun i => (hX i).aemeasurable)).const_mul a)).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_finiteMaximum_le_sum _ a

/-- `∫ exp(a · finiteMaximum |X i ω|) ≤ (2 · |I|) · exp(c a²/2)`, obtained by bounding the
integrand termwise by `∑ i, exp(a|X i ω|)` and applying `integral_exp_abs_le_of_subgaussian` to
each of the `Fintype.card I` summands. -/
lemma integral_exp_finiteMaximum_abs_le {X : I → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) c μ) (a : ℝ) :
    (∫ ω, Real.exp (a * finiteMaximum (fun i => |X i ω|)) ∂μ) ≤
      (2 * Fintype.card I) * Real.exp ((c : ℝ) * a ^ 2 / 2) := by
  calc
    _ ≤ ∫ ω, ∑ i, Real.exp (a * |X i ω|) ∂μ :=
      integral_mono (integrable_exp_finiteMaximum_abs hX a)
        (integrable_finsetSum Finset.univ (fun i _ => integrable_exp_abs_of_subgaussian (hX i) a))
        (fun ω => exp_finiteMaximum_le_sum _ a)
    _ = ∑ i, ∫ ω, Real.exp (a * |X i ω|) ∂μ :=
      integral_finsetSum Finset.univ (fun i _ => integrable_exp_abs_of_subgaussian (hX i) a)
    _ ≤ ∑ _ : I, 2 * Real.exp ((c : ℝ) * a ^ 2 / 2) :=
      Finset.sum_le_sum (fun i _ => integral_exp_abs_le_of_subgaussian (hX i) a)
    _ = _ := by simp; ring

variable [IsProbabilityMeasure μ]

/-- The main sub-Gaussian maximal inequality: for a finite family with common sub-Gaussian
parameter `c`, `𝔼[max_i |X i|] ≤ (1 + c/2) · √(log(2|I|))`. Proved by Jensen's inequality for
`Real.exp` applied to `a · finiteMaximum |X i|` at the optimal `a = √(log(2|I|))`, combined with
`integral_exp_finiteMaximum_abs_le` and `Real.log_le_log`. -/
lemma integral_finiteMaximum_abs_le {X : I → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) c μ) :
    (∫ ω, finiteMaximum (fun i => |X i ω|) ∂μ) ≤
      (1 + (c : ℝ) / 2) * Real.sqrt (Real.log (2 * Fintype.card I)) := by
  have hcard : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos (α := I)
  have hlog : 0 < Real.log (2 * Fintype.card I) := Real.log_pos (by linarith)
  let a : ℝ := Real.sqrt (Real.log (2 * Fintype.card I))
  have ha : 0 < a := Real.sqrt_pos.mpr hlog
  have ha2 : a ^ 2 = Real.log (2 * Fintype.card I) := Real.sq_sqrt hlog.le
  have hi := integrable_finiteMaximum_abs (fun i => (hX i).integrable)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all μ (fun _ => mem_univ _)) (hi.const_mul a) (integrable_exp_finiteMaximum_abs hX a)
  rw [integral_const_mul] at hj
  have hb := hj.trans (integral_exp_finiteMaximum_abs_le hX a)
  have hh := Real.log_le_log (Real.exp_pos _) hb
  rw [Real.log_exp, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hh
  change _ ≤ (1 + (c : ℝ) / 2) * a
  nlinarith

end Sandpile
