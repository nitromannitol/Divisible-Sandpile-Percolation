import Sandpile.Support.Dgt4AStep1Gaussian

/-!
The two elementary inputs that Step 2 of case (a) takes from Step 1
(`sandpile.tex:5104-5107`): "By `eq:dgt4-centered-value-decay`, stationarity, Jensen's
inequality, and `eq:dgt4-mean-increment-bound`".

Jensen's inequality there is Cauchy-Schwarz against the constant one, which turns the
second moment of Step 1 into a first moment; stationarity is that `P^k` preserves the mean
of a functional whose mean does not depend on the site, since the heat kernel is a
probability.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

/-- `\E|f|\leq(\E f^2)^{1/2}` under a probability measure. -/
theorem integral_abs_le_sqrt_integral_sq {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have habsmem : MemLp (fun x => |f x|) 2 μ := hf.abs
  have hvar := ProbabilityTheory.variance_eq_sub habsmem
  have hnn : 0 ≤ ProbabilityTheory.variance (fun x => |f x|) μ :=
    ProbabilityTheory.variance_nonneg _ _
  have hsqabs : (∫ x, ((fun x => |f x|) ^ 2) x ∂μ) = ∫ x, f x ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show |f x| ^ 2 = f x ^ 2
    rw [sq_abs]
  rw [hvar, hsqabs] at hnn
  have hnn2 : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have habs : 0 ≤ ∫ x, |f x| ∂μ := integral_nonneg fun x => abs_nonneg _
  nlinarith [Real.sq_sqrt hnn2, Real.sqrt_nonneg (∫ x, f x ^ 2 ∂μ), hnn, habs]

variable {d : ℕ}

/-- **`P^k` preserves the mean of a site-invariant functional**: the heat kernel is a
probability and the mean does not depend on the site.  This is the "stationarity" input of
Step 2 (`sandpile.tex:5099-5102`). -/
theorem integral_avgIterate_eq_of_site_invariant (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (F : (Site d → ℝ) → Site d → ℝ)
    (hint : ∀ y : Site d, Integrable (fun ζ => F ζ y) (LatticeProb.iidLaw d ν))
    (hinv : ∀ y : Site d, (∫ ζ, F ζ y ∂(LatticeProb.iidLaw d ν))
      = ∫ ζ, F ζ 0 ∂(LatticeProb.iidLaw d ν)) (k : ℕ) :
    (∫ ζ, (avg^[k] (fun y => F ζ y)) 0 ∂(LatticeProb.iidLaw d ν))
      = ∫ ζ, F ζ 0 ∂(LatticeProb.iidLaw d ν) := by
  have he : (fun ζ : Site d → ℝ => (avg^[k] (fun y => F ζ y)) 0)
      = fun ζ => ∑ z ∈ boxFinset (0 : Site d) k, heatKernel d k 0 z * F ζ z :=
    funext fun ζ => avg_iterate_eq_finsetSum _ _ _
  rw [he, integral_finsetSum _ fun z _ => (hint z).const_mul _]
  have hval : ∀ z ∈ boxFinset (0 : Site d) k,
      (∫ ζ, heatKernel d k 0 z * F ζ z ∂(LatticeProb.iidLaw d ν))
        = heatKernel d k 0 z * ∫ ζ, F ζ 0 ∂(LatticeProb.iidLaw d ν) := by
    intro z _
    rw [integral_const_mul, hinv z]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_mul, sum_heatKernel_boxFinset hd k 0, one_mul]

/-- `P^k` of a square-integrable field is square integrable. -/
theorem memLp_two_avgIterate (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (F : (Site d → ℝ) → Site d → ℝ)
    (hF : ∀ y : Site d, MemLp (fun ζ => F ζ y) 2 (LatticeProb.iidLaw d ν)) (k : ℕ) :
    MemLp (fun ζ : Site d → ℝ => (avg^[k] (fun y => F ζ y)) 0) 2
      (LatticeProb.iidLaw d ν) := by
  have he : (fun ζ : Site d → ℝ => (avg^[k] (fun y => F ζ y)) 0)
      = fun ζ => ∑ z ∈ boxFinset (0 : Site d) k, heatKernel d k 0 z * F ζ z :=
    funext fun ζ => avg_iterate_eq_finsetSum _ _ _
  rw [he]
  exact memLp_finsetSum _ (fun z _ => ((hF z).const_mul _))

/-- `\E[(A+B)^2]\leq2(\E A^2+\E B^2)`, the two-summand form of the inequality that replaces
the `L^2` triangle inequality. -/
theorem integral_add_two_sq_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {A B : α → ℝ}
    (hA : Integrable (fun x => A x ^ 2) μ) (hB : Integrable (fun x => B x ^ 2) μ)
    (hm : AEStronglyMeasurable (fun x => (A x + B x) ^ 2) μ) :
    (∫ x, (A x + B x) ^ 2 ∂μ) ≤ 2 * ((∫ x, A x ^ 2 ∂μ) + ∫ x, B x ^ 2 ∂μ) := by
  have hpt : ∀ x, (A x + B x) ^ 2 ≤ 2 * (A x ^ 2 + B x ^ 2) := by
    intro x
    nlinarith [sq_nonneg (A x - B x)]
  have hmaj : Integrable (fun x => 2 * (A x ^ 2 + B x ^ 2)) μ := (hA.add hB).const_mul 2
  have hLHS : Integrable (fun x => (A x + B x) ^ 2) μ := by
    refine Integrable.mono' hmaj hm (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt x
  refine le_trans (integral_mono hLHS hmaj fun x => hpt x) (le_of_eq ?_)
  rw [integral_const_mul, integral_add hA hB]

end Sandpile
