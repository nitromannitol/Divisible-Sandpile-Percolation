/-
Step 1 of case (a) of `prop:dgt4-contact-asymptotics` (`sandpile.tex:5031-5080`), assembled
at a fixed horizon `j`.

The telescoping of `sandpile.tex:5074-5077` writes
`V_\infty(0)-u_n(0)+\E u_n(0)` as the sum of three terms,

  `\sum_{i<j}P^iD_n(0)`,  `P^jV_\infty(0)`,  and  `-(P^ju_n(0)-\E u_n(0))`,

and the elementary inequality `(a+b+c)^2\leq3(a^2+b^2+c^2)` replaces the `L^2` triangle
inequality; the constant `3` is free because the conclusion carries an existential constant.
The three terms are bounded by `j^2\E[D_n^2]` (`Support/Dgt4ATelescopeL2.lean`), by
`v\sum_z(\sum_{r\geq j}p_r(0,z))^2` (`Support/Dgt4AGaussTailVar.lean`) and by the same square
sum times a moment of the scenery (`Support/Dgt4AOdometerTailVar.lean`).
-/
import Sandpile.Support.Dgt4AGaussTailVar
import Sandpile.Support.Dgt4ATelescopeL2
import Sandpile.Support.Dgt4AOdometerTailVar
import Sandpile.Support.Dgt4AIterateSub
import Sandpile.Support.Dgt4ATelescope

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}


/-- `D_n(x)=(V_\infty-u_n)(x)-P(V_\infty-u_n)(x)` at a general site. -/
theorem sceneryDeviationField_eq_centered (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m => infiniteGreenFieldPartial m ζ y) atTop (𝓝 L))
    (n : ℕ) (x : Site d) :
    (infiniteGreenField ζ x - odometerOf ζ n x)
        - Sandpile.avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) x
      = sceneryDeviationField d ζ n x := by
  have hV : Sandpile.avg (Sandpile.infiniteGreenField ζ) x
      = Sandpile.infiniteGreenField ζ x - ζ x :=
    Sandpile.avg_infiniteGreenField hd ζ x hconv
  have hsub : Sandpile.avg
        (fun y => Sandpile.infiniteGreenField ζ y - Sandpile.odometerOf ζ n y) x
      = Sandpile.avg (fun y => Sandpile.infiniteGreenField ζ y) x
        - Sandpile.avg (fun y => Sandpile.odometerOf ζ n y) x :=
    LatticeProb.walkOp_sub (fun y => Sandpile.infiniteGreenField ζ y)
      (fun y => Sandpile.odometerOf ζ n y) x
  rw [sceneryDeviationField, hsub, hV]
  ring

/-- **The telescoping of Step 1** (`sandpile.tex:5069-5072`) at a scenery where the box
limit of `eq:dgt4-infinite-green-field` converges. -/
theorem centeredValue_eq_telescope (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m => infiniteGreenFieldPartial m ζ y) atTop (𝓝 L))
    (n j : ℕ) (c : ℝ) :
    infiniteGreenField ζ 0 - odometerOf ζ n 0 + c
      = ((avg^[j] (fun y => infiniteGreenField ζ y)) 0
            + (-((avg^[j] (fun y => odometerOf ζ n y)) 0 - c)))
        + ∑ i ∈ Finset.range j, (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0 := by
  have hd1 : 1 ≤ d := by omega
  have htel := Sandpile.avg_iterate_add_telescope hd1
    (fun y => infiniteGreenField ζ y - odometerOf ζ n y) c j
  have hdev : (fun y => (infiniteGreenField ζ y - odometerOf ζ n y)
      - Sandpile.avg (fun w => infiniteGreenField ζ w - odometerOf ζ n w) y)
      = fun y => sceneryDeviationField d ζ n y :=
    funext fun y => sceneryDeviationField_eq_centered hd ζ hconv n y
  rw [hdev] at htel
  have hsplit : (avg^[j] (fun y => (infiniteGreenField ζ y - odometerOf ζ n y) + c)) 0
      = (avg^[j] (fun y => infiniteGreenField ζ y)) 0
        + (-((avg^[j] (fun y => odometerOf ζ n y)) 0 - c)) := by
    have h1 : (fun y => (infiniteGreenField ζ y - odometerOf ζ n y) + c)
        = fun y => infiniteGreenField ζ y + ((-1) * odometerOf ζ n y + c) :=
      funext fun y => by ring
    rw [h1, Sandpile.avg_iterate_add, Sandpile.avg_iterate_add,
      Sandpile.avg_iterate_mul_const, Sandpile.avg_iterate_const hd1]
    ring
  rw [hsplit] at htel
  linarith [htel]



/-- `\E P^ju_n(0)=\E u_n(0)`: the mean odometer does not depend on the site and the heat
kernel is a probability. -/
theorem integral_avgIterate_odometerOf_eq (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (n j : ℕ) :
    (∫ ζ, (avg^[j] (fun y => odometerOf ζ n y)) 0 ∂(LatticeProb.iidLaw d ν))
      = ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
  have he : (fun ζ : Site d → ℝ => (avg^[j] (fun y => odometerOf ζ n y)) 0)
      = fun ζ => ∑ z ∈ boxFinset (0 : Site d) j, heatKernel d j 0 z * odometerOf ζ n z :=
    funext fun ζ => avg_iterate_eq_finsetSum _ _ _
  rw [he, integral_finsetSum _ fun z _ => (integrable_odometerOf d ν hpos n z).const_mul _]
  have hval : ∀ z ∈ boxFinset (0 : Site d) j,
      (∫ ζ, heatKernel d j 0 z * odometerOf ζ n z ∂(LatticeProb.iidLaw d ν))
        = heatKernel d j 0 z * ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
    intro z _
    rw [integral_const_mul, integral_odometerOf_eq d ν n z]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_mul, sum_heatKernel_boxFinset hd j 0, one_mul]

/-- The square of `P^ju_n(0)` is integrable when the one-site law is square integrable. -/
theorem integrable_avgIterate_odometerOf_sq (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hsq : Integrable (fun z : ℝ => z ^ 2) ν) (n j : ℕ) :
    Integrable (fun ζ : Site d → ℝ => (avg^[j] (fun y => odometerOf ζ n y)) 0 ^ 2)
      (LatticeProb.iidLaw d ν) := by
  have he : (fun ζ : Site d → ℝ => (avg^[j] (fun y => odometerOf ζ n y)) 0)
      = fun ζ => ∑ z ∈ boxFinset (0 : Site d) j, heatKernel d j 0 z * odometerOf ζ n z :=
    funext fun ζ => avg_iterate_eq_finsetSum _ _ _
  have hmem : MemLp (fun ζ : Site d → ℝ => (avg^[j] (fun y => odometerOf ζ n y)) 0) 2
      (LatticeProb.iidLaw d ν) := by
    rw [he]
    exact memLp_finsetSum _ (fun z _ => ((memLp_two_odometerOf ν hsq n z).const_mul _))
  exact hmem.integrable_sq

/-- The square of `P^jV_\infty(0)` is integrable under the Gaussian scenery. -/
theorem integrable_avgIterate_infiniteGreenField_sq (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) {j : ℕ} (hj : 1 ≤ j) (v : ℝ≥0) :
    Integrable (fun ζ : Site d → ℝ => ((avg^[j] (fun x => infiniteGreenField ζ x)) 0) ^ 2)
      (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
  classical
  have hS : Measurable fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z := by
    fun_prop
  have he : (fun ζ : Site d → ℝ => ((avg^[j] (fun x => infiniteGreenField ζ x)) 0) ^ 2)
      = fun ζ => (∑ z ∈ boxFinset (0 : Site d) j,
          heatKernel d j 0 z * infiniteGreenField ζ z) ^ 2 := by
    funext ζ
    rw [avg_iterate_eq_finsetSum]
  have hAE : AEStronglyMeasurable
      (fun ζ : Site d → ℝ => ((avg^[j] (fun x => infiniteGreenField ζ x)) 0) ^ 2)
      (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
    have hsum : AEMeasurable (fun ζ : Site d → ℝ => ∑ z ∈ boxFinset (0 : Site d) j,
        heatKernel d j 0 z * infiniteGreenField ζ z)
        (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
      have h := Finset.aemeasurable_sum (μ := LatticeProb.iidLaw d (gaussianReal 0 v))
        (boxFinset (0 : Site d) j)
        (f := fun (z : Site d) (ζ : Site d → ℝ) => heatKernel d j 0 z * infiniteGreenField ζ z)
        (fun z _ => (aemeasurable_infiniteGreenField_iid hd v z).const_mul _)
      have heq : (∑ i ∈ boxFinset (0 : Site d) j,
            fun ζ : Site d → ℝ => heatKernel d j 0 i * infiniteGreenField ζ i)
          = fun ζ : Site d → ℝ => ∑ z ∈ boxFinset (0 : Site d) j,
            heatKernel d j 0 z * infiniteGreenField ζ z := by
        funext ζ
        simp [Finset.sum_apply]
      rw [heq] at h
      exact h
    rw [he]
    exact (hsum.pow_const 2).aestronglyMeasurable
  rw [iidLaw_gaussianReal_eq_map d v] at hAE ⊢
  rw [integrable_map_measure hAE hS.aemeasurable]
  have hiso : Integrable (fun ω : Site d → ℝ =>
      (Real.sqrt (v : ℝ) * ⇑(LatticeProb.gaussIso (tailKernelLp hGH hd hj)) ω) ^ 2)
      (LatticeProb.gaussLaw (Site d)) :=
    ((Lp.memLp (LatticeProb.gaussIso (tailKernelLp hGH hd hj))).const_mul
      (Real.sqrt (v : ℝ))).integrable_sq
  refine hiso.congr ?_
  filter_upwards [ae_avgIterate_infiniteGreenField_eq hGH hd hj (Real.sqrt (v : ℝ))] with ω hω
  rw [Function.comp_apply, hω]

/-- The square of the telescoping sum `\sum_{i<j}P^iD_n(0)` is integrable. -/
theorem integrable_sum_avgIterate_sceneryDeviationField_sq (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n j : ℕ)
    (hint : Integrable (fun ζ : Site d → ℝ => sceneryDeviation d ζ n ^ 2)
      (LatticeProb.iidLaw d ν)) :
    Integrable (fun ζ : Site d → ℝ => (∑ i ∈ Finset.range j,
      (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0) ^ 2)
      (LatticeProb.iidLaw d ν) := by
  have hmem : MemLp (fun ζ : Site d → ℝ => ∑ i ∈ Finset.range j,
      (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0) 2 (LatticeProb.iidLaw d ν) := by
    refine memLp_finsetSum _ fun i _ => ?_
    refine (memLp_two_iff_integrable_sq
      (measurable_avgIterate_sceneryDeviationField n i).aestronglyMeasurable).2 ?_
    exact integrable_avgIterate_sceneryDeviationField_sq hd ν n i hint
  exact hmem.integrable_sq

/-- `\E[(A+B+C)^2]\leq3(\E A^2+\E B^2+\E C^2)`. -/
theorem integral_add_three_sq_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {A B C : α → ℝ}
    (hA : Integrable (fun x => A x ^ 2) μ) (hB : Integrable (fun x => B x ^ 2) μ)
    (hC : Integrable (fun x => C x ^ 2) μ)
    (hm : AEStronglyMeasurable (fun x => (A x + B x + C x) ^ 2) μ) :
    (∫ x, (A x + B x + C x) ^ 2 ∂μ)
      ≤ 3 * ((∫ x, A x ^ 2 ∂μ) + (∫ x, B x ^ 2 ∂μ) + ∫ x, C x ^ 2 ∂μ) := by
  have hpt : ∀ x, (A x + B x + C x) ^ 2 ≤ 3 * (A x ^ 2 + B x ^ 2 + C x ^ 2) := by
    intro x
    nlinarith [sq_nonneg (A x - B x), sq_nonneg (A x - C x), sq_nonneg (B x - C x)]
  have hmaj : Integrable (fun x => 3 * (A x ^ 2 + B x ^ 2 + C x ^ 2)) μ :=
    ((hA.add hB).add hC).const_mul 3
  have hLHS : Integrable (fun x => (A x + B x + C x) ^ 2) μ := by
    refine Integrable.mono' hmaj hm (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt x
  have hAB : Integrable (fun x => A x ^ 2 + B x ^ 2) μ := hA.add hB
  refine le_trans (integral_mono hLHS hmaj fun x => hpt x) (le_of_eq ?_)
  rw [integral_const_mul, integral_add hAB hC, integral_add hA hB]

/-- **Step 1 at a fixed horizon** (`sandpile.tex:5069-5072`): the telescoping bound with
`j` steps, with the constant `3` of the elementary three-term inequality in place of the
`L^2` triangle inequality. -/
theorem integral_centeredValue_sq_le (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) {j : ℕ} (hj : 1 ≤ j) (n : ℕ)
    (hpos : Integrable (fun z : ℝ => max z 0) (gaussianReal 0 v))
    (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v))
    (hint : Integrable (fun ζ : Site d → ℝ => sceneryDeviation d ζ n ^ 2)
      (LatticeProb.iidLaw d (gaussianReal 0 v))) :
    (∫ ζ, (infiniteGreenField ζ 0 - odometerOf ζ n 0
          + ∫ η, odometerOf η n 0 ∂(LatticeProb.iidLaw d (gaussianReal 0 v))) ^ 2
        ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      ≤ 3 * (((j : ℝ) ^ 2 * ∫ ζ, sceneryDeviation d ζ n ^ 2
            ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
        + (∫ ζ, ((avg^[j] (fun x => infiniteGreenField ζ x)) 0) ^ 2
            ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
        + ∫ ζ, ((avg^[j] (fun y => odometerOf ζ n y)) 0
              - ∫ η, (avg^[j] (fun y => odometerOf η n y)) 0
                ∂(LatticeProb.iidLaw d (gaussianReal 0 v))) ^ 2
            ∂(LatticeProb.iidLaw d (gaussianReal 0 v))) := by
  classical
  have hd1 : 1 ≤ d := by omega
  set μ : Measure (Site d → ℝ) := LatticeProb.iidLaw d (gaussianReal 0 v) with hμ
  set c : ℝ := ∫ η, odometerOf η n 0 ∂μ with hc
  set A : (Site d → ℝ) → ℝ := fun ζ => ∑ i ∈ Finset.range j,
    (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0 with hA
  set B : (Site d → ℝ) → ℝ := fun ζ => (avg^[j] (fun x => infiniteGreenField ζ x)) 0 with hB
  set C : (Site d → ℝ) → ℝ := fun ζ => -((avg^[j] (fun y => odometerOf ζ n y)) 0 - c) with hC
  have hIA : Integrable (fun ζ => A ζ ^ 2) μ :=
    integrable_sum_avgIterate_sceneryDeviationField_sq hd1 _ n j hint
  have hIB : Integrable (fun ζ => B ζ ^ 2) μ :=
    integrable_avgIterate_infiniteGreenField_sq hGH hd hj v
  have hICodo : Integrable (fun ζ : Site d → ℝ =>
      (avg^[j] (fun y => odometerOf ζ n y)) 0 ^ 2) μ :=
    integrable_avgIterate_odometerOf_sq _ hsq n j
  have hIC : Integrable (fun ζ => C ζ ^ 2) μ := by
    have hmem : MemLp (fun ζ : Site d → ℝ =>
        (avg^[j] (fun y => odometerOf ζ n y)) 0) 2 μ :=
      (memLp_two_iff_integrable_sq
        (measurable_avg_iterate_odometerOf j n 0).aestronglyMeasurable).2 hICodo
    have : MemLp C 2 μ := by
      have := (hmem.sub (memLp_const (μ := μ) (p := 2) c)).neg
      exact this
    exact this.integrable_sq
  have htel : ∀ᵐ ζ ∂μ,
      infiniteGreenField ζ 0 - odometerOf ζ n 0 + c = A ζ + B ζ + C ζ := by
    have hconvae : ∀ᵐ ζ ∂μ, ∀ y : Site d, ∃ L : ℝ,
        Tendsto (fun m => infiniteGreenFieldPartial m ζ y) atTop (𝓝 L) := by
      rw [ae_all_iff]
      intro y
      exact ae_mem_greenFieldConv_iid hd v y
    filter_upwards [hconvae] with ζ hζ
    rw [centeredValue_eq_telescope (by omega) ζ hζ n j c]
    rw [hA, hB, hC]
    ring
  have hmeas : AEStronglyMeasurable (fun ζ => (A ζ + B ζ + C ζ) ^ 2) μ := by
    have h1 : AEStronglyMeasurable
        (fun ζ : Site d → ℝ =>
          (infiniteGreenField ζ 0 - odometerOf ζ n 0 + c) ^ 2) μ := by
      have hV : AEMeasurable (fun ζ : Site d → ℝ => infiniteGreenField ζ 0) μ :=
        aemeasurable_infiniteGreenField_iid hd v 0
      exact (((hV.sub (measurable_odometerOf n 0).aemeasurable).add_const
        c).pow_const 2).aestronglyMeasurable
    refine h1.congr ?_
    filter_upwards [htel] with ζ hζ
    rw [hζ]
  have hkey := integral_add_three_sq_le (μ := μ) (A := A) (B := B) (C := C) hIA hIB hIC hmeas
  have hlhs : (∫ ζ, (infiniteGreenField ζ 0 - odometerOf ζ n 0 + c) ^ 2 ∂μ)
      = ∫ ζ, (A ζ + B ζ + C ζ) ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [htel] with ζ hζ
    rw [hζ]
  have hAbound : (∫ ζ, A ζ ^ 2 ∂μ)
      ≤ (j : ℝ) ^ 2 * ∫ ζ, sceneryDeviation d ζ n ^ 2 ∂μ :=
    integral_sum_avgIterate_sq_le hd1 _ n j hint
  have hCeq : (∫ ζ, C ζ ^ 2 ∂μ)
      = ∫ ζ, ((avg^[j] (fun y => odometerOf ζ n y)) 0
          - ∫ η, (avg^[j] (fun y => odometerOf η n y)) 0 ∂μ) ^ 2 ∂μ := by
    rw [integral_avgIterate_odometerOf_eq hd1 _ hpos n j]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    rw [hC]
    ring
  rw [hlhs]
  refine hkey.trans ?_
  rw [hCeq]
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  nlinarith [hAbound]

end Sandpile
