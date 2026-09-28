import Sandpile.Support.ExplFieldSemigroup
import Sandpile.Support.StopMeasurable
import LatticeProb.Prob.GaussDensity

/-!
# The Brownian transition density for the generator `Δ/(2d)`

The coordinates of a Brownian motion `B` on `Space d` are independent, each with variance
`r/d` at time `r`, the normalization forced by the generator `Δ/(2d)`. Transporting the
resulting product Gaussian law to Euclidean space via the coordinate isometry identifies the
law of a Brownian increment `z + (B r - B 0)` with the measure of density `heatKernelBM d r z`,
and yields the corresponding integrable transition expectation formula.
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal
namespace Sandpile.Support
open Sandpile.Continuum

/-- For a Brownian motion `B` on `Space d`, the `i`-th coordinate of the increment
`z + (B r - B 0)` has law `gaussianReal (z i) (r / d)`, the variance forced on each
coordinate by the generator `Δ/(2d)`. -/
theorem brownian_shift_coord_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 1 ≤ d) {P : Measure Ω} {x : Space d}
    {B : ℝ≥0 → Ω → Space d} (hB : IsBrownian d x B P)
    (r : ℝ≥0) (z : Space d) (i : Fin d) :
    HasLaw (fun b => z i + (B r b i - B 0 b i))
      (gaussianReal (z i) (Real.toNNReal ((r : ℝ) / d))) P := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hs : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd')
  have hv : r / ⟨(Real.sqrt d) ^ 2, sq_nonneg _⟩ = Real.toNNReal ((r : ℝ) / d) := by
    apply NNReal.coe_injective
    change (r : ℝ) / (Real.sqrt d) ^ 2 = _
    rw [Real.sq_sqrt hd'.le, Real.coe_toNNReal _ (by positivity : 0 ≤ (r : ℝ) / d)]
  have hl := gaussianReal_const_add
    (gaussianReal_div_const ((hB.coord i).toIsPreBrownianReal.hasLaw_eval r) (Real.sqrt d)) (z i)
  simp only [zero_div, zero_add] at hl
  rw [← hv]
  apply hl.congr
  filter_upwards [hB.start] with b hb
  rw [hb]
  rw [mul_div_cancel_left₀ _ hs]


/-- The measure on `Space d` with density the product Gaussian density
`∏ i, gaussianPDF (z i) v` equals the pushforward of the product measure
`Measure.pi (fun i => gaussianReal (z i) v)` under the coordinate isometry
`MeasurableEquiv.toLp 2 (Fin d → ℝ)`. -/
theorem euclidean_gaussDensity_mean_eq_map {d : ℕ} (z : Space d)
    (v : ℝ≥0) (hv : v ≠ 0) :
    (volume : Measure (Space d)).withDensity (fun y => ∏ i, gaussianPDF (z i) v (y i)) =
      (Measure.pi fun i : Fin d => gaussianReal (z i) v).map
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)) := by
  classical
  haveI (i : Fin d) :
      IsProbabilityMeasure ((volume : Measure ℝ).withDensity (gaussianPDF (z i) v)) := by
    rw [← gaussianReal_of_var_ne_zero (z i) hv]
    infer_instance
  have hpi : Measure.pi (fun i : Fin d => gaussianReal (z i) v) =
      (volume : Measure (Fin d → ℝ)).withDensity (fun y => ∏ i, gaussianPDF (z i) v (y i)) := by
    simp_rw [gaussianReal_of_var_ne_zero _ hv]
    rw [pi_withDensity_prod (fun _ : Fin d => (volume : Measure ℝ))
      (fun i => gaussianPDF (z i) v) (fun i => measurable_gaussianPDF (z i) v), ← volume_pi]
  have hm : Measurable (fun y : Fin d → ℝ => ∏ i, gaussianPDF (z i) v (y i)) :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDF (z i) v).comp (measurable_pi_apply i)
  rw [hpi, map_withDensity_measurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℝ))
    (PiLp.volume_preserving_toLp (Fin d)) hm]
  rfl


/-- For a Brownian motion `B` on `Space d`, the pushforward law of `z + (B r - B 0)` under
`P` is the measure on `Space d` with density `heatKernelBM d r z`, obtained by transporting
the per-coordinate Gaussian laws of `brownian_shift_coord_hasLaw` to Euclidean space. -/
theorem brownian_shift_map_heatKernelBM {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 1 ≤ d) {P : Measure Ω} {x : Space d}
    {B : ℝ≥0 → Ω → Space d} (hB : IsBrownian d x B P)
    (r : ℝ≥0) (hr : 0 < r) (z : Space d) :
    P.map (fun b => z + (B r b - B 0 b)) =
      (volume : Measure (Space d)).withDensity
        (fun y => ENNReal.ofReal (heatKernelBM d r z y)) := by
  classical
  let f (i : Fin d) (b : Ω) := z i + (B r b i - B 0 b i)
  have hl (i : Fin d) : HasLaw (f i) (gaussianReal (z i) (Real.toNNReal ((r : ℝ) / d))) P :=
    brownian_shift_coord_hasLaw hd hB r z i
  have hind : iIndepFun f P := hB.indep.comp (fun i c => z i + (c r - c 0))
    (fun _ => measurable_const.add ((measurable_pi_apply r).sub (measurable_pi_apply 0)))
  have hp : P.map (fun b i => f i b) = Measure.pi
      (fun i : Fin d => gaussianReal (z i) (Real.toNNReal ((r : ℝ) / d))) := by
    rw [hind.map_fun_eq_pi_map (fun i => (hl i).aemeasurable)]
    congr 1
    funext i
    exact (hl i).map_eq
  have he : P.map (fun b => z + (B r b - B 0 b)) =
      (Measure.pi (fun i : Fin d => gaussianReal (z i) (Real.toNNReal ((r : ℝ) / d)))).map
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)) := by
    rw [← hp,
      AEMeasurable.map_map_of_aemeasurable
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.aemeasurable
        (aemeasurable_pi_lambda _ fun i => (hl i).aemeasurable)]
    rfl
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hv : Real.toNNReal ((r : ℝ) / d) ≠ 0 := by positivity
  rw [he, ← euclidean_gaussDensity_mean_eq_map z _ hv]
  congr 1
  funext y
  rw [heatKernelBM_eq_prod hd (show 0 < (r : ℝ) from hr) z y,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg (z i) _ (y i))]
  rfl

/-- If `heatKernelBM d r z * f` is integrable, the observable `f (z + (B r - B 0))` is
integrable under `P`, and its expectation is the transition expectation formula
`∫ y, heatKernelBM d r z y * f y`. -/
theorem brownian_transition_integral {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 1 ≤ d) {P : Measure Ω} {x : Space d}
    {B : ℝ≥0 → Ω → Space d} (hB : IsBrownian d x B P)
    (r : ℝ≥0) (hr : 0 < r) (z : Space d) (f : Space d → ℝ) (hf : Measurable f)
    (hi : Integrable (fun y => heatKernelBM d r z y * f y) volume) :
    Integrable (fun b => f (z + (B r b - B 0 b))) P ∧
      (∫ b, f (z + (B r b - B 0 b)) ∂P) = ∫ y, heatKernelBM d r z y * f y := by
  let F (b : Ω) := z + (B r b - B 0 b)
  have hF : AEMeasurable F P := aemeasurable_const.add ((hB.aemeasurable r).sub (hB.aemeasurable 0))
  have hmap := brownian_shift_map_heatKernelBM hd hB r hr z
  have hm : Measurable (fun y => ENNReal.ofReal (heatKernelBM d r z y)) := by
    unfold heatKernelBM
    fun_prop
  have hif : Integrable f (P.map F) := by
    rw [hmap]
    apply (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure (Space d)))
      (g := f) hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    simpa only [ENNReal.toReal_ofReal
        (heatKernelBM_nonneg d (show 0 ≤ (r : ℝ) from r.property) z _),
      smul_eq_mul] using hi
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable hF).mp hif, ?_⟩
  calc (∫ b, f (F b) ∂P) = ∫ y, f y ∂P.map F :=
      (integral_map hF hf.aestronglyMeasurable).symm
    _ = ∫ y, heatKernelBM d r z y * f y := by
      rw [hmap, integral_heatKernelBM_measure (show 0 ≤ (r : ℝ) from r.property)]


end Sandpile.Support
