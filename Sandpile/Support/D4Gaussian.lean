/-
Gaussian fluctuations and the exact variance limit for the dimension-four odometer.
The membrane limit transfers through a reflection error vanishing in the second moment.
-/
import Sandpile.Support.D4L2Error
import Sandpile.Support.MembraneGaussian
import Sandpile.Support.SecondMomentConvergence

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

theorem memLp_two_membrane {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (t : ℕ) (x : Site d) :
    MemLp (fun ζ => membrane ζ t x) 2 (LatticeProb.iidLaw d ν) := by
  have h := memLp_two_linear_pick ν hsq (boxEnum x t) (boxEnum_injective x t)
    (fun i => greenTime d t x (boxEnum x t i))
  exact h.ae_eq (Eventually.of_forall fun ζ => (membrane_eq_sum_boxEnum t x ζ).symm)

theorem integral_div_sqrt_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    (∫ ω, (F ω / Real.sqrt L) ^ 2 ∂μ) = (∫ ω, F ω ^ 2 ∂μ) / L := by
  simp_rw [div_pow, Real.sq_sqrt hL]
  rw [integral_div]

theorem odometer_gaussian_four_iid (hVS : External.VarianceScale)
    (hPaired : External.PairedLocalCLTFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0) (θ : ℝ) (hθ : 0 < θ)
    (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    TendstoInDistribution
      (fun (t : ℕ) (ζ : Site 4 → ℝ) => (odometerOf ζ t 0 -
        (∫ η, odometerOf η t 0 ∂LatticeProb.iidLaw 4 ν)) / Real.sqrt (Real.log t))
      atTop (id : ℝ → ℝ) (fun _ => LatticeProb.iidLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal (4 * variance id ν / Real.pi ^ 2))) ∧
    Tendsto (fun t : ℕ => variance (fun ζ => odometerOf ζ t 0) (LatticeProb.iidLaw 4 ν) /
      Real.log t) atTop (𝓝 (4 * variance id ν / Real.pi ^ 2)) := by
  let P := LatticeProb.iidLaw 4 ν
  let V (t : ℕ) (ζ : Site 4 → ℝ) := membrane ζ t 0 / Real.sqrt (Real.log t)
  let E (t : ℕ) (ζ : Site 4 → ℝ) :=
    (odometerOf ζ t 0 - (∫ η, odometerOf η t 0 ∂P) - membrane ζ t 0) / Real.sqrt (Real.log t)
  have hV (t : ℕ) : MemLp (V t) 2 P := by
    simpa only [V, inv_mul_eq_div] using
      (memLp_two_membrane ν hsq t (0 : Site 4)).const_mul (Real.sqrt (Real.log t))⁻¹
  have hE (t : ℕ) : MemLp (E t) 2 P := by
    have hu := memLp_two_odometerOf (d := 4) ν (by simpa using hsq.integrable_sq) t 0
    have he := (hu.sub (memLp_const (∫ η, odometerOf η t 0 ∂P))).sub
      (memLp_two_membrane ν hsq t (0 : Site 4))
    simpa only [E, Pi.sub_apply, inv_mul_eq_div] using
      he.const_mul (Real.sqrt (Real.log t))⁻¹
  have hElim : Tendsto (fun t => ∫ ζ, E t ζ ^ 2 ∂P) atTop (𝓝 0) := by
    refine (tendsto_linearization_second_moment_div_log_four hVS ν hmean θ hθ hexp 0).congr' ?_
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with t ht
    exact (integral_div_sqrt_sq P _ _
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t)))).symm
  have hEinMeasure : TendstoInMeasure P E atTop (fun _ => 0) :=
    tendstoInMeasure_zero_of_second_moment P
      (Eventually.of_forall fun t => (hE t).integrable_sq) hElim
  have hsum (t : ℕ) (ζ : Site 4 → ℝ) : V t ζ + E t ζ =
      (odometerOf ζ t 0 - (∫ η, odometerOf η t 0 ∂P)) / Real.sqrt (Real.log t) := by
    dsimp only [V, E]
    ring
  constructor
  · have hVclt := tendsto_membrane_gaussian_four hPaired ν hsq hmean
    have h := hVclt.add_of_tendstoInMeasure_const hEinMeasure (fun t => (hE t).aemeasurable)
    exact h.congr (fun t => Eventually.of_forall fun ζ => hsum t ζ)
      (Eventually.of_forall fun z => add_zero z)
  · have hVlim : Tendsto (fun t => ∫ ζ, V t ζ ^ 2 ∂P) atTop
        (𝓝 (4 * variance id ν / Real.pi ^ 2)) := by
      refine (tendsto_membrane_variance_four hPaired ν hsq).congr' ?_
      filter_upwards [eventually_ge_atTop (3 : ℕ)] with t ht
      rw [show (∫ ζ, V t ζ ^ 2 ∂P) =
        (∫ ζ, membrane ζ t 0 ^ 2 ∂P) / Real.log t from
          integral_div_sqrt_sq P _ _
            (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t)))]
      congr 1
      rw [variance_eq_integral (measurable_membrane t 0).aemeasurable,
        integral_membrane_zero ν (hsq.integrable (by norm_num)) hmean]
      simp only [sub_zero, P]
    have hlim := tendsto_second_moment_add_zero P (Eventually.of_forall hV)
      (Eventually.of_forall hE) hVlim hElim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with t ht
    simp_rw [hsum]
    rw [integral_div_sqrt_sq P _ _
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t)))]
    rw [variance_eq_integral (measurable_odometerOf t 0).aemeasurable]

theorem odometer_gaussian_four_mass (hVS : External.VarianceScale)
    (hPaired : External.PairedLocalCLTFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0) (θ : ℝ) (hθ : 0 < θ)
    (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    TendstoInDistribution
      (fun (t : ℕ) (σ : Site 4 → ℝ) =>
        (odometer σ t 0 - meanOdometer (centeredMassLaw 4 ν) t) / Real.sqrt (Real.log t))
      atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal (4 * variance id ν / Real.pi ^ 2))) ∧
    Tendsto (fun t : ℕ => variance (fun σ => odometer σ t 0) (centeredMassLaw 4 ν) /
      Real.log t) atTop (𝓝 (4 * variance id ν / Real.pi ^ 2)) := by
  obtain ⟨hclt, hvar⟩ := odometer_gaussian_four_iid hVS hPaired ν hsq hmean θ hθ hexp
  have hm (t : ℕ) : Measurable (fun ζ : Site 4 → ℝ => (odometerOf ζ t 0 -
      (∫ η, odometerOf η t 0 ∂LatticeProb.iidLaw 4 ν)) / Real.sqrt (Real.log t)) :=
    ((measurable_odometerOf t 0).sub measurable_const).div_const _
  have hmp : MeasurePreserving (scenery 4) (centeredMassLaw 4 ν) (LatticeProb.iidLaw 4 ν) :=
    ⟨measurable_scenery 4, map_scenery_centeredMassLaw 4 ν (by norm_num)⟩
  have he (t : ℕ) (σ : Site 4 → ℝ) : (odometer σ t 0 - meanOdometer (centeredMassLaw 4 ν) t) /
      Real.sqrt (Real.log t) = (odometerOf (scenery 4 σ) t 0 -
        (∫ η, odometerOf η t 0 ∂LatticeProb.iidLaw 4 ν)) / Real.sqrt (Real.log t) := by
    rw [odometer_eq_odometerOf, meanOdometer_eq 4 ν (by norm_num)]
  constructor
  · refine ⟨fun t => ?_, measurable_id.aemeasurable, ?_⟩
    · simpa only [he, Function.comp_def] using ((hm t).comp hmp.measurable).aemeasurable
    · convert hclt.tendsto using 2 with t
      apply Subtype.ext
      simp_rw [he]
      have hmap := Measure.map_map (μ := centeredMassLaw 4 ν) (hm t) hmp.measurable
      rw [hmp.map_eq] at hmap
      simpa only [Function.comp_def] using hmap.symm
  · have hev (t : ℕ) : variance (fun σ => odometer σ t 0) (centeredMassLaw 4 ν) =
        variance (fun ζ => odometerOf ζ t 0) (LatticeProb.iidLaw 4 ν) := by
      simp_rw [odometer_eq_odometerOf]
      exact hmp.variance_fun_comp (measurable_odometerOf t 0).aemeasurable
    simpa only [hev] using hvar

end Sandpile
