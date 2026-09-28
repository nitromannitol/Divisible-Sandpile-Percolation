import Sandpile.Frozen.D23CriticalLevelPercolation
import Sandpile.Frozen.D4CriticalLevelPercolation
import Sandpile.Frozen.DGT4Nontriviality
import Sandpile.Support.Crit23Centering
import Sandpile.Support.D23Component
import Sandpile.Support.D4Centering
import Sandpile.Support.SceneryBridge
import Sandpile.Support.ExponentialMoments

/-!
# Assembling Theorem 1.2 from its three regime theorems

The assembly of Theorem 1.2 of `sandpile.tex` (`sandpile.tex:113-126`,
`thm:main-critical-level-percolation`) from its three regime theorems: the
dimension-two-and-three theorem `thm:d23-critical-level-percolation` (`sandpile.tex:2560-2575`),
the dimension-four theorem `thm:d4-critical-level-percolation` (`sandpile.tex:3952-3968`) and
the high-dimensional theorem `thm:dgt4-nontriviality` (`sandpile.tex:6625-6647`), exactly as
the paper's proof at `sandpile.tex:130-142` does. The paper writes `ζ := (σ-1)/(2d)`; the mass
law of `μ` is the centred mass law of the law of `(s-1)/(2d)`
(`crit23_centeredMassLaw_map_centering`), the hypotheses of the main theorem on `μ` become the
hypotheses of the regime theorems on that law (`crit23_integral_centering_eq_zero`,
`crit23_evariance_centering_le`, `crit23_integrable_exp_centering`,
`crit23_integral_exp_centering`), and the regime conclusions, which place the infinite
component inside a coordinate plane, are pushed to the ambient lattice by
`hasInfiniteComponent_criticalScale_of_plane` (dimensions two and three) and
`hasInfiniteComponent_planeEmbed` (dimension four). The high-dimensional theorem is stated in
the scenery language, so its conclusion is transported by `odometer_eq_odometerOf` and
`map_scenery_centeredMassLaw`.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace Sandpile

/-- The critical scale in dimensions two and three is `t^{(4-d)/4}`. -/
theorem criticalScale_d23 (d : ℕ) (hd : d = 2 ∨ d = 3) (t : ℕ) :
    criticalScale d t = (t : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
  unfold criticalScale
  rw [if_pos (by omega : d ≤ 3)]

/-- The critical scale in dimension four is `log t`. -/
theorem criticalScale_four (t : ℕ) : criticalScale 4 t = Real.log t := by
  unfold criticalScale
  norm_num

/-- The critical scale in dimensions five and higher is `(log t)^{2/d}`. -/
theorem criticalScale_dgt4 (d : ℕ) (hd : 5 ≤ d) (t : ℕ) :
    criticalScale d t = (Real.log t) ^ ((2 : ℝ) / d) := by
  unfold criticalScale
  rw [if_neg (by omega : ¬ d ≤ 3), if_neg (by omega : ¬ d = 4)]

/-- The variance of the centred law is finite when the exponential moment is. -/
theorem evariance_centering_lt_top (d : ℕ) (_hd : 1 ≤ d) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (θ₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexp : Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ) :
    evariance id (μ.map fun s => (s - 1) / (2 * (d : ℝ))) < ⊤ := by
  have hf : Measurable fun s : ℝ => (s - 1) / (2 * (d : ℝ)) := by fun_prop
  haveI : IsProbabilityMeasure (μ.map fun s : ℝ => (s - 1) / (2 * (d : ℝ))) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  refine ProbabilityTheory.evariance_lt_top ?_
  have h1 : Integrable (fun s : ℝ => Real.exp (θ₀ * |s|)) μ := by
    refine (hexp.const_mul (Real.exp θ₀)).mono' (by fun_prop)
      (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h2 : |s| ≤ |s - 1| + 1 := by
      have h5 : |(s - 1) + (1 : ℝ)| ≤ |s - 1| + |(1 : ℝ)| := abs_add_le (s - 1) 1
      have h6 : (s - 1) + (1 : ℝ) = s := by ring
      rw [h6] at h5
      simpa using h5
    nlinarith
  have hsq : Integrable (fun s : ℝ => s ^ 2) μ := integrable_sq_of_exp hθ₀ h1
  have hsub : Integrable (fun s : ℝ => (s - 1) ^ 2) μ := by
    have hbound : Integrable (fun s : ℝ => 2 * s ^ 2 + 2) μ := by
      have h2 : Integrable (fun s : ℝ => 2 * s ^ 2) μ := by
        simpa using hsq.const_mul (2 : ℝ)
      simpa using h2.add (integrable_const (2 : ℝ))
    refine hbound.mono' (by fun_prop) (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (s + 1)]
  have hmap : Integrable (fun z : ℝ => z ^ 2)
      (μ.map fun s : ℝ => (s - 1) / (2 * (d : ℝ))) := by
    rw [integrable_map_measure (by fun_prop) hf.aemeasurable]
    refine (hsub.const_mul (((2 * (d : ℝ)) ^ 2)⁻¹)).congr
      (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.comp_apply]
    rw [div_pow, div_eq_inv_mul]
  exact (memLp_two_iff_integrable_sq (by fun_prop)).mpr hmap

/-- The dimension-two-and-three branch of the main theorem: the frozen
`thm:d23-critical-level-percolation` at the centred law of `μ`, pushed to the
ambient lattice. -/
theorem crit23_d23_branch
    (hLSS : Sandpile.External.LSSDomination)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hOcc : Sandpile.External.BallOccupationDensity)
    (_hLocalCLT : Sandpile.External.LocalCLT)
    (hCube : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (ν₀ θ₀ K₀ : ℝ)
    (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.massLaw d μ),
          Sandpile.HasInfiniteComponent
            {x | c * Sandpile.criticalScale d t < Sandpile.odometer σ t x} := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hd3 : d ≤ 3 := by omega
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  obtain ⟨c, hc, t₀, hmain⟩ :=
    Sandpile.Frozen.d23_critical_level_percolation hLSS hRSWc hPitt hOcc hCube
      d hd (ν₀ / (2 * (d : ℝ)))
      (2 * (d : ℝ) * θ₀) K₀ (by positivity) (by positivity)
  refine ⟨c, hc, t₀, ?_⟩
  intro μ hμ hmean hvar hexpint hexp t ht
  letI := hμ
  set ν : Measure ℝ := μ.map fun s : ℝ => (s - 1) / (2 * (d : ℝ)) with hν
  have hf : Measurable fun s : ℝ => (s - 1) / (2 * (d : ℝ)) := by fun_prop
  have hνprob : IsProbabilityMeasure ν := by
    rw [hν]
    exact Measure.isProbabilityMeasure_map hf.aemeasurable
  have hid : Integrable id μ := integrable_id_of_shifted_exp_moment μ θ₀ hθ₀ hexpint
  have h1 : ∫ z, z ∂ν = 0 := crit23_integral_centering_eq_zero d hd1 μ hid hmean
  have h2 : ENNReal.ofReal ((ν₀ / (2 * (d : ℝ))) ^ 2) ≤ evariance id ν :=
    crit23_evariance_centering_le d hd1 μ hid hmean ν₀ hvar
  have h3 : Integrable (fun z => Real.exp (2 * (d : ℝ) * θ₀ * |z|)) ν :=
    crit23_integrable_exp_centering d hd1 μ θ₀ hexpint
  have h4 : ∫ z, Real.exp (2 * (d : ℝ) * θ₀ * |z|) ∂ν ≤ K₀ := by
    rw [hν, crit23_integral_exp_centering d hd1 μ θ₀]
    exact hexp
  have hlaw : Sandpile.centeredMassLaw d ν = Sandpile.massLaw d μ :=
    crit23_centeredMassLaw_map_centering d hd1 μ
  have hae := hmain ν hνprob h1 h2 h3 h4 t ht
  rw [hlaw] at hae
  filter_upwards [hae] with σ hσ
  exact hasInfiniteComponent_criticalScale_of_plane hd2 hd3 c t σ hσ

/-- The dimension-four branch of the main theorem: the frozen
`thm:d4-critical-level-percolation` at the centred law of `μ`, pushed to the
ambient lattice. -/
theorem crit23_d4_branch
    (_hBallGreen : Sandpile.External.BallGreenBounds)
    (hRSW : Sandpile.External.PlanarRSW)
    (hLSS : Sandpile.External.LSSDomination)
    (_hVarScale : Sandpile.External.VarianceScale)
    (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.massLaw 4 μ),
          Sandpile.HasInfiniteComponent
            {x | c * Sandpile.criticalScale 4 t < Sandpile.odometer σ t x} := by
  obtain ⟨c, hc, t₀, hmain⟩ :=
    massLaw_critical_level_percolation_four ν₀ θ₀ K₀ hθ₀
      (Sandpile.Frozen.d4_critical_level_percolation hRSW hLSS
        (ν₀ / 8) (8 * θ₀) K₀ (by positivity) (by positivity))
  refine ⟨c, hc, t₀, ?_⟩
  intro μ hμ hmean hvar hexpint hexp t ht
  have hae := hmain μ hμ hmean hvar hexpint hexp t ht
  filter_upwards [hae] with σ hσ
  rwa [criticalScale_four]

/-- The high-dimensional branch of the main theorem: the frozen
`thm:dgt4-nontriviality` at the centred law of `μ`, transported from the
scenery language to the mass-field language. -/
theorem crit23_dgt4_branch
    (hBoundary : Sandpile.External.ExteriorBoundaryConnected)
    (_hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.massLaw d μ),
          Sandpile.HasInfiniteComponent
            {x | c * Sandpile.criticalScale d t < Sandpile.odometer σ t x} := by
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  obtain ⟨b, C, hb, hC, hmain⟩ :=
    Sandpile.Frozen.dgt4_nontriviality hBoundary d hd (2 * (d : ℝ) * θ₀) K₀
      (by positivity)
  obtain ⟨c, hc, t₀, hreg⟩ :=
    hmain (ν₀ / (2 * (d : ℝ))) (by positivity)
  refine ⟨c, hc, t₀, ?_⟩
  intro μ hμ hmean hvar hexpint hexp t ht
  letI := hμ
  set ν : Measure ℝ := μ.map fun s : ℝ => (s - 1) / (2 * (d : ℝ)) with hν
  have hf : Measurable fun s : ℝ => (s - 1) / (2 * (d : ℝ)) := by fun_prop
  have hνprob : IsProbabilityMeasure ν := by
    rw [hν]
    exact Measure.isProbabilityMeasure_map hf.aemeasurable
  have hid : Integrable id μ := integrable_id_of_shifted_exp_moment μ θ₀ hθ₀ hexpint
  have h1 : ∫ z, z ∂ν = 0 := crit23_integral_centering_eq_zero d hd1 μ hid hmean
  have h2 : ENNReal.ofReal ((ν₀ / (2 * (d : ℝ))) ^ 2) ≤ evariance id ν :=
    crit23_evariance_centering_le d hd1 μ hid hmean ν₀ hvar
  have h2' : evariance id ν < ⊤ :=
    evariance_centering_lt_top d hd1 μ θ₀ hθ₀ hexpint
  have h3 : Integrable (fun z => Real.exp (2 * (d : ℝ) * θ₀ * |z|)) ν :=
    crit23_integrable_exp_centering d hd1 μ θ₀ hexpint
  have h4 : ∫ z, Real.exp (2 * (d : ℝ) * θ₀ * |z|) ∂ν ≤ K₀ := by
    rw [hν, crit23_integral_exp_centering d hd1 μ θ₀]
    exact hexp
  have hae := (hreg ν hνprob h1 h2 h2' h3 h4 t ht).1
  have hmp : MeasurePreserving (scenery d) (Sandpile.centeredMassLaw d ν)
      (LatticeProb.iidLaw d ν) :=
    ⟨measurable_scenery d, map_scenery_centeredMassLaw d ν hd1⟩
  have h' := hmp.quasiMeasurePreserving.ae hae
  have hlaw : Sandpile.centeredMassLaw d ν = Sandpile.massLaw d μ :=
    crit23_centeredMassLaw_map_centering d hd1 μ
  rw [hlaw] at h'
  filter_upwards [h'] with σ hσ
  refine hasInfiniteComponent_mono ?_ hσ
  intro x hx
  have h4' : c * (Real.log t) ^ ((2 : ℝ) / d) < odometerOf (scenery d σ) t x := hx
  have h5 : odometerOf (scenery d σ) t x = odometer σ t x :=
    (congrFun (odometer_eq_odometerOf σ t) x).symm
  rw [h5] at h4'
  rwa [criticalScale_dgt4 d hd t]

/-- **Theorem 1.2 from its three regime theorems.**  The conclusion is exactly
that of `thm:main-critical-level-percolation`; the three regime theorems enter
as the frozen statements they are. -/
theorem critical_level_percolation_assembly
    (hBallGreen : Sandpile.External.BallGreenBounds)
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hVarScale : Sandpile.External.VarianceScale)
    (hRSW : Sandpile.External.PlanarRSW)
    (hLSS : Sandpile.External.LSSDomination)
    (hBoundary : Sandpile.External.ExteriorBoundaryConnected)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hOcc : Sandpile.External.BallOccupationDensity)
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hCube : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.massLaw d μ),
          Sandpile.HasInfiniteComponent
            {x | c * Sandpile.criticalScale d t < Sandpile.odometer σ t x} := by
  rcases lt_or_ge d 4 with h4 | h4
  · exact crit23_d23_branch hLSS hRSWc hPitt hOcc hLocalCLT hCube d (by omega) ν₀ θ₀ K₀ hν₀ hθ₀
  · rcases lt_or_ge d 5 with h5 | h5
    · obtain rfl : d = 4 := by omega
      exact crit23_d4_branch hBallGreen hRSW hLSS hVarScale ν₀ θ₀ K₀ hν₀ hθ₀
    · exact crit23_dgt4_branch hBoundary hGreenHigh d h5 ν₀ θ₀ K₀ hν₀ hθ₀

end Sandpile
