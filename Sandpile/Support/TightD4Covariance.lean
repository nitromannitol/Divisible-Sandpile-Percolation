/-
The covariance decay of the diffusively scaled four-dimensional odometer,
`eq:d4-finite-covariance-bound` and `eq:d4-covariance-decay` of
`sandpile.tex:3288-3316`, in the form the tightness lemma of
`ssec:sobolev-tightness` consumes.

The chain is the paper's: the covariance of two odometers is between zero and
`2 Var(ζ(0))` times the doubled Green kernel, which decays like a small power;
the normalization `R^{-ε}` converts the growth `t^{ε}` at `t = ⌊TR²⌋` into the
constant `T^{ε}`; and `(1+|x-y|²)^{-ε}` is `(1+|x-y|)^{-2ε}` up to `2^{ε}`.
-/
import Sandpile.Support.TightSmallPower
import Sandpile.Support.SceneryBridge
import Sandpile.Support.Concentration
import Sandpile.Frozen.SobolevTightness

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

variable {d : ℕ}

/-- Covariance is carried along a measurable map of the sample space. -/
theorem covariance_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] {φ : α → β} (hφ : Measurable φ)
    {f g : β → ℝ} (hf : AEStronglyMeasurable f (μ.map φ))
    (hg : AEStronglyMeasurable g (μ.map φ)) :
    covariance (fun a => f (φ a)) (fun a => g (φ a)) μ = covariance f g (μ.map φ) := by
  have h1 : ∫ ω, f ω ∂(μ.map φ) = ∫ a, f (φ a) ∂μ := integral_map hφ.aemeasurable hf
  have h2 : ∫ ω, g ω ∂(μ.map φ) = ∫ a, g (φ a) ∂μ := integral_map hφ.aemeasurable hg
  have h3 : ∫ ω, (f ω - ∫ w, f w ∂(μ.map φ)) * (g ω - ∫ w, g w ∂(μ.map φ)) ∂(μ.map φ)
      = ∫ a, (f (φ a) - ∫ w, f w ∂(μ.map φ)) * (g (φ a) - ∫ w, g w ∂(μ.map φ)) ∂μ :=
    integral_map hφ.aemeasurable
      ((hf.sub aestronglyMeasurable_const).mul (hg.sub aestronglyMeasurable_const))
  simp only [ProbabilityTheory.covariance]
  rw [h3, h1, h2]

/-- The odometer of a mass field is square integrable when the one-site scenery
law is. -/
theorem memLp_two_odometer (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (hd : 1 ≤ d) (t : ℕ) (x : Site d) :
    MemLp (fun σ : Site d → ℝ => Sandpile.odometer σ t x) 2 (centeredMassLaw d ν) := by
  have hmap := map_scenery_centeredMassLaw d ν hd
  have h : MemLp (fun ζ : Site d → ℝ => odometerOf ζ t x) 2
      ((centeredMassLaw d ν).map (scenery d)) := by
    rw [hmap]; exact memLp_two_odometerOf ν hsq t x
  have heq : (fun σ : Site d → ℝ => Sandpile.odometer σ t x)
      = (fun ζ : Site d → ℝ => odometerOf ζ t x) ∘ (scenery d) := by
    funext σ; exact congrFun (odometer_eq_odometerOf σ t) x
  rw [heq]
  exact (memLp_map_measure_iff (by rw [hmap]; exact (measurable_odometerOf t x).aestronglyMeasurable)
    (measurable_scenery d).aemeasurable).mp h

/-- The odometer of a mass field is integrable when the one-site scenery law is
integrable on the positive part. -/
theorem integrable_odometer (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (hd : 1 ≤ d) (t : ℕ) (x : Site d) :
    Integrable (fun σ : Site d → ℝ => Sandpile.odometer σ t x) (centeredMassLaw d ν) := by
  have hmap := map_scenery_centeredMassLaw d ν hd
  have h : Integrable (fun ζ : Site d → ℝ => odometerOf ζ t x)
      ((centeredMassLaw d ν).map (scenery d)) := by
    rw [hmap]; exact integrable_odometerOf d ν hpos t x
  have heq : (fun σ : Site d → ℝ => Sandpile.odometer σ t x)
      = (fun ζ : Site d → ℝ => odometerOf ζ t x) ∘ (scenery d) := by
    funext σ; exact congrFun (odometer_eq_odometerOf σ t) x
  rw [heq]
  have hasm : AEStronglyMeasurable (fun ζ : Site d → ℝ => odometerOf ζ t x)
      ((centeredMassLaw d ν).map (scenery d)) := by
    rw [hmap]; exact (measurable_odometerOf t x).aestronglyMeasurable
  exact (integrable_map_measure hasm (measurable_scenery d).aemeasurable).mp h

/-- The mean of the odometer does not depend on the site. -/
theorem integral_odometer_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    (t : ℕ) (x : Site d) :
    ∫ σ, Sandpile.odometer σ t x ∂(centeredMassLaw d ν)
      = meanOdometer (centeredMassLaw d ν) t := by
  have hmap := map_scenery_centeredMassLaw d ν hd
  have h1 : ∫ σ, Sandpile.odometer σ t x ∂(centeredMassLaw d ν)
      = ∫ σ, odometerOf (scenery d σ) t x ∂(centeredMassLaw d ν) :=
    integral_congr_ae (Filter.Eventually.of_forall fun σ =>
      congrFun (odometer_eq_odometerOf σ t) x)
  have h2 := integral_map (μ := centeredMassLaw d ν) (φ := scenery d)
      (f := fun ζ : Site d → ℝ => odometerOf ζ t x)
      (measurable_scenery d).aemeasurable
      (by rw [hmap]; exact (measurable_odometerOf t x).aestronglyMeasurable)
  rw [hmap] at h2
  rw [h1, ← h2, integral_odometerOf_eq d ν t x, ← meanOdometer_eq d ν hd t]

/-- The covariance of two odometers of a mass field is the covariance of the
odometers of its scenery. -/
theorem covariance_odometer_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    (t : ℕ) (x y : Site d) :
    covariance (fun σ => Sandpile.odometer σ t x) (fun σ => Sandpile.odometer σ t y)
        (centeredMassLaw d ν)
      = covariance (fun ζ => odometerOf ζ t x) (fun ζ => odometerOf ζ t y)
        (LatticeProb.iidLaw d ν) := by
  have hmap := map_scenery_centeredMassLaw d ν hd
  have hx : (fun σ : Site d → ℝ => Sandpile.odometer σ t x)
      = fun σ => odometerOf (scenery d σ) t x := by
    funext σ; exact congrFun (odometer_eq_odometerOf σ t) x
  have hy : (fun σ : Site d → ℝ => Sandpile.odometer σ t y)
      = fun σ => odometerOf (scenery d σ) t y := by
    funext σ; exact congrFun (odometer_eq_odometerOf σ t) y
  have hax : AEStronglyMeasurable (fun ζ : Site d → ℝ => odometerOf ζ t x)
      ((centeredMassLaw d ν).map (scenery d)) := by
    rw [hmap]; exact (measurable_odometerOf t x).aestronglyMeasurable
  have hay : AEStronglyMeasurable (fun ζ : Site d → ℝ => odometerOf ζ t y)
      ((centeredMassLaw d ν).map (scenery d)) := by
    rw [hmap]; exact (measurable_odometerOf t y).aestronglyMeasurable
  rw [hx, hy, covariance_comp (φ := scenery d)
    (f := fun ζ : Site d → ℝ => odometerOf ζ t x)
    (g := fun ζ : Site d → ℝ => odometerOf ζ t y)
    (centeredMassLaw d ν) (measurable_scenery d) hax hay, hmap]

/-- The two Euclidean site distances of the repository are the same function. -/
theorem external_latticeDist_eq (x y : Site d) :
    Sandpile.External.latticeDist x y = Sandpile.Frozen.SobolevTightness.latticeDist x y := rfl

/-- The square distance and the distance give comparable decaying powers. -/
theorem rpow_neg_one_add_sq_le (ε L : ℝ) (hε : 0 < ε) (hL : 0 ≤ L) :
    (1 + L ^ 2) ^ (-ε) ≤ 2 ^ ε * (1 + L) ^ (-(2 * ε)) := by
  have h1 : (0:ℝ) < (1 + L) ^ 2 / 2 := by positivity
  have h2 : (1 + L) ^ 2 / 2 ≤ 1 + L ^ 2 := by nlinarith [sq_nonneg (1 - L)]
  have hmain := Real.rpow_le_rpow_of_nonpos h1 h2 (le_of_lt (neg_neg_iff_pos.mpr hε))
  refine hmain.trans (le_of_eq ?_)
  rw [Real.div_rpow (by positivity) (by norm_num),
    ← Real.rpow_natCast (1 + L) 2, ← Real.rpow_mul (by linarith)]
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  have h3 : ((2:ℕ) : ℝ) * -ε = -(2 * ε) := by push_cast; ring
  rw [h3]
  field_simp

/-- The covariance decay of the diffusively scaled four-dimensional odometer,
`eq:d4-covariance-decay`: after the normalization `R^{-ε}`, the covariance of
the odometer at time `⌊TR²⌋` decays like `(1+|x-y|)^{-2ε}` with a constant that
does not depend on `R`. -/
theorem exists_d4_covariance_decay (hHK : Sandpile.External.HeatKernelBounds)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : Integrable (fun z => z ^ 2) ν)
    (hpos : Integrable (fun z => max z 0) ν)
    (T : ℝ) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ x y : Site 4,
      |covariance
          (fun σ => R ^ (-ε) * (Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
            meanOdometer (centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊))
          (fun σ => R ^ (-ε) * (Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y -
            meanOdometer (centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊))
          (centeredMassLaw 4 ν)|
        ≤ K * (1 + Sandpile.Frozen.SobolevTightness.latticeDist x y) ^ (-(2 * ε)) := by
  obtain ⟨C₃, hC₃, hgb⟩ := exists_green_product_small_power hHK ε hε hε1
  have hV : (0:ℝ) ≤ variance (id : ℝ → ℝ) ν := variance_nonneg _ _
  refine ⟨2 * variance (id : ℝ → ℝ) ν * C₃ * T ^ ε * 2 ^ ε, by positivity, ?_⟩
  intro R hR x y
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  set n := ⌊T * R ^ 2⌋₊ with hn
  set m := meanOdometer (centeredMassLaw 4 ν) n with hm
  set P := centeredMassLaw 4 ν with hP
  have hix : Integrable (fun σ : Site 4 → ℝ => Sandpile.odometer σ n x) P :=
    integrable_odometer ν hpos (by norm_num) n x
  have hiy : Integrable (fun σ : Site 4 → ℝ => Sandpile.odometer σ n y) P :=
    integrable_odometer ν hpos (by norm_num) n y
  have hsub : covariance (fun σ => Sandpile.odometer σ n x - m)
      (fun σ => Sandpile.odometer σ n y - m) P
      = covariance (fun σ => Sandpile.odometer σ n x) (fun σ => Sandpile.odometer σ n y) P := by
    rw [covariance_sub_const_left hix m, covariance_sub_const_right hiy m]
  have hsplit : covariance
      (fun σ => R ^ (-ε) * (Sandpile.odometer σ n x - m))
      (fun σ => R ^ (-ε) * (Sandpile.odometer σ n y - m)) P
      = R ^ (-ε) * (R ^ (-ε) *
        covariance (fun σ => Sandpile.odometer σ n x) (fun σ => Sandpile.odometer σ n y) P) := by
    have e1 : (fun σ : Site 4 → ℝ => R ^ (-ε) * (Sandpile.odometer σ n x - m))
        = (R ^ (-ε)) • (fun σ : Site 4 → ℝ => Sandpile.odometer σ n x - m) := rfl
    have e2 : (fun σ : Site 4 → ℝ => R ^ (-ε) * (Sandpile.odometer σ n y - m))
        = (R ^ (-ε)) • (fun σ : Site 4 → ℝ => Sandpile.odometer σ n y - m) := rfl
    rw [e1, e2, covariance_smul_left, covariance_smul_right, hsub]
  have hcnn : 0 ≤ covariance (fun ζ : Site 4 → ℝ => odometerOf ζ n x)
      (fun ζ => odometerOf ζ n y) (LatticeProb.iidLaw 4 ν) :=
    covariance_odometerOf_nonneg ν hsq n n x y
  have hcle := covariance_odometerOf_le (d := 4) ν hsq n n x y
  have hgreen := hgb n x y
  have hLnn : (0:ℝ) ≤ Sandpile.External.latticeDist x y := Real.sqrt_nonneg _
  have hAnn : (0:ℝ) < (1 + Sandpile.External.latticeDist x y ^ 2) ^ (-ε) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hcov0 : covariance (fun σ : Site 4 → ℝ => Sandpile.odometer σ n x)
      (fun σ => Sandpile.odometer σ n y) P
      = covariance (fun ζ : Site 4 → ℝ => odometerOf ζ n x)
        (fun ζ => odometerOf ζ n y) (LatticeProb.iidLaw 4 ν) :=
    covariance_odometer_eq ν (by norm_num) n x y
  have hcovbd : covariance (fun σ : Site 4 → ℝ => Sandpile.odometer σ n x)
      (fun σ => Sandpile.odometer σ n y) P
      ≤ 2 * variance (id : ℝ → ℝ) ν *
        (C₃ * (n : ℝ) ^ ε * (1 + Sandpile.External.latticeDist x y ^ 2) ^ (-ε)) := by
    rw [hcov0]
    refine hcle.trans ?_
    exact mul_le_mul_of_nonneg_left hgreen (by positivity)
  have hcovnn : 0 ≤ covariance (fun σ : Site 4 → ℝ => Sandpile.odometer σ n x)
      (fun σ => Sandpile.odometer σ n y) P := by rw [hcov0]; exact hcnn
  -- the scaling of the time factor
  have hnle : (n : ℝ) ≤ T * R ^ 2 := Nat.floor_le (by positivity)
  have hRpow : R ^ (-ε) * R ^ (-ε) = R ^ (-(2 * ε)) := by
    rw [← Real.rpow_add hR0]; congr 1; ring
  have hRsq : (T * R ^ 2) ^ ε = T ^ ε * R ^ (2 * ε) := by
    rw [Real.mul_rpow (le_of_lt hT) (by positivity), ← Real.rpow_natCast R 2,
      ← Real.rpow_mul (le_of_lt hR0)]
    norm_num
  have htime : R ^ (-(2 * ε)) * (n : ℝ) ^ ε ≤ T ^ ε := by
    have h1 : (n : ℝ) ^ ε ≤ (T * R ^ 2) ^ ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hnle (le_of_lt hε)
    have h2 : R ^ (-(2 * ε)) * (n : ℝ) ^ ε ≤ R ^ (-(2 * ε)) * (T ^ ε * R ^ (2 * ε)) := by
      rw [← hRsq]
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.rpow_pos_of_pos hR0 _))
    refine h2.trans (le_of_eq ?_)
    have : R ^ (-(2 * ε)) * R ^ (2 * ε) = 1 := by
      rw [← Real.rpow_add hR0]; simp
    calc R ^ (-(2 * ε)) * (T ^ ε * R ^ (2 * ε))
        = (R ^ (-(2 * ε)) * R ^ (2 * ε)) * T ^ ε := by ring
      _ = T ^ ε := by rw [this, one_mul]
  have hsqcomp := rpow_neg_one_add_sq_le ε (Sandpile.External.latticeDist x y) hε hLnn
  rw [hsplit, abs_of_nonneg (by positivity)]
  calc R ^ (-ε) * (R ^ (-ε) *
        covariance (fun σ : Site 4 → ℝ => Sandpile.odometer σ n x)
          (fun σ => Sandpile.odometer σ n y) P)
      = R ^ (-(2 * ε)) * covariance (fun σ : Site 4 → ℝ => Sandpile.odometer σ n x)
          (fun σ => Sandpile.odometer σ n y) P := by rw [← hRpow]; ring
    _ ≤ R ^ (-(2 * ε)) * (2 * variance (id : ℝ → ℝ) ν *
          (C₃ * (n : ℝ) ^ ε * (1 + Sandpile.External.latticeDist x y ^ 2) ^ (-ε))) :=
        mul_le_mul_of_nonneg_left hcovbd (le_of_lt (Real.rpow_pos_of_pos hR0 _))
    _ = (2 * variance (id : ℝ → ℝ) ν * C₃) * (R ^ (-(2 * ε)) * (n : ℝ) ^ ε) *
          (1 + Sandpile.External.latticeDist x y ^ 2) ^ (-ε) := by ring
    _ ≤ (2 * variance (id : ℝ → ℝ) ν * C₃) * T ^ ε *
          (1 + Sandpile.External.latticeDist x y ^ 2) ^ (-ε) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htime (by positivity))
          (le_of_lt hAnn)
    _ ≤ (2 * variance (id : ℝ → ℝ) ν * C₃) * T ^ ε *
          (2 ^ ε * (1 + Sandpile.Frozen.SobolevTightness.latticeDist x y) ^ (-(2 * ε))) := by
        rw [← external_latticeDist_eq x y]
        exact mul_le_mul_of_nonneg_left hsqcomp (by positivity)
    _ = (2 * variance (id : ℝ → ℝ) ν * C₃ * T ^ ε * 2 ^ ε) *
          (1 + Sandpile.Frozen.SobolevTightness.latticeDist x y) ^ (-(2 * ε)) := by ring

end Sandpile.Support
