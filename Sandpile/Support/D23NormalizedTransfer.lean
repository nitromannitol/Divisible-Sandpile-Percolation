import Sandpile.Support.D23KilledCoupling
import Sandpile.Support.D23Transfer
import Sandpile.Support.D23Field

/-!
# Normalization and marginal-law passage for the localized scenery field

This file carries out the normalization and marginal-law passage of `sandpile.tex:2640-2663`,
transferring the sequential killed coupling into an exact bad-block probability estimate for the
localized scenery field used by the percolation argument. Along the way it records that
`BlockGood` is compatible with rescaling the field by a positive constant
(`blockGood_pos_mul_iff`), that the planar embedding `planePoint` is continuous and its
rescaled grid points recover the exact lattice sites of `planeSite`, and that at integer scales
the killed value on the embedded mesh coincides with the localized field `d23Field`. The main
result, `eventually_measure_bad_d23_block_lt_of_fdd`, combines these with the killed coupling and
the four continuum crossing events to bound the probability of a bad block for the original
scenery law and unscaled level.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
namespace Sandpile.Support
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A positive scalar on the field is transferred to the level. -/
theorem blockGood_pos_mul_iff (R : ℕ) (F : Site 2 → ℝ) (a l : ℝ) (ha : 0 < a)
    (w : Site 2) : BlockGood R (fun z => a * F z) l w ↔ BlockGood R F (l / a) w := by
  constructor
  · apply blockGood_mono_on
    intro z _ hz
    exact (div_le_iff₀ ha).mpr (by simpa [mul_comm] using hz)
  · apply blockGood_mono_on
    intro z _ hz
    simpa [mul_comm] using (div_le_iff₀ ha).mp hz

/-- The planar embedding is continuous in every dimension. -/
theorem continuous_planePoint (d : ℕ) : Continuous (planePoint (d := d)) := by
  apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
  apply continuous_pi
  intro i
  dsimp [planePoint]
  split_ifs <;> fun_prop

/-- Rescaling an embedded mesh point recovers its exact lattice site. -/
theorem floor_plane_gridPt {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Site 2) :
    (fun i => ⌊R * planePoint (d := d) (gridPt (1/R) z) i⌋) = planeSite z := by
  funext i
  dsimp [planePoint, planeSite]
  split_ifs with hi
  · rw [gridPt_apply, show R * (1 / R * (z ⟨i.val, hi⟩ : ℝ)) =
        (z ⟨i.val, hi⟩ : ℝ) by field_simp]
    exact Int.floor_intCast _
  · simp

/-- Every site of the enlarged block maps into the fixed continuum rectangle. -/
theorem gridPt_mem_block_rectangle {R : ℕ} (hR : 0 < R)
    {z : Site 2} (hz : z ∈ planeRectangle (4*R) (4*R)) :
    gridPt (1/(R:ℝ)) z ∈ rectSet ![0,0] ![4,4] := by
  have hRp : (0:ℝ) < R := by exact_mod_cast hR
  have h := (mem_planeRectangle _ _ _).mp hz
  intro i
  fin_cases i <;> simp only [gridPt_apply]
  · constructor
    · exact mul_nonneg (by positivity) (by exact_mod_cast h.1)
    · rw [one_div_mul_eq_div, div_le_iff₀ hRp]
      change (z 0 : ℝ) ≤ 4 * (R : ℝ)
      exact_mod_cast h.2.1
  · constructor
    · exact mul_nonneg (by positivity) (by exact_mod_cast h.2.2.1)
    · rw [one_div_mul_eq_div, div_le_iff₀ hRp]
      change (z 1 : ℝ) ≤ 4 * (R : ℝ)
      exact_mod_cast h.2.2.2

/-- At integer scales the killed value on the embedded mesh is the localized
field in the block definition, with the same horizon and cube. -/
theorem localized_mesh_value_eq_d23Field {d : ℕ} {R : ℕ} (hR : 0 < R)
    (T : ℝ) (ζ : Site d → ℝ) (z : Site 2) :
    localizedOdometer
        (supBox (fun i => ⌊(R:ℝ) * planePoint (d := d) (gridPt (1/(R:ℝ)) z) i⌋) R)
        ζ ⌊T * (R:ℝ)^2⌋₊
        (fun i => ⌊(R:ℝ) * planePoint (d := d) (gridPt (1/(R:ℝ)) z) i⌋) =
      d23Field d R ⌊(R:ℝ)^2 * T⌋₊ ζ z := by
  rw [floor_plane_gridPt (by exact_mod_cast hR), mul_comm T]
  rfl

/-- The killed coupling and the four continuum crossings give the exact
localized block estimate with the original scenery law and unscaled level. -/
theorem eventually_measure_bad_d23_block_lt_of_fdd
    (hStab : Sandpile.External.CubeStoppingStability)
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (hmean : ∀ n, ∫ z, z ∂(ν n) = 0)
    (hexp : ∀ n, Integrable (fun z => Real.exp (θ₀ * |z|)) (ν n))
    (hK₀ : ∀ n, ∫ z, Real.exp (θ₀ * |z|) ∂(ν n) ≤ K₀)
    (Rs : ℕ → ℕ) (hRs : Tendsto Rs atTop atTop)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (Z : ΩW → ℝ → Space d → ℝ)
    (hZcont : ∀ᵐ ω ∂PW, Continuous fun q : ℝ × Space d => Z ω q.1 q.2)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Space d → ℝ≥0 → ΩB → Space d) (hB : ∀ y, IsBrownian d y (B y) PB)
    (T c δ : ℝ) (hT : 0 < T) (hc : 0 < c) (hδ : 0 < δ)
    (hfdd : ∀ (m : ℕ) (r : Fin m → ℝ) (w : Fin m → Space d),
      (∀ i, r i ∈ Set.Icc (0 : ℝ) T) →
      TendstoInDistribution
        (fun n (σ : Site d → ℝ) (i : Fin m) =>
          Frozen.HeatPotentialInvariance.linInterp d (Rs n) (scenery d σ) (r i) (w i))
        atTop (fun ω i => Z ω (r i) (w i))
        (fun n => centeredMassLaw d (ν n)) PW)
    (X : ΩW → Space 2 → ℝ)
    (hX : ∀ ω u, X ω u = brownianValueCube (B (planePoint u)) PB (Z ω) T 1 (planePoint u))
    (hXm : ∀ u, Measurable (fun ω => X ω u))
    (E : Set ΩW)
    (hE : ∀ ω ∈ E, Continuous (X ω) ∧
      Crosses ![0, 0] ![2, 2] 0 {u | 2*c ≤ X ω u} ∧
      Crosses ![0, 0] ![2, 2] 1 {u | 2*c ≤ X ω u} ∧
      Crosses ![0, 0] ![4, 2] 0 {u | 2*c ≤ X ω u} ∧
      Crosses ![0, 0] ![2, 4] 1 {u | 2*c ≤ X ω u})
    (hprob : PW Eᶜ < ENNReal.ofReal (δ / 2)) :
    ∀ᶠ n in atTop, LatticeProb.iidLaw d (ν n)
      {ζ | ¬ BlockGood (Rs n) (d23Field d (Rs n) ⌊(Rs n : ℝ)^2 * T⌋₊ ζ)
        (c * (Rs n : ℝ) ^ (2 - (d:ℝ)/2)) 0} < ENNReal.ofReal δ := by
  let K : Set (Space d) := planePoint '' rectSet ![0,0] ![4,4]
  have hK : IsCompact K := (isCompact_rectSet _ _).image (continuous_planePoint d)
  have hRreal : Tendsto (fun n => (Rs n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hRs
  let F : ℕ → (Site d → ℝ) → Site 2 → ℝ := fun n σ z =>
    (Rs n : ℝ) ^ (-(2 - (d:ℝ)/2)) *
      d23Field d (Rs n) ⌊(Rs n : ℝ)^2 * T⌋₊ (scenery d σ) z
  have hF : ∀ n z, Measurable (fun σ => F n σ z) := fun n z =>
    ((measurable_d23Field hd _ _ z).comp (measurable_scenery d)).const_mul _
  have hcoupling := Sandpile.dlt4_killed_scaling_seq_of_fdd hStab hd hd3 θ₀ K₀ hθ₀
    ν hmean hexp hK₀ (fun n => (Rs n : ℝ)) hRreal PW Z hZcont ΩB PB B hB
    K hK T hT hfdd (c/2) (δ/2) (by positivity) (by positivity)
  have hpos : ∀ᶠ n in atTop, 0 < Rs n := hRs.eventually (eventually_gt_atTop 0)
  have hgrid : ∀ᶠ n in atTop, ∃ Q : Measure ((Site d → ℝ) × ΩW),
      Q.map Prod.fst = centeredMassLaw d (ν n) ∧ Q.map Prod.snd = PW ∧
      Q {p | ∃ z ∈ planeRectangle (4 * Rs n) (4 * Rs n),
        c/2 < |F n p.1 z - X p.2 (gridPt (1/(Rs n : ℝ)) z)|} ≤ ENNReal.ofReal (δ/2) := by
    filter_upwards [hcoupling, hpos] with n hn hRn
    obtain ⟨Q, _, hQf, hQs, hQerr⟩ := hn
    refine ⟨Q, hQf, hQs, le_trans (measure_mono ?_) hQerr⟩
    rintro p ⟨z, hz, herr⟩
    refine ⟨planePoint (gridPt (1/(Rs n : ℝ)) z),
      ⟨_, gridPt_mem_block_rectangle hRn hz, rfl⟩, ?_⟩
    rw [localized_mesh_value_eq_d23Field hRn, ← hX]
    exact herr
  have hbad := eventually_measure_bad_block_lt_of_couplings
    (fun n => centeredMassLaw d (ν n)) PW Rs hRs F hF X hXm E
    (by positivity : 0 < c/2) hδ hE hprob hgrid
  rw [show 2*c - 2*(c/2) = c by ring] at hbad
  filter_upwards [hbad, hpos] with n hn hRn
  have hRp : (0:ℝ) < Rs n := by exact_mod_cast hRn
  have hm : MeasurableSet {ζ : Site d → ℝ |
      ¬ BlockGood (Rs n) (d23Field d (Rs n) ⌊(Rs n : ℝ)^2 * T⌋₊ ζ)
        (c * (Rs n : ℝ) ^ (2 - (d:ℝ)/2)) 0} :=
    (measurableSet_blockGood_field _ (fun z => measurable_d23Field hd _ _ z) _ _ _).compl
  rw [← map_scenery_centeredMassLaw d (ν n) hd, Measure.map_apply (measurable_scenery d) hm]
  convert hn using 1
  congr 1
  ext σ
  change (¬ BlockGood (Rs n) (d23Field d (Rs n) ⌊(Rs n : ℝ)^2*T⌋₊ (scenery d σ))
      (c * (Rs n : ℝ) ^ (2-(d:ℝ)/2)) 0) ↔ ¬ BlockGood (Rs n) (F n σ) c 0
  dsimp only [F]
  rw [blockGood_pos_mul_iff _ _ _ _ (Real.rpow_pos_of_pos hRp _) 0,
    Real.rpow_neg hRp.le, div_inv_eq_mul]

end Sandpile.Support
