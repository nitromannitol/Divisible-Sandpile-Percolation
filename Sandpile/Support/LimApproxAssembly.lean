import Sandpile.Support.LimDiffKernel
import Sandpile.Support.LimBoxUniform
import Sandpile.Support.LimFieldVersion

/-!
# Uniform approximation by the ball-stopped field

This is `Sandpile.Support.BallStoppedApproximation`, the analytic input of
`thm-limiting-odometer-crossing`: on finitely many rectangles and finitely many scales,
the ball-stopped field is uniformly within `c` of the ball field, off an event of
probability `δ`, once the horizon is large.

Everything the chaining consumes is proved: both moment inputs fall below any threshold
(`LimDiffKernel.lean`), the Kolmogorov box bound is wrapped as a threshold statement
(`LimBoxUniform.lean`), and an almost surely continuous field has a measurable
everywhere continuous modification (`LimFieldVersion.lean`).  What is left, and what this
module does, is to move between the rectangle `rectSet a b` of the plane with its
Euclidean metric and the box `Set.Icc a b` of `Fin 2 → ℝ` with the supremum metric that
the chaining lemma is stated for, and to sum the finitely many exceptional events.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal

namespace Sandpile.Support

/-! ### The metric bridge -/

/-- The plane point of a box parameter, as a point of the plane. -/
theorem planePoint_toLp_coord {d : ℕ} (u' : Fin 2 → ℝ) (i : Fin d) :
    (planePoint (d := d) (WithLp.toLp 2 u') : Space d) i
      = if h : (i : ℕ) < 2 then u' ⟨(i : ℕ), h⟩ else 0 := rfl

/-- Membership of a plane point coming from a box parameter in `rectSet a b` is exactly
membership of the parameter in the corresponding box `Set.Icc a b`. -/
theorem rectSet_toLp_iff {a b : Fin 2 → ℝ} (u' : Fin 2 → ℝ) :
    (WithLp.toLp 2 u' : Space 2) ∈ rectSet a b ↔ u' ∈ Set.Icc a b := by
  constructor
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  · intro h i
    exact ⟨h.1 i, h.2 i⟩

/-- **The Euclidean distance of two plane points is at most `√2` times the supremum
distance of the box parameters.** -/
theorem norm_planePoint_sub_le {d : ℕ} (hd : d = 2 ∨ d = 3) (u' v' : Fin 2 → ℝ) :
    ‖planePoint (d := d) (WithLp.toLp 2 u') - planePoint (d := d) (WithLp.toLp 2 v')‖
      ≤ Real.sqrt 2 * dist u' v' := by
  have hcoord : ∀ i : Fin d,
      ((planePoint (d := d) (WithLp.toLp 2 u') - planePoint (d := d) (WithLp.toLp 2 v'))
        : Space d) i
        = (if h : (i : ℕ) < 2 then u' ⟨(i : ℕ), h⟩ else 0)
          - (if h : (i : ℕ) < 2 then v' ⟨(i : ℕ), h⟩ else 0) := by
    intro i
    rfl
  have hsq : ‖planePoint (d := d) (WithLp.toLp 2 u')
      - planePoint (d := d) (WithLp.toLp 2 v')‖ ^ 2 ≤ 2 * dist u' v' ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hbd : ∀ i : Fin 2, (u' i - v' i) ^ 2 ≤ dist u' v' ^ 2 := by
      intro i
      have h1 : |u' i - v' i| ≤ dist u' v' := by
        have := dist_le_pi_dist u' v' i
        rwa [Real.dist_eq] at this
      have h2 : (0 : ℝ) ≤ dist u' v' := dist_nonneg
      nlinarith [abs_nonneg (u' i - v' i), sq_abs (u' i - v' i)]
    rcases hd with rfl | rfl
    · rw [Fin.sum_univ_two]
      simp only [hcoord]
      norm_num
      have h0 := hbd 0
      have h1 := hbd 1
      nlinarith [h0, h1]
    · rw [Fin.sum_univ_three]
      simp only [hcoord]
      norm_num
      have h0 := hbd 0
      have h1 := hbd 1
      nlinarith [h0, h1]
  have hnn : (0 : ℝ) ≤ ‖planePoint (d := d) (WithLp.toLp 2 u')
      - planePoint (d := d) (WithLp.toLp 2 v')‖ := norm_nonneg _
  have hd0 : (0 : ℝ) ≤ dist u' v' := dist_nonneg
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2,
    mul_nonneg (Real.sqrt_nonneg 2) hd0]

/-! ### The bound on one rectangle at one scale -/

/-- **On one rectangle and at one scale, the ball-stopped field is uniformly within `c` of
the ball field off an event of probability `ε`, once the horizon is large.** -/
theorem eventually_measure_bad_rect_le (hOcc : Sandpile.External.BallOccupationDensity)
    {d : ℕ} (hdd : d = 2 ∨ d = 3) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (a b : Fin 2 → ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW),
      IsProbabilityMeasure PW → ∀ (W : (Space d → ℝ) → ΩW → ℝ), IsWhiteNoise d W PW →
      (∀ᵐ ω ∂PW, Continuous fun u : Space 2 => ballField d W s u ω) →
      ∀ (Z : ℝ → Space d → ΩW → ℝ),
      (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d 1 W t x ω) →
      ContinuousHeatPotential d Z PW →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB), IsProbabilityMeasure PB →
      ∀ (B : Space d → ℝ≥0 → ΩB → Space d), (∀ y, IsBrownian d y (B y) PB) →
      (∀ y ω, Continuous fun t => B y t ω) → (∀ y t, StronglyMeasurable (B y t)) →
      PW {ω | ∀ u ∈ rectSet a b,
          |ballStoppedField d Z PB B s T u ω - ballField d W s u ω| ≤ c}ᶜ
        ≤ ENNReal.ofReal ε := by
  have hd : 1 ≤ d := by rcases hdd with rfl | rfl <;> norm_num
  have hd3 : d ≤ 3 := by rcases hdd with rfl | rfl <;> norm_num
  have hd0 : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  -- the exponents
  set p : ℝ := 25 with hpdef
  have hp : 0 < p := by norm_num [hpdef]
  set q : ℝ := p / 12 with hqdef
  have hq : ((2 : ℕ) : ℝ) < q := by
    rw [hqdef, hpdef]
    norm_num
  -- the threshold from the chaining bound
  obtain ⟨M₀, hM₀pos, hM₀⟩ := exists_moment_threshold (k := 2) a b p q hp hq hc hε
  -- the moment threshold that produces it
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 ^ q := by
    have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact Real.one_le_rpow h1 (by rw [hqdef, hpdef]; norm_num)
  have hM₀' : 0 < M₀ / Real.sqrt 2 ^ q := by
    have : (0 : ℝ) < Real.sqrt 2 ^ q := by
      have : (0 : ℝ) < Real.sqrt 2 := by positivity
      exact Real.rpow_pos_of_pos this _
    positivity
  filter_upwards [eventually_diffField_moment_bounds hOcc hdd hs0 hs1 hp hM₀',
    eventually_gt_atTop (0 : ℝ)] with T hT hTpos
  intro ΩW _ PW hPW W hW hXc Z hmod hZc ΩB _ PB hPB B hB hBc hBm
  obtain ⟨hbase, hmom⟩ := hT ΩW PW hPW W hW ΩB PB hPB B hB hBc hBm
  -- the kernels and the measurable white-noise version of the difference field
  set f : Space 2 → Space d → ℝ := fun u y =>
    2 * (d : ℝ) * ballKernel d s u y - ballStoppedKernel d PB B s T u y with hfdef
  have hmemf : ∀ u : Space 2, MemLp (f u) 2 (volume : Measure (Space d)) := by
    intro u
    exact ((memLp_ballKernel hdd hs0 u).const_mul _).sub
      (memLp_ballStoppedKernel hd hd3 PB hBc hBm hTpos.le u)
  set X : Space 2 → ΩW → ℝ := fun u ω => -(2 * (d : ℝ))⁻¹ * W (f u) ω with hXdef
  have hXmeas : ∀ u, Measurable (X u) := by
    intro u
    exact (hW.meas (f u) (hmemf u)).const_mul _
  set D : Space 2 → ΩW → ℝ := fun u ω =>
    ballStoppedField d Z PB B s T u ω - ballField d W s u ω with hDdef
  have hae : ∀ u, D u =ᵐ[PW] X u := by
    intro u
    filter_upwards [ae_whiteNoise_ballField_sub hdd hW hmod hZc PB hBc hBm hs0 hTpos u]
      with ω hω
    have hne : (2 * (d : ℝ)) ≠ 0 := ne_of_gt hd0
    show ballStoppedField d Z PB B s T u ω - ballField d W s u ω
        = -(2 * (d : ℝ))⁻¹ * W (f u) ω
    rw [← hω]
    field_simp
    ring
  have hcontD : ∀ᵐ ω ∂PW, Continuous fun u : Space 2 => D u ω := by
    filter_upwards [hXc, hZc T hTpos] with ω h1 h2
    exact (continuous_ballStoppedField hB hBc hBm hs0.le hTpos h2).sub h1
  obtain ⟨Y, hYmeas, hYcont, hYae⟩ :=
    exists_measurable_continuous_version (P := PW) D X hXmeas hae hcontD
  -- the field on the box
  set Xbox : (Fin 2 → ℝ) → ΩW → ℝ := fun u' ω => Y (WithLp.toLp 2 u') ω with hXboxdef
  have hXboxmeas : ∀ u', Measurable (Xbox u') := fun u' => hYmeas _
  have hXboxcont : ∀ ω, ContinuousOn (fun u' => Xbox u' ω) (Set.Icc a b) := by
    intro ω
    refine Continuous.continuousOn ?_
    exact (hYcont ω).comp (PiLp.continuous_toLp 2 fun _ => ℝ)
  -- the moment bounds transfer to the box field
  have haeX : ∀ u' : Fin 2 → ℝ, Xbox u' =ᵐ[PW] X (WithLp.toLp 2 u') := by
    intro u'
    filter_upwards [hYae, hae (WithLp.toLp 2 u')] with ω h1 h2
    show Y (WithLp.toLp 2 u') ω = X (WithLp.toLp 2 u') ω
    rw [h1 (WithLp.toLp 2 u')]
    exact h2
  have hconst : (0 : ℝ) < (2 * (d : ℝ))⁻¹ := by positivity
  have hconstle : ((2 * (d : ℝ))⁻¹) ^ p ≤ 1 := by
    refine Real.rpow_le_one (le_of_lt hconst) ?_ hp.le
    rw [inv_le_one_iff₀]
    right
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  -- the increment moment
  have habs : ∀ (u v : Space 2) (ω : ΩW), |X u ω - X v ω| ^ p
      = ((2 * (d : ℝ))⁻¹) ^ p * |W (f u) ω - W (f v) ω| ^ p := by
    intro u v ω
    have hrw : X u ω - X v ω = -(2 * (d : ℝ))⁻¹ * (W (f u) ω - W (f v) ω) := by
      simp only [hXdef]
      ring
    rw [hrw, abs_mul, abs_neg, abs_of_pos hconst,
      Real.mul_rpow (le_of_lt hconst) (abs_nonneg _)]
  have hintW : ∀ u v : Space 2,
      Integrable (fun ω => |W (f u) ω - W (f v) ω| ^ p) PW := fun u v =>
    integrable_abs_rpow_whiteNoise_sub PW W hW (f u) (f v) (hmemf u) (hmemf v) hp
  have hintX : ∀ u' v' : Fin 2 → ℝ,
      Integrable (fun ω => |Xbox u' ω - Xbox v' ω| ^ p) PW := by
    intro u' v'
    refine Integrable.congr
      ((hintW (WithLp.toLp 2 u') (WithLp.toLp 2 v')).const_mul (((2 * (d : ℝ))⁻¹) ^ p)) ?_
    filter_upwards [haeX u', haeX v'] with ω h1 h2
    rw [← habs, h1, h2]
  have hmomX : ∀ u' ∈ Set.Icc a b, ∀ v' ∈ Set.Icc a b,
      (∫ ω, |Xbox u' ω - Xbox v' ω| ^ p ∂PW) ≤ M₀ * dist u' v' ^ q := by
    intro u' _ v' _
    have hrw : (∫ ω, |Xbox u' ω - Xbox v' ω| ^ p ∂PW)
        = ((2 * (d : ℝ))⁻¹) ^ p
          * ∫ ω, |W (f (WithLp.toLp 2 u')) ω - W (f (WithLp.toLp 2 v')) ω| ^ p ∂PW := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [haeX u', haeX v'] with ω h1 h2
      rw [h1, h2, habs]
    rw [hrw]
    have hmomuv := hmom (WithLp.toLp 2 u') (WithLp.toLp 2 v')
    have hnorm := norm_planePoint_sub_le (d := d) hdd u' v'
    have hd0' : (0 : ℝ) ≤ dist u' v' := dist_nonneg
    have hnn : (0 : ℝ) ≤ ‖planePoint (d := d) (WithLp.toLp 2 u')
        - planePoint (d := d) (WithLp.toLp 2 v')‖ := norm_nonneg _
    have hpow : ‖planePoint (d := d) (WithLp.toLp 2 u')
        - planePoint (d := d) (WithLp.toLp 2 v')‖ ^ q
        ≤ Real.sqrt 2 ^ q * dist u' v' ^ q := by
      have h1 : ‖planePoint (d := d) (WithLp.toLp 2 u')
          - planePoint (d := d) (WithLp.toLp 2 v')‖ ^ q
          ≤ (Real.sqrt 2 * dist u' v') ^ q :=
        Real.rpow_le_rpow hnn hnorm (by rw [hqdef, hpdef]; norm_num)
      rwa [Real.mul_rpow (Real.sqrt_nonneg 2) hd0'] at h1
    have hMle : M₀ / Real.sqrt 2 ^ q * (Real.sqrt 2 ^ q * dist u' v' ^ q)
        = M₀ * dist u' v' ^ q := by
      have hs2 : (0 : ℝ) < Real.sqrt 2 ^ q := by
        have : (0 : ℝ) < Real.sqrt 2 := by positivity
        exact Real.rpow_pos_of_pos this _
      field_simp
    have hint0 : (0 : ℝ) ≤ ∫ ω, |W (f (WithLp.toLp 2 u')) ω
        - W (f (WithLp.toLp 2 v')) ω| ^ p ∂PW := by
      refine integral_nonneg fun ω => ?_
      exact Real.rpow_nonneg (abs_nonneg _) _
    have hstep : ((2 * (d : ℝ))⁻¹) ^ p
        * ∫ ω, |W (f (WithLp.toLp 2 u')) ω - W (f (WithLp.toLp 2 v')) ω| ^ p ∂PW
        ≤ ∫ ω, |W (f (WithLp.toLp 2 u')) ω - W (f (WithLp.toLp 2 v')) ω| ^ p ∂PW := by
      nlinarith [hconstle, hint0, Real.rpow_nonneg (le_of_lt hconst) p]
    refine hstep.trans ?_
    refine hmomuv.trans ?_
    rw [← hMle]
    exact mul_le_mul_of_nonneg_left hpow hM₀'.le
  -- the base point moment
  have hintX0 : Integrable (fun ω => |Xbox a ω| ^ p) PW := by
    have hzero := ae_whiteNoise_zero hW
    have hint := integrable_abs_rpow_whiteNoise_sub PW W hW (f (WithLp.toLp 2 a))
      (fun _ => (0 : ℝ)) (hmemf _) MemLp.zero' hp
    refine Integrable.congr (hint.const_mul (((2 * (d : ℝ))⁻¹) ^ p)) ?_
    filter_upwards [haeX a, hzero] with ω h1 h2
    have hrw : X (WithLp.toLp 2 a) ω = -(2 * (d : ℝ))⁻¹ * (W (f (WithLp.toLp 2 a)) ω
        - W (fun _ => (0 : ℝ)) ω) := by
      rw [h2]
      simp only [hXdef]
      ring
    show ((2 * (d : ℝ))⁻¹) ^ p * |W (f (WithLp.toLp 2 a)) ω - W (fun _ => (0 : ℝ)) ω| ^ p
      = |Xbox a ω| ^ p
    rw [h1, hrw, abs_mul, abs_neg, abs_of_pos hconst,
      Real.mul_rpow (le_of_lt hconst) (abs_nonneg _)]
  have hbaseX : (∫ ω, |Xbox a ω| ^ p ∂PW) ≤ M₀ := by
    have hzero := ae_whiteNoise_zero hW
    have hrw : (∫ ω, |Xbox a ω| ^ p ∂PW)
        = ((2 * (d : ℝ))⁻¹) ^ p * ∫ ω, |W (f (WithLp.toLp 2 a)) ω| ^ p ∂PW := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [haeX a] with ω h1
      have hrw2 : Xbox a ω = -(2 * (d : ℝ))⁻¹ * W (f (WithLp.toLp 2 a)) ω := by
        rw [h1]
      rw [hrw2, abs_mul, abs_neg, abs_of_pos hconst,
        Real.mul_rpow (le_of_lt hconst) (abs_nonneg _)]
    rw [hrw]
    have hb := hbase (WithLp.toLp 2 a)
    have hint0 : (0 : ℝ) ≤ ∫ ω, |W (f (WithLp.toLp 2 a)) ω| ^ p ∂PW := by
      refine integral_nonneg fun ω => ?_
      exact Real.rpow_nonneg (abs_nonneg _) _
    have hstep : ((2 * (d : ℝ))⁻¹) ^ p * ∫ ω, |W (f (WithLp.toLp 2 a)) ω| ^ p ∂PW
        ≤ ∫ ω, |W (f (WithLp.toLp 2 a)) ω| ^ p ∂PW := by
      nlinarith [hconstle, hint0, Real.rpow_nonneg (le_of_lt hconst) p]
    have hM₀le : M₀ / Real.sqrt 2 ^ q ≤ M₀ := by
      have hs2 : (0 : ℝ) < Real.sqrt 2 ^ q := by
        have : (0 : ℝ) < Real.sqrt 2 := by positivity
        exact Real.rpow_pos_of_pos this _
      rw [div_le_iff₀ hs2]
      nlinarith [hM₀pos.le, hsqrt2]
    linarith [hstep, hb, hM₀le]
  -- the chaining bound, transported back to the rectangle
  have hsup := hM₀ PW hPW Xbox hXboxmeas (fun u' _ v' _ => hintX u' v') hmomX hintX0 hbaseX
    hXboxcont
  refine le_trans (measure_mono_ae ?_) hsup
  filter_upwards [hYae] with ω hω hbad
  have hbad' : ω ∈ {ω | ∀ u ∈ rectSet a b,
      |ballStoppedField d Z PB B s T u ω - ballField d W s u ω| ≤ c}ᶜ := hbad
  show ω ∈ {ω | ∃ u' ∈ Set.Icc a b, c < |Xbox u' ω|}
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hbad'
  obtain ⟨u, hu, hgt⟩ := hbad'
  refine ⟨WithLp.ofLp u, ?_, ?_⟩
  · exact (rectSet_toLp_iff (a := a) (b := b) (WithLp.ofLp u)).mp hu
  · have hval : Xbox (WithLp.ofLp u) ω = D u ω := by
      show Y (WithLp.toLp 2 (WithLp.ofLp u)) ω = D u ω
      rw [hω]
    rw [hval]
    exact lt_of_not_ge hgt

/-! ### The union over the finitely many scales and rectangles -/

/-- **The ball-stopped field approximates the ball field uniformly on the rectangles**:
`Sandpile.Support.BallStoppedApproximation`, the analytic input of
`thm-limiting-odometer-crossing` (`sandpile.tex:2511-2513`). -/
theorem ballStoppedApproximation_of_occupation
    (hOcc : Sandpile.External.BallOccupationDensity) {d : ℕ} (hdd : d = 2 ∨ d = 3) :
    BallStoppedApproximation d := by
  intro k s hs N a b c δ hc hδ
  set ε : ℝ := δ / ((k : ℝ) * (N : ℝ) + 1) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    have : (0 : ℝ) ≤ (k : ℝ) * (N : ℝ) := by positivity
    positivity
  have hscale : ∀ i : Fin k, 0 < ((s i : ℚ) : ℝ) ∧ ((s i : ℚ) : ℝ) ≤ 1 := by
    intro i
    obtain ⟨h1, h2⟩ := hs i
    constructor
    · exact_mod_cast h1
    · have : ((s i : ℚ) : ℝ) < 1 := by exact_mod_cast h2
      linarith
  have hall : ∀ᶠ T : ℝ in atTop, ∀ ij : Fin k × Fin N,
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW),
      IsProbabilityMeasure PW → ∀ (W : (Space d → ℝ) → ΩW → ℝ), IsWhiteNoise d W PW →
      (∀ᵐ ω ∂PW, Continuous fun u : Space 2 => ballField d W ((s ij.1 : ℚ) : ℝ) u ω) →
      ∀ (Z : ℝ → Space d → ΩW → ℝ),
      (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d 1 W t x ω) →
      ContinuousHeatPotential d Z PW →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB), IsProbabilityMeasure PB →
      ∀ (B : Space d → ℝ≥0 → ΩB → Space d), (∀ y, IsBrownian d y (B y) PB) →
      (∀ y ω, Continuous fun t => B y t ω) → (∀ y t, StronglyMeasurable (B y t)) →
      PW {ω | ∀ u ∈ rectSet (a ij.2) (b ij.2),
          |ballStoppedField d Z PB B ((s ij.1 : ℚ) : ℝ) T u ω
            - ballField d W ((s ij.1 : ℚ) : ℝ) u ω| ≤ c}ᶜ
        ≤ ENNReal.ofReal ε := by
    rw [Filter.eventually_all]
    intro ij
    exact eventually_measure_bad_rect_le hOcc hdd (hscale ij.1).1 (hscale ij.1).2 hc hε
      (a ij.2) (b ij.2)
  filter_upwards [hall] with T hT
  intro ΩW _ PW hPW W hW hXc Z hmod hZc ΩB _ PB hPB B hB hBc hBm
  -- the bad event is covered by the finitely many rectangle events
  have hsub : {ω | ∀ (i : Fin k) (u : Space 2), (∃ j, u ∈ rectSet (a j) (b j)) →
      |ballStoppedField d Z PB B ((s i : ℚ) : ℝ) T u ω
        - ballField d W ((s i : ℚ) : ℝ) u ω| ≤ c}ᶜ
      ⊆ ⋃ ij : Fin k × Fin N, {ω | ∀ u ∈ rectSet (a ij.2) (b ij.2),
        |ballStoppedField d Z PB B ((s ij.1 : ℚ) : ℝ) T u ω
          - ballField d W ((s ij.1 : ℚ) : ℝ) u ω| ≤ c}ᶜ := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hω
    push Not at hω
    obtain ⟨i, u, ⟨j, hj⟩, hgt⟩ := hω
    refine Set.mem_iUnion.mpr ⟨(i, j), ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    push Not
    exact ⟨u, hj, hgt⟩
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_iUnion_fintype_le _ _) ?_
  have hbound : ∀ ij : Fin k × Fin N,
      PW {ω | ∀ u ∈ rectSet (a ij.2) (b ij.2),
        |ballStoppedField d Z PB B ((s ij.1 : ℚ) : ℝ) T u ω
          - ballField d W ((s ij.1 : ℚ) : ℝ) u ω| ≤ c}ᶜ ≤ ENNReal.ofReal ε := by
    intro ij
    exact hT ij ΩW PW hPW W hW (hXc _ (hscale ij.1).1 (hscale ij.1).2) Z hmod hZc ΩB PB hPB B hB
      hBc hBm
  refine le_trans (Finset.sum_le_sum fun ij _ => hbound ij) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hεdef]
  have hkn : (0 : ℝ) ≤ (k : ℝ) * (N : ℝ) := by positivity
  have hpos : (0 : ℝ) < (k : ℝ) * (N : ℝ) + 1 := by linarith
  rw [mul_div_assoc'] at *
  rw [div_le_iff₀ hpos]
  push_cast
  nlinarith [hδ.le, hkn]

end Sandpile.Support
