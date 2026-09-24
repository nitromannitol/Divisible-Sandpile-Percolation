/-
Two facts the concrete exploration of Step 2 needs.

**Versions.**  The exploration reads the field through the noise of the cubes it has revealed,
and the white noise is only ALMOST SURELY additive over a decomposition of a test function, so
the field the exploration computes agrees with `ballField` only almost surely at each point.
The crossing event reads the field at countably many points (the rational parameters of the
segments of the countably many admissible chains), so the two crossing events differ by a null
set: `closedCrossEvent_ae_eq_of_field_ae`.  Both the law and every exponential tilt of it, being
mutually absolutely continuous, then give the two events the same measure.

**Mass.**  The shift of Step 3 raises the field by `a𝔪` at a point of the rectangle exactly when
the shifted region contains the support of the unit kernel there (`sandpile.tex:2337-2345`:
"This union is deterministic, and it contains the support of every unit kernel that the
exploration evaluates").  `integral_ballKernel_mul_indicator_of_covers` is that statement, and
`integral_ballKernel_eq_centred` says the resulting mass is the same at every point, so the
level is raised by the same amount everywhere.
-/
import Sandpile.Support.CrossFieldTilt

open MeasureTheory ProbabilityTheory Set
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped NNReal ENNReal

namespace Sandpile.Support

/-! ### Versions of the field -/

theorem pathEvent_ae_eq_of_field_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Space 2 → Ω → ℝ) (h : ∀ u, X u =ᵐ[P] Y u) (l : ℝ) (n : ℕ)
    (v : ℕ → Space 2) : pathEvent X l n v =ᵐ[P] pathEvent Y l n v := by
  have hrw : ∀ Z : Space 2 → Ω → ℝ, pathEvent Z l n v =
      ⋂ (j : ℕ), ⋂ (q : ℚ), {ω | j < n → 0 ≤ q → q ≤ 1 →
        l ≤ Z (segPt (v j) (v (j + 1)) (q : ℝ)) ω} := by
    intro Z
    ext ω
    simp only [pathEvent, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hrw X, hrw Y]
  refine Filter.EventuallyEq.countable_iInter fun j => Filter.EventuallyEq.countable_iInter
    fun q => ?_
  filter_upwards [h (segPt (v j) (v (j + 1)) (q : ℝ))] with ω hω
  simp only [eq_iff_iff]
  show (j < n → 0 ≤ q → q ≤ 1 → l ≤ X (segPt (v j) (v (j + 1)) (q : ℝ)) ω) ↔
      (j < n → 0 ≤ q → q ≤ 1 → l ≤ Y (segPt (v j) (v (j + 1)) (q : ℝ)) ω)
  rw [hω]

theorem crossApprox_ae_eq_of_field_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Space 2 → Ω → ℝ) (h : ∀ u, X u =ᵐ[P] Y u) (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    crossApprox X a b i l =ᵐ[P] crossApprox Y a b i l := by
  unfold crossApprox
  exact Filter.EventuallyEq.countable_iUnion fun ch =>
    pathEvent_ae_eq_of_field_ae P X Y h l _ _

/-- Two fields that agree almost surely at every point have almost surely the same crossings:
the crossing event reads only countably many field values. -/
theorem closedCrossEvent_ae_eq_of_field_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Space 2 → Ω → ℝ) (h : ∀ u, X u =ᵐ[P] Y u) (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    closedCrossEvent X a b i l =ᵐ[P] closedCrossEvent Y a b i l := by
  unfold closedCrossEvent
  exact Filter.EventuallyEq.countable_iInter fun n =>
    crossApprox_ae_eq_of_field_ae P X Y h a b i _

/-- The two events have the same measure under every measure absolutely continuous with respect
to `P`, in particular under every exponential tilt of it. -/
theorem measure_closedCrossEvent_eq_of_field_ae {Ω : Type*} [MeasurableSpace Ω]
    (P μ : Measure Ω) (hμ : μ ≪ P) (X Y : Space 2 → Ω → ℝ) (h : ∀ u, X u =ᵐ[P] Y u)
    (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    μ (closedCrossEvent X a b i l) = μ (closedCrossEvent Y a b i l) :=
  measure_congr (hμ.ae_eq (closedCrossEvent_ae_eq_of_field_ae P X Y h a b i l))

/-! ### The mass of the unit kernel on the shifted region -/

/-- Outside the unit ball about `u` the unit kernel vanishes. -/
theorem ballKernel_eq_zero_of_one_le {d : ℕ} (u : Space 2) {z : Space d}
    (hz : 1 ≤ ‖(planePoint (d := d) u) - z‖) : ballKernel d 1 u z = 0 := by
  unfold ballKernel
  rw [if_neg (not_lt.mpr hz)]

/-- **The shift raises the field by the full mass of the kernel.**  If the region `U` contains
the unit ball about `u`, the unit kernel at `u` pairs with the indicator of `U` to its full
mass. -/
theorem integral_ballKernel_mul_indicator_of_covers {d : ℕ} (u : Space 2) (U : Set (Space d))
    (hU : ∀ z : Space d, ‖(planePoint (d := d) u) - z‖ < 1 → z ∈ U) :
    (∫ y : Space d, ballKernel d 1 u y * Set.indicator U (fun _ => (1 : ℝ)) y)
      = ∫ y : Space d, ballKernel d 1 u y := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ballKernel d 1 u y * Set.indicator U (fun _ => (1 : ℝ)) y = ballKernel d 1 u y
  by_cases hy : y ∈ U
  · rw [Set.indicator_of_mem hy]
    ring
  · have hnot : ¬ ‖(planePoint (d := d) u) - y‖ < 1 := fun hlt => hy (hU y hlt)
    rw [ballKernel_eq_zero_of_one_le u (not_lt.mp hnot)]
    ring

/-- The mass of the unit kernel does not depend on the point: the shift raises the field by the
same amount everywhere. -/
theorem integral_ballKernel_eq_centred (d : ℕ) (u : Space 2) :
    (∫ y : Space d, ballKernel d 1 u y) = ∫ y : Space d, centredKernel d 1 y := by
  rw [ballKernel_eq_centredKernel]
  have hmp : MeasurePreserving
      (fun z : Space d => planePoint (d := d) u - z) volume volume :=
    Measure.measurePreserving_sub_left volume _
  exact hmp.integral_comp (MeasurableEquiv.subLeft (planePoint (d := d) u)).measurableEmbedding _



/-! ### The mass of the unit kernel is positive

`sandpile.tex:2090-2100` records the mass as `𝔪 = 1/4` in dimension two and `𝔪 = 1/6` in
dimension three; only its positivity is used, and that is what is proved here.  The kernel is
nonnegative away from the origin, where in dimension three the reciprocal `1/‖y‖` takes the
junk value `0` and the kernel is negative; the origin is a null set, so the integral is
unaffected. -/

theorem centredKernel_eq_zero_of_one_le {d : ℕ} {y : Space d} (hy : 1 ≤ ‖y‖) :
    centredKernel d 1 y = 0 := by
  unfold centredKernel
  rw [if_neg (not_lt.mpr hy)]

theorem centredKernel_pos_of_lt_one {d : ℕ} {y : Space d} (hy : y ≠ 0) (h1 : ‖y‖ < 1) :
    0 < centredKernel d 1 y := by
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hinv : 1 < 1 / ‖y‖ := by
    rw [lt_div_iff₀ hpos]
    linarith
  unfold centredKernel
  rw [if_pos h1]
  by_cases hd2 : d = 2
  · rw [if_pos hd2]
    have hlog : 0 < Real.log (1 / ‖y‖) := Real.log_pos hinv
    have hpi : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
    exact mul_pos hpi hlog
  · rw [if_neg hd2]
    have hpi : (0 : ℝ) < 1 / (4 * Real.pi) := by positivity
    have hgap : 0 < 1 / ‖y‖ - 1 / (1 : ℝ) := by
      rw [div_one]
      linarith
    exact mul_pos hpi hgap

theorem centredKernel_nonneg_of_ne_zero {d : ℕ} {y : Space d} (hy : y ≠ 0) :
    0 ≤ centredKernel d 1 y := by
  by_cases h1 : ‖y‖ < 1
  · exact (centredKernel_pos_of_lt_one hy h1).le
  · rw [centredKernel_eq_zero_of_one_le (not_lt.mp h1)]

theorem integrable_centredKernel {d : ℕ} (hd : d = 2 ∨ d = 3) :
    Integrable (centredKernel d 1) (volume : Measure (Space d)) := by
  have hmem : MemLp (centredKernel d 1) 2 (volume : Measure (Space d)) :=
    memLp_centredKernel hd one_pos
  have hzero : ∀ y : Space d, y ∉ Metric.ball (0 : Space d) 1 → centredKernel d 1 y = 0 := by
    intro y hy
    have h1 : (1 : ℝ) ≤ ‖y‖ := by
      simpa [Metric.mem_ball, dist_zero_right] using hy
    exact centredKernel_eq_zero_of_one_le h1
  have hfin : volume (Metric.ball (0 : Space d) 1) ≠ ⊤ := measure_ball_lt_top.ne
  exact memLp_one_iff_integrable.mp
    (hmem.mono_exponent_of_measure_support_ne_top hzero hfin (by norm_num))

/-- **The mass of the unit kernel is positive** (`sandpile.tex:2090-2100`). -/
theorem centredKernel_mass_pos {d : ℕ} (hd : d = 2 ∨ d = 3) :
    0 < ∫ y : Space d, centredKernel d 1 y := by
  have hd1 : Nontrivial (Space d) := by
    rcases hd with rfl | rfl <;> infer_instance
  have hsingle : volume ({(0 : Space d)}) = 0 := measure_singleton _
  have hnn : 0 ≤ᵐ[(volume : Measure (Space d))] centredKernel d 1 := by
    have hae : ∀ᵐ y : Space d ∂volume, y ∉ ({(0 : Space d)} : Set (Space d)) := by
      rw [ae_iff]
      simp [hsingle]
    filter_upwards [hae] with y hy
    exact centredKernel_nonneg_of_ne_zero (by simp at hy; exact hy)
  rw [integral_pos_iff_support_of_nonneg_ae hnn (integrable_centredKernel hd)]
  have hsub : Metric.ball (0 : Space d) 1 \ {0} ⊆ Function.support (centredKernel d 1) := by
    rintro y ⟨hball, hne⟩
    have h1 : ‖y‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hball
    exact ne_of_gt (centredKernel_pos_of_lt_one (by simpa using hne) h1)
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [measure_sdiff_null hsingle]
  exact Metric.measure_ball_pos _ _ one_pos

end Sandpile.Support
