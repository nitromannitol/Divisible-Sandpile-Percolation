import Sandpile.Support.CrossFieldSym
import Sandpile.External.ContinuumRSW

/-!
# Step 1: the uniform aspect-`θ` crossing constant

Step 1 of `prop:fixed-scale-crossings` (`sandpile.tex:2230-2240`):

  "By sign symmetry and rotation invariance, `P(H_{[-R,R]²}(0)) ≥ 1/2`
   uniformly in `R ≥ 1`.  The continuum form of the RSW theorem, applied to the
   positively associated process `{𝒳_1 ≥ 0}`, then gives, for each `θ > 0`, a
   `c_0 > 0` such that for every `R ≥ 1`,
   `P(H_{[-θR,θR]×[0,2R]}(0)) ≥ c_0`."

The square estimate is the hypothesis `hsq` below, in the form the field carries
it: the crossing probability of an arbitrary square of side at least one, for
the field read at a translated point, which is the same subset of the
probability space as the crossing of the translated square.  It is what
continuum duality and the sign symmetry of the field give, and it is the one
input of this step that is not the RSW comparison itself.

From it the aspect-`θ` estimate is obtained in two ways.  For `θ ≤ 1` the
rectangle is at least as tall as it is wide, so it contains a square with the
same left and right sides and no RSW is needed.  For `θ > 1` the rectangle is
wide, and the continuum RSW comparison of `External.ContinuumRSW` turns the easy
crossing of the tall rectangle `[0,2R]×[0,2θR]`, which again contains a square
with the same left and right sides, into the hard crossing of `[0,2θR]×[0,2R]`.

Both are read on the rectangle `[-θR,θR]×[0,2R]` the proposition asks about
through `crossingSet_translate`: a crossing of a translated rectangle by the
field is the same subset of the probability space as a crossing of the
rectangle by the translated field.  The comparison is therefore made between
outer measures of one and the same set, which is what makes the step legitimate
for an event that is not known to be measurable.  The translated field inherits
the symmetry and association hypotheses of `External.ContinuumRSW`
(`isSymmetricField_translate`, `isAssociatedField_translate`).
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- An order isomorphism of the unit interval is positive at a positive point. -/
theorem orderIso_pos (ψ : Set.Icc (0 : ℝ) 1 ≃o Set.Icc (0 : ℝ) 1)
    (x : Set.Icc (0 : ℝ) 1) (hx : 0 < (x : ℝ)) : 0 < (ψ x : ℝ) := by
  have hz : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) < x := by
    exact Subtype.coe_lt_coe.mp (by simpa using hx)
  have hψ : ψ ⟨0, by norm_num⟩ < ψ x := ψ.lt_iff_lt.mpr hz
  have h0 : (0 : ℝ) ≤ (ψ ⟨0, by norm_num⟩ : ℝ) := (ψ ⟨0, by norm_num⟩).2.1
  have h1 : ((ψ ⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) : ℝ) < ((ψ x : Set.Icc (0 : ℝ) 1) : ℝ) :=
    hψ
  linarith

/-- The translation that moves the origin-anchored rectangle `[0,2θR]×[0,2R]` to
the centred rectangle `[-θR,θR]×[0,2R]`. -/
noncomputable def centreShift (w : ℝ) : Sandpile.Continuum.Space 2 :=
  WithLp.toLp 2 ![-w, 0]

/-- The first coordinate of `centreShift w` is `-w`. -/
theorem centreShift_apply_zero (w : ℝ) : (centreShift w) 0 = -w := rfl

/-- The second coordinate of `centreShift w` is `0`. -/
theorem centreShift_apply_one (w : ℝ) : (centreShift w) 1 = 0 := rfl

/-- A real lower bound for `P.real` is a lower bound for the measure itself. -/
theorem ofReal_le_measure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {A : Set Ω} {c : ℝ} (h : c ≤ μ.real A) :
    ENNReal.ofReal c ≤ μ A := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ A)]
  exact ENNReal.ofReal_le_ofReal h

/-- The crossing of the centred rectangle by the field is the crossing of the
origin-anchored rectangle by the translated field. -/
theorem crossingSet_centre {Ω : Type*} (X : Sandpile.Continuum.Space 2 → Ω → ℝ)
    (w h l : ℝ) :
    {ω | Crosses ![-w, 0] ![w, h] 0 {u | l ≤ X u ω}}
      = {ω | Crosses ![0, 0] ![2 * w, h] 0 {u | l ≤ X (u + centreShift w) ω}} := by
  have hA : (fun k => (![(0 : ℝ), 0]) k + (centreShift w) k) = ![-w, 0] := by
    funext k
    fin_cases k <;> simp [centreShift_apply_zero, centreShift_apply_one]
  have hB : (fun k => (![2 * w, h]) k + (centreShift w) k) = ![w, h] := by
    funext k
    fin_cases k
    · show 2 * w + (centreShift w) 0 = w
      rw [centreShift_apply_zero]; ring
    · show h + (centreShift w) 1 = h
      rw [centreShift_apply_one]; ring
  have := crossingSet_translate X (centreShift w) ![0, 0] ![2 * w, h] 0 l
  rw [hA, hB] at this
  exact this

/-- A rectangle contains the square on its base when it is at least as tall as
it is wide, and the square has the same left and right sides. -/
theorem crossingSet_square_subset {Ω : Type*} (X : Sandpile.Continuum.Space 2 → Ω → ℝ)
    {w h l : ℝ} (hwh : 2 * w ≤ h) :
    {ω | Crosses ![0, 0] ![2 * w, 2 * w] 0 {u | l ≤ X u ω}}
      ⊆ {ω | Crosses ![0, 0] ![2 * w, h] 0 {u | l ≤ X u ω}} := by
  intro ω hω
  have hω' : Crosses ![0, 0] ![2 * w, 2 * w] 0 {u | l ≤ X u ω} := hω
  show Crosses ![0, 0] ![2 * w, h] 0 {u | l ≤ X u ω}
  refine crosses_rect_mono (a' := ![0, 0]) (b' := ![2 * w, 2 * w])
    (rectSet_mono (fun k => le_refl _) ?_) rfl rfl hω'
  intro k
  fin_cases k
  · exact le_refl _
  · exact hwh

/-- Step 1 of `sandpile.tex:2230-2240` with the constant bound where the paper
binds it: `c` depends on `θ` alone, before the probability space carrying the
field.  In the wide case it is the value of the RSW comparison map of
`External.ContinuumRSW` at one half, and that map is chosen from the aspect
ratio alone; in the tall case it is one half.  This is what lets
`prop:fixed-scale-crossings` quantify `p` before the space, as the paper does.

The square estimate is the hypothesis `hsq`, in the form the field carries it:
the crossing probability of an arbitrary square of side at least one, for the
field read at a translated point, which is the same subset of the probability
space as the crossing of the translated square.  For `θ ≤ 1` the rectangle is at
least as tall as it is wide, so it contains a square with the same left and
right sides and no RSW is needed; for `θ > 1` the continuum RSW comparison turns
the easy crossing of the tall rectangle into the hard crossing of the wide one.
-/
theorem uniform_crossing_constant
    (hRSW : Sandpile.External.ContinuumRSW) (θ : ℝ) (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Sandpile.Continuum.Space 2 → Ω → ℝ), (∀ u, Measurable (X u)) →
        (∀ᵐ ω ∂P, Continuous fun u => X u ω) →
        Sandpile.Continuum.IsSymmetricField P X →
        Sandpile.Continuum.IsAssociatedField P X →
        ∀ lev : ℝ,
        (∀ (v : Sandpile.Continuum.Space 2) (s : ℝ), 1 ≤ s →
          (1 : ℝ) / 2 ≤ P.real {ω |
            Crosses ![0, 0] ![2 * s, 2 * s] 0 {u | lev ≤ X (u + v) ω}}) →
        ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
          ENNReal.ofReal c ≤
            P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | lev ≤ X u ω}} := by
  rcases le_or_gt θ 1 with hθ1 | hθ1
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro Ω _ P _ X hmeas hcont hsym hass lev hsq R hR
    have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
    have hRinv : θ⁻¹ ≤ R := le_trans (le_max_right _ _) hR
    have hθR : (1 : ℝ) ≤ θ * R := by
      have h := mul_le_mul_of_nonneg_left hRinv hθ.le
      rwa [mul_inv_cancel₀ hθ.ne'] at h
    have hle : 2 * (θ * R) ≤ 2 * R := by nlinarith
    rw [crossingSet_centre X (θ * R) (2 * R) lev]
    refine le_trans (ofReal_le_measure P (hsq (centreShift (θ * R)) (θ * R) hθR)) ?_
    exact measure_mono (crossingSet_square_subset (fun u ω => X (u + centreShift (θ * R)) ω) hle)
  · obtain ⟨ψ, hψ⟩ := hRSW θ hθ1.le
    refine ⟨(ψ ⟨1 / 2, by norm_num⟩ : ℝ), orderIso_pos ψ _ (by norm_num), ?_⟩
    intro Ω _ P _ X hmeas hcont hsym hass lev hsq R hR
    have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
    have hcontY : ∀ᵐ ω ∂P, Continuous fun u => X (u + centreShift (θ * R)) ω := by
      filter_upwards [hcont] with ω hω
      exact hω.comp (continuous_id.add continuous_const)
    have hhalf : (1 : ℝ) / 2 ≤ P.real {ω |
        Crosses ![0, 0] ![2 * R, 2 * θ * R] 0
          {u | lev ≤ X (u + centreShift (θ * R)) ω}} := by
      have hsub := crossingSet_square_subset (fun u ω => X (u + centreShift (θ * R)) ω)
        (w := R) (h := 2 * θ * R) (l := lev) (by nlinarith)
      refine le_trans (hsq (centreShift (θ * R)) R hR1) ?_
      exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
    have hmono : (ψ ⟨1 / 2, by norm_num⟩ : ℝ) ≤
        (ψ (Sandpile.probabilityInUnitInterval P {ω |
          Crosses ![0, 0] ![2 * R, 2 * θ * R] 0
            {u | lev ≤ X (u + centreShift (θ * R)) ω}}) : ℝ) := by
      have hle : (⟨1 / 2, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ≤
          Sandpile.probabilityInUnitInterval P {ω |
            Crosses ![0, 0] ![2 * R, 2 * θ * R] 0
              {u | lev ≤ X (u + centreShift (θ * R)) ω}} := hhalf
      exact ψ.monotone hle
    have hrsw := hψ Ω P (fun u ω => X (u + centreShift (θ * R)) ω)
      (fun u => hmeas _) hcontY
      (Sandpile.Continuum.isSymmetricField_translate hsym (centreShift (θ * R)))
      (Sandpile.Continuum.isAssociatedField_translate hass (centreShift (θ * R))) R hR1 lev
    have hkey : (ψ ⟨1 / 2, by norm_num⟩ : ℝ) ≤ P.real {ω |
        Crosses ![0, 0] ![2 * θ * R, 2 * R] 0
          {u | lev ≤ X (u + centreShift (θ * R)) ω}} := le_trans hmono hrsw
    rw [crossingSet_centre X (θ * R) (2 * R) lev]
    have hrw : (2 : ℝ) * (θ * R) = 2 * θ * R := by ring
    rw [hrw]
    exact ofReal_le_measure P hkey

/-- The same bound for one field, in the form the assembly used before the
constant was hoisted. -/
theorem crossing_level_of_square
    (hRSW : Sandpile.External.ContinuumRSW) (θ : ℝ) (hθ : 0 < θ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (hmeas : ∀ u, Measurable (X u))
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω)
    (hsym : Sandpile.Continuum.IsSymmetricField P X)
    (hass : Sandpile.Continuum.IsAssociatedField P X)
    (lev : ℝ)
    (hsq : ∀ (v : Sandpile.Continuum.Space 2) (s : ℝ), 1 ≤ s →
      (1 : ℝ) / 2 ≤ P.real {ω |
        Crosses ![0, 0] ![2 * s, 2 * s] 0 {u | lev ≤ X (u + v) ω}}) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
      ENNReal.ofReal c ≤
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | lev ≤ X u ω}} := by
  obtain ⟨c, hc, h⟩ := uniform_crossing_constant hRSW θ hθ
  exact ⟨c, hc, h Ω P X hmeas hcont hsym hass lev hsq⟩

end Sandpile.Support
