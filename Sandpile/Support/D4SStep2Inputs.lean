import Sandpile.Support.D4SmoothL2
import Sandpile.Support.D4L2Error
import Sandpile.Support.Smoothed

/-!
# The inputs of Step 2: the centred linearization error and its crude total-variation bound

Step 2 of `prop:d4-superdiffusive-limit` (`sandpile.tex:3368-3382`) smooths the centred
linearization error `E_m = u_m - \E u_m(0) - V_m` of `prop:d4-pointwise-linearization`
(`linError`). Two things are recorded here. The first is the crude total variation bound
`∑_y|p_n(x,y)-p_n(b,y)| ≤ 2`, valid for ANY two sites (`tsum_abs_heatKernel_sub_le_two`), and its
consequence for second moments (`integral_sq_smoothing_increment_le_four`): this is what the
second display of Step 2 needs, since its two base points `0` and `e_1` lie in different parity
classes, so the gradient bound of `eq:rw-tv-gradient` does not apply and only the trivial bound is
available. The second is the identification of the smoothed centred error with the paper's `F_R`
(`avg_iterate_linError`), together with its uniform second moment
(`exists_linError_second_moment`).
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- **The total variation of two heat kernels is at most two.**  Unlike
`eq:rw-tv-gradient` this needs no parity relation between the two sites. -/
theorem tsum_abs_heatKernel_sub_le_two (hd : 1 ≤ d) (n : ℕ) (x b : Site d) :
    ∑' y : Site d, |heatKernel d n x y - heatKernel d n b y| ≤ 2 := by
  classical
  set S : Finset (Site d) := Sandpile.boxFinset x n ∪ Sandpile.boxFinset b n with hS
  have hzero : ∀ y : Site d, y ∉ S → |heatKernel d n x y - heatKernel d n b y| = 0 := by
    intro y hy
    rw [Finset.mem_union, not_or] at hy
    have h1 : heatKernel d n x y = 0 := by
      by_contra hne
      exact hy.1 (Sandpile.mem_boxFinset (Sandpile.heatKernel_support n x hne))
    have h2 : heatKernel d n b y = 0 := by
      by_contra hne
      exact hy.2 (Sandpile.mem_boxFinset (Sandpile.heatKernel_support n b hne))
    rw [h1, h2]; simp
  rw [tsum_eq_sum (s := S) hzero]
  have hbound : ∀ y ∈ S, |heatKernel d n x y - heatKernel d n b y|
      ≤ heatKernel d n x y + heatKernel d n b y := by
    intro y _
    have h1 := Sandpile.heatKernel_nonneg n x y
    have h2 := Sandpile.heatKernel_nonneg n b y
    rw [abs_le]
    constructor <;> linarith
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_add_distrib]
  have hx : ∑ y ∈ S, heatKernel d n x y ≤ 1 := by
    have heq : ∑ y ∈ S, heatKernel d n x y
        = ∑ y ∈ Sandpile.boxFinset x n, heatKernel d n x y :=
      (Finset.sum_subset (fun y hy => by
          rw [hS]; exact Finset.mem_union.mpr (Or.inl hy))
        (fun y _ hybox => by
          by_contra hne
          exact hybox (Sandpile.mem_boxFinset (Sandpile.heatKernel_support n x hne)))).symm
    rw [heq]
    exact le_of_eq (Sandpile.sum_heatKernel_boxFinset hd n x)
  have hb : ∑ y ∈ S, heatKernel d n b y ≤ 1 := by
    have heq : ∑ y ∈ S, heatKernel d n b y
        = ∑ y ∈ Sandpile.boxFinset b n, heatKernel d n b y :=
      (Finset.sum_subset (fun y hy => by
          rw [hS]; exact Finset.mem_union.mpr (Or.inr hy))
        (fun y _ hybox => by
          by_contra hne
          exact hybox (Sandpile.mem_boxFinset (Sandpile.heatKernel_support n b hne)))).symm
    rw [heq]
    exact le_of_eq (Sandpile.sum_heatKernel_boxFinset hd n b)
  linarith

/-- **The crude second moment of a smoothed increment**, without a parity
relation: `E(P^nX(x)-P^nX(b))² ≤ 4V`.  This is what bounds the paper's
`|F_R(0)-F_R(e_1)|`, whose two base points have opposite parity. -/
theorem integral_sq_smoothing_increment_le_four (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Site d → ℝ) (n : ℕ) (x b : Site d) (V : ℝ)
    (hint : ∀ z : Site d, Integrable (fun ω => (X ω z) ^ 2) P)
    (hV : ∀ z : Site d, ∫ ω, (X ω z) ^ 2 ∂P ≤ V) :
    ∫ ω, ((avg^[n] (X ω)) x - (avg^[n] (X ω)) b) ^ 2 ∂P ≤ 4 * V := by
  have hV0 : (0 : ℝ) ≤ V := le_trans (integral_nonneg fun ω => sq_nonneg _) (hV x)
  refine le_trans (Sandpile.integral_sq_smoothing_increment_le P X n x b V hint hV) ?_
  have htv := tsum_abs_heatKernel_sub_le_two hd n x b
  have htv0 : (0:ℝ) ≤ ∑' y : Site d, |heatKernel d n x y - heatKernel d n b y| :=
    tsum_nonneg fun y => abs_nonneg _
  have hsq : (∑' y : Site d, |heatKernel d n x y - heatKernel d n b y|) ^ 2 ≤ 4 := by
    nlinarith
  nlinarith

/-- The centred linearization error `E_m = u_m - \E u_m(0) - V_m`, the field
Step 2 smooths (`sandpile.tex:3368-3372`). -/
noncomputable def linError (ν : Measure ℝ) (m : ℕ) (ζ : Site 4 → ℝ) (z : Site 4) : ℝ :=
  diffField ζ m z - ∫ η, odometerOf η m 0 ∂(LatticeProb.iidLaw 4 ν)

/-- Unfolds `linError` via `diffField = odometerOf - membrane`. -/
theorem linError_eq (ν : Measure ℝ) (m : ℕ) (ζ : Site 4 → ℝ) (z : Site 4) :
    linError ν m ζ z =
      odometerOf ζ m z - (∫ η, odometerOf η m 0 ∂(LatticeProb.iidLaw 4 ν)) -
        membrane ζ m z := by
  show odometerOf ζ m z - membrane ζ m z - _ = _
  ring

/-- `linError ν m · z` is measurable, as a difference of the measurable odometer and membrane
fields and a constant. -/
theorem measurable_linError (ν : Measure ℝ) (m : ℕ) (z : Site 4) :
    Measurable (fun ζ : Site 4 → ℝ => linError ν m ζ z) := by
  have h : (fun ζ : Site 4 → ℝ => linError ν m ζ z) =
      fun ζ => odometerOf ζ m z - (∫ η, odometerOf η m 0 ∂(LatticeProb.iidLaw 4 ν)) -
        membrane ζ m z := by
    funext ζ; exact linError_eq ν m ζ z
  rw [h]
  exact ((measurable_odometerOf m z).sub measurable_const).sub (measurable_membrane m z)

/-- **The smoothed centred error is the paper's `F_R`.**  The smoothing operator
fixes constants, so subtracting `\E u_m(0)` before or after smoothing is the
same. -/
theorem avg_iterate_linError (ν : Measure ℝ) (m n : ℕ) (ζ : Site 4 → ℝ) (x : Site 4) :
    (avg^[n] (linError ν m ζ)) x =
      (avg^[n] (diffField ζ m)) x - ∫ η, odometerOf η m 0 ∂(LatticeProb.iidLaw 4 ν) :=
  avg_iterate_sub_const (by norm_num) n (diffField ζ m) _ x

/-- **The uniform second moment of the centred error**
(`prop:d4-pointwise-linearization`, `sandpile.tex:3372`). -/
theorem exists_linError_second_moment (hVS : External.VarianceScale)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m : ℕ, 3 ≤ m → ∀ z : Site 4,
      Integrable (fun ζ => (linError ν m ζ z) ^ 2) (LatticeProb.iidLaw 4 ν) ∧
      (∫ ζ, (linError ν m ζ z) ^ 2 ∂(LatticeProb.iidLaw 4 ν)) ≤
        (1 + Real.log (Real.log m)) ^ 2 + M := by
  obtain ⟨M, hM, hb⟩ := exists_linearization_second_moment_four hVS ν hmean θ hθ hexp
  refine ⟨M, hM, fun m hm z => ?_⟩
  obtain ⟨h1, h2⟩ := hb m hm z
  have hcongr : (fun ζ : Site 4 → ℝ => (linError ν m ζ z) ^ 2) =
      fun ζ => (odometerOf ζ m z - (∫ η, odometerOf η m 0 ∂(LatticeProb.iidLaw 4 ν)) -
        membrane ζ m z) ^ 2 := by
    funext ζ; rw [linError_eq ν m ζ z]
  rw [hcongr]
  exact ⟨h1, h2⟩

end Sandpile
