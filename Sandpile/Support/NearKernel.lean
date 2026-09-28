import Sandpile.Support.FiniteKernelTail
import Sandpile.Support.BallCrossingDefinitions

/-!
# Near-field kernel: support, bounds, and the near-far decomposition

Defines the near-field kernel `nearKernel r L φ`, the difference between the killed Green's
function on `External.BallGreen.box r` and its smooth cutoff `External.BallGreen.cutField r L φ`.
Establishes that both are finitely supported on `boxFinset 0 r` (hence `ℓ²`-summable), that
`nearKernel` vanishes once the cutoff has fully engaged past distance `2 * L`, gives a uniform
pointwise bound and a logarithmic `ℓ²` bound on `nearKernel` from `External.BallGreenBounds`,
and proves the exact near-far decomposition of the dimension-four ball Green field into a
`cutField` part and a `nearKernel` part.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace Sandpile

/-- `killedGreen (External.BallGreen.box r) 0 u` vanishes when `u` lies outside `boxFinset 0 r`,
since such a `u` is not in the killed box's target set. -/
lemma killedGreen_box_eq_zero_of_notMem_boxFinset (r : ℕ) {u : Site 4}
    (hu : u ∉ boxFinset 0 r) : killedGreen (External.BallGreen.box r) 0 u = 0 := by
  apply killedGreen_eq_zero_of_target_notMem
  intro hb
  apply hu
  apply mem_boxFinset
  apply Finset.sup_le
  intro i _
  simpa only [Pi.zero_apply, zero_sub, Int.natAbs_neg] using hb i

/-- The squares `killedGreen (External.BallGreen.box r) 0 u ^ 2` form a summable family over
`u : Site 4`, because the terms vanish outside the finite set `boxFinset 0 r`. -/
lemma summable_killedGreen_box_sq (r : ℕ) :
    Summable (fun u : Site 4 => killedGreen (External.BallGreen.box r) 0 u ^ 2) := by
  apply summable_of_ne_finset_zero (s := boxFinset 0 r)
  intro u hu
  rw [killedGreen_box_eq_zero_of_notMem_boxFinset r hu, zero_pow (by decide : 2 ≠ 0)]

/-- The near-field kernel at scale `(r, L)`: the killed Green's function on `box r` minus its
smooth cutoff tail `External.BallGreen.cutField r L φ`, isolating the part of the ball Green
field that the cutoff `φ` does not yet suppress. -/
def nearKernel (r L : ℕ) (φ : ℝ → ℝ) (u : Site 4) : ℝ :=
  killedGreen (External.BallGreen.box r) 0 u - External.BallGreen.cutField r L φ u

/-- `nearKernel r L φ u` factors as `killedGreen (External.BallGreen.box r) 0 u` times
`1 - φ (External.BallGreen.latticeNorm u / L)`, by unfolding `nearKernel` and `cutField` and
simplifying with `ring`. -/
lemma nearKernel_eq_mul (r L : ℕ) (φ : ℝ → ℝ) (u : Site 4) :
    nearKernel r L φ u = killedGreen (External.BallGreen.box r) 0 u *
      (1 - φ (External.BallGreen.latticeNorm u / (L : ℝ))) := by
  simp only [nearKernel, External.BallGreen.cutField]
  ring

/-- For a cutoff `φ` satisfying `External.BallGreen.IsCutoff`, `nearKernel r L φ u` lies between
`0` and `killedGreen (External.BallGreen.box r) 0 u`, since the factor
`1 - φ (‖u‖ / L)` from `nearKernel_eq_mul` lies in `[0, 1]`. -/
lemma nearKernel_nonneg_le (r L : ℕ) {φ : ℝ → ℝ} (hφ : External.BallGreen.IsCutoff φ) (u : Site 4) :
    0 ≤ nearKernel r L φ u ∧ nearKernel r L φ u ≤ killedGreen (External.BallGreen.box r) 0 u := by
  have hg : 0 ≤ killedGreen (External.BallGreen.box r) 0 u :=
    tsum_nonneg (fun n => killedKernel_nonneg _ n _ _)
  have hc := hφ.1 (External.BallGreen.latticeNorm u / (L : ℝ))
    (div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
  rw [nearKernel_eq_mul]
  constructor
  · exact mul_nonneg hg (sub_nonneg.mpr hc.2)
  · nlinarith [mul_nonneg hg hc.1]

/-- `nearKernel r L φ u = 0` outside `boxFinset 0 r`, since both `killedGreen` and
`External.BallGreen.cutField` vanish there. -/
lemma nearKernel_eq_zero_of_notMem_boxFinset (r L : ℕ) (φ : ℝ → ℝ) {u : Site 4}
    (hu : u ∉ boxFinset 0 r) : nearKernel r L φ u = 0 := by
  rw [nearKernel, killedGreen_box_eq_zero_of_notMem_boxFinset r hu,
    cutField_eq_zero_of_notMem_boxFinset r L φ hu, sub_self]

/-- `nearKernel r L φ u = 0` once `2 * L ≤ External.BallGreen.latticeNorm u`, because a cutoff
`φ` has already reached its second threshold there, forcing the factor `1 - φ (‖u‖ / L)` from
`nearKernel_eq_mul` to vanish. -/
lemma nearKernel_eq_zero_of_two_mul_le (r L : ℕ) (hL : 0 < L)
    {φ : ℝ → ℝ} (hφ : External.BallGreen.IsCutoff φ) {u : Site 4}
    (hu : 2 * (L : ℝ) ≤ External.BallGreen.latticeNorm u) : nearKernel r L φ u = 0 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  rw [nearKernel_eq_mul, hφ.2.2.2 _ ((le_div_iff₀ hLpos).mpr hu), sub_self, mul_zero]

/-- The squares `nearKernel r L φ u ^ 2` form a summable family over `u : Site 4`, because the
terms vanish outside the finite set `boxFinset 0 r`. -/
lemma summable_nearKernel_sq (r L : ℕ) (φ : ℝ → ℝ) :
    Summable (fun u : Site 4 => nearKernel r L φ u ^ 2) := by
  apply summable_of_ne_finset_zero (s := boxFinset 0 r)
  intro u hu
  rw [nearKernel_eq_zero_of_notMem_boxFinset r L φ hu, zero_pow (by decide : 2 ≠ 0)]

/-- `nearKernel r L φ u = 0` outside `boxFinset 0 (2 * L)`: any such `u` has sup-norm exceeding
`2 * L`, hence `External.BallGreen.latticeNorm u ≥ 2 * L`, so `nearKernel_eq_zero_of_two_mul_le`
applies. -/
lemma nearKernel_eq_zero_of_notMem_near_box (r L : ℕ) (hL : 0 < L)
    {φ : ℝ → ℝ} (hφ : External.BallGreen.IsCutoff φ) {u : Site 4}
    (hu : u ∉ boxFinset 0 (2 * L)) : nearKernel r L φ u = 0 := by
  apply nearKernel_eq_zero_of_two_mul_le r L hL hφ
  by_contra hh
  apply hu
  apply mem_boxFinset
  apply Finset.sup_le
  intro i _
  have hi : |(u i : ℝ)| ≤ (2 * L : ℕ) := by
    exact (ballNorm_coord u i).trans (by push_cast; linarith)
  simpa only [Pi.zero_apply, zero_sub, Int.natAbs_neg] using
    (show (u i).natAbs ≤ 2 * L by
      exact_mod_cast (by simpa only [natAbs_cast_real] using hi : ((u i).natAbs : ℝ) ≤ (2 * L : ℕ)))

/-- Given `External.BallGreenBounds`, produces a uniform constant `G > 0` such that for all
`r, L ≥ 2` and cutoffs `φ`, `nearKernel r L φ` is bounded pointwise by `G` and its squared
`ℓ²`-sum over `Site 4` is at most `G * log (2 * L + 2)`. -/
lemma nearKernel_coefficients (hBall : External.BallGreenBounds) :
    ∃ G > 0, ∀ r L : ℕ, 2 ≤ r → 2 ≤ L → ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
      (∀ u, |nearKernel r L φ u| ≤ G) ∧
      (∑' u : Site 4, nearKernel r L φ u ^ 2) ≤ G * Real.log (2 * (L : ℝ) + 2) := by
  obtain ⟨G, g, hG, _, hb⟩ := hBall
  refine ⟨G, hG, ?_⟩
  intro r L hr hL φ hφ
  have hLpos : 0 < L := by omega
  have hnear (u : Site 4) := nearKernel_nonneg_le r L hφ u
  constructor
  · intro u
    rw [abs_of_nonneg (hnear u).1]
    have hn : 0 ≤ External.BallGreen.latticeNorm u := Real.sqrt_nonneg _
    calc
      _ ≤ killedGreen (External.BallGreen.box r) 0 u := (hnear u).2
      _ ≤ green 4 0 u := ((hb r hr).1 u).2.1
      _ ≤ G / (1 + External.BallGreen.latticeNorm u) ^ 2 := ((hb r hr).1 u).2.2
      _ ≤ G := div_le_self hG.le (by nlinarith)
  · have hsupp : Function.support (fun u : Site 4 => nearKernel r L φ u ^ 2) ⊆
        {u | External.BallGreen.latticeNorm u ≤ 2 * (L : ℝ)} := by
      intro u hu
      by_contra hout
      have he := nearKernel_eq_zero_of_two_mul_le r L hLpos hφ (le_of_lt (lt_of_not_ge hout))
      exact hu (by change nearKernel r L φ u ^ 2 = 0; rw [he, zero_pow (by decide : 2 ≠ 0)])
    calc
      _ = ∑' u : {u : Site 4 // External.BallGreen.latticeNorm u ≤ 2 * (L : ℝ)},
          nearKernel r L φ u ^ 2 := (tsum_subtype_eq_of_support_subset hsupp).symm
      _ ≤ ∑' u : {u : Site 4 // External.BallGreen.latticeNorm u ≤ 2 * (L : ℝ)},
          killedGreen (External.BallGreen.box r) 0 u ^ 2 := by
        refine Summable.tsum_le_tsum ?_ ((summable_nearKernel_sq r L φ).subtype _)
          ((summable_killedGreen_box_sq r).subtype _)
        intro u
        exact (sq_le_sq₀ (hnear u).1
          (tsum_nonneg (fun n => killedKernel_nonneg _ n _ _))).mpr (hnear u).2
      _ ≤ _ := (hb r hr).2.2.1 L hL

/-- The ball cube `ballCube 0 (r : ℝ)` centered at `0` coincides with `External.BallGreen.box r`,
matching the real coordinate bound `|u i| ≤ r` against the integer bound `(u i).natAbs ≤ r`. -/
lemma ballCube_zero_eq_box (r : ℕ) : ballCube 0 (r : ℝ) = External.BallGreen.box r := by
  ext u
  simp only [ballCube, External.BallGreen.box, mem_setOf_eq, Pi.zero_apply, Int.cast_zero,
    sub_zero]
  constructor
  · intro h i
    exact_mod_cast (show ((u i).natAbs : ℝ) ≤ r by simpa only [natAbs_cast_real] using h i)
  · intro h i
    simpa only [natAbs_cast_real] using (show ((u i).natAbs : ℝ) ≤ r by exact_mod_cast h i)

/-- The exact near-far decomposition of the dimension-four ball Green field:
`ballGreenField r ζ z` equals `finiteKernelField (cutField r L φ) ζ z` plus
`finiteKernelField (nearKernel r L φ) ζ z`, since `nearKernel` is defined as the difference of
`killedGreen` and `cutField` and both series are summable. -/
lemma ballGreenField_eq_far_add_near (r L : ℕ) (φ : ℝ → ℝ) (ζ : Site 4 → ℝ) (z : Site 4) :
    ballGreenField r ζ z = finiteKernelField (External.BallGreen.cutField r L φ) ζ z +
      finiteKernelField (nearKernel r L φ) ζ z := by
  have hh : Summable (fun u : Site 4 => External.BallGreen.cutField r L φ u * ζ (z + u)) :=
    summable_of_ne_finset_zero (s := boxFinset 0 r)
      (fun u hu => by rw [cutField_eq_zero_of_notMem_boxFinset r L φ hu, zero_mul])
  have hq : Summable (fun u : Site 4 => nearKernel r L φ u * ζ (z + u)) :=
    summable_of_ne_finset_zero (s := boxFinset 0 r)
      (fun u hu => by rw [nearKernel_eq_zero_of_notMem_boxFinset r L φ hu, zero_mul])
  simp only [ballGreenField, ballCube_zero_eq_box, finiteKernelField]
  rw [← hh.tsum_add hq]
  apply tsum_congr
  intro u
  dsimp [nearKernel]
  ring

end Sandpile
