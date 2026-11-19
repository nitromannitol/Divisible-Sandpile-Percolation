import Sandpile.External.LocalCLT
import Sandpile.External.MaxDisplacementProved
import LatticeProb.Graph.WalkAverage
import Sandpile.External.Stopping.GridStopping

/-!
# Linear interpolation of the lattice walk

The rescaled walk is linearly interpolated between successive lattice times.
At each grid time its history is determined by the walk positions up to that
time, as needed for stopping-time arguments.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Linear interpolation of a rescaled walk, in units of one lattice step. -/
noncomputable def linearWalk {d : ℕ} (R : ℝ) (s : ℝ≥0) (X : ℕ → Site d) :
    Continuum.Space d :=
  let n := ⌊(s : ℝ)⌋₊
  let a := (s : ℝ) - n
  (1 - a) • Lclt.scaledSite R (X n) + a • Lclt.scaledSite R (X (n + 1))

/-- At a lattice time the interpolation equals the scaled walk position. -/
@[simp] theorem linearWalk_nat {d : ℕ} (R : ℝ) (k : ℕ) (X : ℕ → Site d) :
    linearWalk R k X = Lclt.scaledSite R (X k) := by
  simp [linearWalk]

/-- The interpolated walk through a lattice time is determined by the discrete
walk through that time. -/
theorem linearWalk_grid_causal {d : ℕ} (R : ℝ) (k : ℕ) (X Y : ℕ → Site d)
    (hXY : ∀ j ≤ k, X j = Y j) (s : ℝ≥0) (hs : s ≤ k) :
    linearWalk R s X = linearWalk R s Y := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · simpa only [linearWalk_nat] using congrArg (Lclt.scaledSite R) (hXY k le_rfl)
  · have hs' : (s : ℝ) < k := by exact_mod_cast hs
    have hn : ⌊(s : ℝ)⌋₊ < k := (Nat.floor_lt s.property).2 hs'
    simp only [linearWalk, hXY _ (Nat.le_of_lt hn), hXY _ hn]

/-- The interpolation is at most one scaled walk increment from the next
lattice position. -/
theorem norm_linearWalk_sub_next_le {d : ℕ} (R : ℝ) (s : ℝ≥0) (X : ℕ → Site d) :
    ‖linearWalk R s X - Lclt.scaledSite R (X (⌊(s : ℝ)⌋₊ + 1))‖ ≤
      ‖Lclt.scaledSite R (X ⌊(s : ℝ)⌋₊) -
        Lclt.scaledSite R (X (⌊(s : ℝ)⌋₊ + 1))‖ := by
  let n := ⌊(s : ℝ)⌋₊
  let a : ℝ := (s : ℝ) - n
  have ha0 : 0 ≤ a := by
    dsimp [a, n]
    exact sub_nonneg.mpr (Nat.floor_le s.property)
  have ha1 : a ≤ 1 := by dsimp [a, n]; linarith [Nat.lt_floor_add_one (s : ℝ)]
  have heq : linearWalk R s X - Lclt.scaledSite R (X (n + 1)) =
      (1 - a) • (Lclt.scaledSite R (X n) - Lclt.scaledSite R (X (n + 1))) := by
    change (1 - a) • Lclt.scaledSite R (X n) +
      a • Lclt.scaledSite R (X (n + 1)) - Lclt.scaledSite R (X (n + 1)) = _
    simp only [smul_sub, sub_smul, one_smul]
    abel
  change ‖linearWalk R s X - Lclt.scaledSite R (X (n + 1))‖ ≤
    ‖Lclt.scaledSite R (X n) - Lclt.scaledSite R (X (n + 1))‖
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha1)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

/-- Euclidean displacement of scaled sites is bounded by the graph distance
scaled by the same factor. -/
theorem norm_scaledSite_sub_le_graphNorm {d : ℕ} (R : ℝ) (hR : 0 < R)
    (x y : Site d) :
    ‖Lclt.scaledSite R x - Lclt.scaledSite R y‖ ≤
      ((LatticeProb.graphNorm (x - y) : ℕ) : ℝ) / R := by
  have hcoord : ∀ i : Fin d, (Lclt.scaledSite R x - Lclt.scaledSite R y) i =
      ((x i - y i : ℤ) : ℝ) / R := by
    intro i
    show ((x i : ℤ) : ℝ) / R - ((y i : ℤ) : ℝ) / R = _
    push_cast
    ring
  have heq : ‖Lclt.scaledSite R x - Lclt.scaledSite R y‖ = latticeDist x y / R := by
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ i : Fin d, ‖(Lclt.scaledSite R x - Lclt.scaledSite R y) i‖ ^ 2 =
        (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2) * (R⁻¹) ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcoord i, Real.norm_eq_abs, sq_abs, div_pow]
      field_simp
    rw [hsum, Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
      Real.sqrt_sq (le_of_lt (inv_pos.mpr hR))]
    rfl
  rw [heq]
  exact div_le_div_of_nonneg_right (latticeDist_le_graphNorm x y) hR.le

/-- Every scaled step has length at most `1 / R`, simultaneously at all times,
almost surely. -/
theorem ae_norm_scaled_walk_step_le {d : ℕ} (hd : 1 ≤ d) (x : Site d)
    (R : ℝ) (hR : 0 < R) :
    ∀ᵐ X ∂(walkLaw d x), ∀ n : ℕ,
      ‖Lclt.scaledSite R (X n) - Lclt.scaledSite R (X (n + 1))‖ ≤ 1 / R := by
  let : NeZero d := ⟨by omega⟩
  filter_upwards [show ∀ᵐ X ∂(walkLaw d x), X 0 = x ∧
      ∀ k : ℕ, (LatticeProb.lattice d).Adj (X k) (X (k + 1)) from
        LatticeProb.ae_adj_siteWalkLaw x] with X hX n
  obtain ⟨i, hi⟩ := LatticeProb.Graph.Zd.adj_iff.mp (hX.2 n)
  have hu : LatticeProb.graphNorm (unit i : Site d) = 1 := by
    rw [← LatticeProb.dirVec_eq_unit i, LatticeProb.graphNorm_dirVec]
  rcases hi with hi | hi
  · have hs : X n - X (n + 1) = -(unit i : Site d) := by rw [hi]; abel
    simpa [hs, LatticeProb.graphNorm_neg, hu] using
      norm_scaledSite_sub_le_graphNorm R hR (X n) (X (n + 1))
  · have hs : X n - X (n + 1) = (unit i : Site d) := by rw [hi]; abel
    simpa [hs, hu] using norm_scaledSite_sub_le_graphNorm R hR (X n) (X (n + 1))

/-- The interpolation is uniformly within `1 / R` of its next grid position
on almost every walk path. -/
theorem ae_norm_linearWalk_sub_next_le {d : ℕ} (hd : 1 ≤ d) (x : Site d)
    (R : ℝ) (hR : 0 < R) :
    ∀ᵐ X ∂(walkLaw d x), ∀ s : ℝ≥0,
      ‖linearWalk R s X - Lclt.scaledSite R (X (⌊(s : ℝ)⌋₊ + 1))‖ ≤ 1 / R := by
  filter_upwards [ae_norm_scaled_walk_step_le hd x R hR] with X hX s
  exact (norm_linearWalk_sub_next_le R s X).trans (hX ⌊(s : ℝ)⌋₊)

end Sandpile.External.Stopping
