/-
The smoothed odometer `P^m u_n` as a function of the scenery.

`lem:dgt4-smoothed-odometer-tail` (`sandpile.tex:4417-4428`) applies the
concentration lemma to `P^m u_n(0)`.  Its coordinate Lipschitz constants are
`∑_z p_m(0,z) g_n(z,y) = ∑_{j<n} p_{m+j}(0,y)`, by the optimal-stopping
Lipschitz bound for `u_n` and Chapman-Kolmogorov.  This file reads `P^m u_n(x)`
as a function of the coordinates of a finite set of sites containing the box it
reads, and proves that bound in those coordinates.
-/
import Sandpile.Support.FiniteCoord
import Sandpile.Support.Iterate
import Sandpile.Support.Stationary
import Sandpile.External.GreenBoundsHigh

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- The coefficient `∑_{j<n} p_{m+j}(x,y)` of `lem:dgt4-smoothed-odometer-tail`. -/
noncomputable def smoothedCoeff (d : ℕ) (m n : ℕ) (x y : Site d) : ℝ :=
  ∑ j ∈ Finset.range n, heatKernel d (m + j) x y

theorem smoothedCoeff_nonneg (m n : ℕ) (x y : Site d) : 0 ≤ smoothedCoeff d m n x y :=
  Finset.sum_nonneg fun _ _ => heatKernel_nonneg _ _ _

theorem tsum_heatKernel_mul_greenTime' (m n : ℕ) (x y : Site d) :
    ∑' z : Site d, heatKernel d m x z * greenTime d n z y = smoothedCoeff d m n x y :=
  tsum_heatKernel_mul_greenTime m n x y

/-- `P^m u_n(x)`, read as a function of the coordinates of a finite set of
sites. -/
noncomputable def scenerySmoothed (s : Finset (Site d)) (m n : ℕ) (x : Site d)
    (ξ : Fin s.card → ℝ) : ℝ :=
  (avg^[m] fun z => odometerOf (siteExtend s ξ) n z) x

theorem scenerySmoothed_eq (s : Finset (Site d)) (m n : ℕ) (x : Site d)
    (ξ : Fin s.card → ℝ) :
    scenerySmoothed s m n x ξ
      = ∑ z ∈ boxFinset x m, heatKernel d m x z * odometerOf (siteExtend s ξ) n z := by
  rw [scenerySmoothed, avg_iterate, tsum_heatKernel_mul_eq_sum]

/-- The smoothed odometer at `x` reads only the sites of the box of radius
`m + n` about `x`. -/
theorem avg_odometerOf_congr_box (m n : ℕ) (x : Site d) (ζ η : Site d → ℝ)
    (h : ∀ w : Site d, boxDist x w ≤ m + n → ζ w = η w) :
    (avg^[m] fun z => odometerOf ζ n z) x = (avg^[m] fun z => odometerOf η n z) x := by
  rw [avg_iterate, avg_iterate, tsum_heatKernel_mul_eq_sum, tsum_heatKernel_mul_eq_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  by_cases hp : heatKernel d m x z = 0
  · simp [hp]
  · have hxz : boxDist x z ≤ m := heatKernel_support m x hp
    refine congrArg (fun r : ℝ => heatKernel d m x z * r) ?_
    refine odometerOf_congr_box n z ζ η fun w hw => ?_
    exact h w (le_trans (boxDist_trans x z w) (Nat.add_le_add hxz hw))

theorem scenerySmoothed_pick {s : Finset (Site d)} {m n : ℕ} {x : Site d}
    (hsub : boxFinset x (m + n) ⊆ s) (ζ : Site d → ℝ) :
    scenerySmoothed s m n x (fun i => ζ (siteEnum s i))
      = (avg^[m] fun z => odometerOf ζ n z) x :=
  avg_odometerOf_congr_box m n x _ ζ fun _ hw =>
    siteExtend_siteEnum s ζ (hsub (mem_boxFinset hw))

theorem measurable_scenerySmoothed (s : Finset (Site d)) (m n : ℕ) (x : Site d) :
    Measurable (scenerySmoothed s m n x) := by
  have h : ∀ ξ : Fin s.card → ℝ, scenerySmoothed s m n x ξ
      = ∑ z ∈ boxFinset x m, heatKernel d m x z * sceneryOdometer s n z ξ :=
    fun ξ => scenerySmoothed_eq s m n x ξ
  rw [funext h]
  exact Finset.measurable_sum _ fun z _ =>
    (measurable_sceneryOdometer s n z).const_mul _

/-- The coordinate Lipschitz bound for the smoothed odometer. -/
theorem abs_scenerySmoothed_update_le (s : Finset (Site d)) (m n : ℕ) (x : Site d)
    (ξ : Fin s.card → ℝ) (i : Fin s.card) (y : ℝ) :
    |scenerySmoothed s m n x ξ - scenerySmoothed s m n x (Function.update ξ i y)|
      ≤ smoothedCoeff d m n x (siteEnum s i) * |ξ i - y| := by
  rw [scenerySmoothed_eq, scenerySmoothed_eq, ← Finset.sum_sub_distrib]
  have hpt : ∀ z ∈ boxFinset x m,
      |heatKernel d m x z * odometerOf (siteExtend s ξ) n z -
          heatKernel d m x z * odometerOf (siteExtend s (Function.update ξ i y)) n z|
        ≤ heatKernel d m x z * (greenTime d n z (siteEnum s i) * |ξ i - y|) := by
    intro z _
    rw [← mul_sub, abs_mul, abs_of_nonneg (heatKernel_nonneg m x z)]
    refine mul_le_mul_of_nonneg_left ?_ (heatKernel_nonneg m x z)
    exact abs_sceneryOdometer_update_le s n z ξ i y
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hpt) (le_of_eq ?_)
  have hfac : ∀ z ∈ boxFinset x m,
      heatKernel d m x z * (greenTime d n z (siteEnum s i) * |ξ i - y|)
        = (heatKernel d m x z * greenTime d n z (siteEnum s i)) * |ξ i - y| :=
    fun z _ => by ring
  rw [Finset.sum_congr rfl hfac, ← Finset.sum_mul,
    ← tsum_heatKernel_mul_eq_sum m x (fun z => greenTime d n z (siteEnum s i)),
    tsum_heatKernel_mul_greenTime]
  rfl

/-- The heat kernel sums to one over the box of radius `m`. -/
theorem sum_heatKernel_boxFinset (hd : 1 ≤ d) (m : ℕ) (x : Site d) :
    ∑ z ∈ boxFinset x m, heatKernel d m x z = 1 := by
  have h := tsum_heatKernel hd m x
  have h2 := tsum_heatKernel_mul_eq_sum m x (fun _ => (1 : ℝ))
  simp only [mul_one] at h2
  rw [← h2, h]

/-- The mean of the smoothed odometer is the mean odometer. -/
theorem integral_avg_odometerOf (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (m n : ℕ) (x : Site d) :
    ∫ ζ, (avg^[m] fun z => odometerOf ζ n z) x ∂(LatticeProb.iidLaw d ν)
      = ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
  have hrep : ∀ ζ : Site d → ℝ, (avg^[m] fun z => odometerOf ζ n z) x
      = ∑ z ∈ boxFinset x m, heatKernel d m x z * odometerOf ζ n z := by
    intro ζ
    rw [avg_iterate, tsum_heatKernel_mul_eq_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hrep),
    integral_finsetSum _ fun z _ =>
      (integrable_odometerOf d ν hpos n z).const_mul (heatKernel d m x z)]
  have hz : ∀ z ∈ boxFinset x m,
      ∫ ζ, heatKernel d m x z * odometerOf ζ n z ∂(LatticeProb.iidLaw d ν)
        = heatKernel d m x z * ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
    intro z _
    rw [integral_const_mul, integral_odometerOf_eq d ν n z]
  rw [Finset.sum_congr rfl hz, ← Finset.sum_mul, sum_heatKernel_boxFinset hd m x, one_mul]

/-- The smoothed coefficient is at most the time tail of the heat kernel. -/
theorem smoothedCoeff_le_tailKernel (m n : ℕ) (y : Site d)
    (hsummable : Summable fun j : {j : ℕ // m ≤ j} => heatKernel d (j : ℕ) 0 y) :
    smoothedCoeff d m n 0 y ≤ Sandpile.External.tailKernel d m y := by
  classical
  have himg : smoothedCoeff d m n 0 y
      = ∑ j ∈ (Finset.range n).image (fun j : ℕ => (⟨m + j, Nat.le_add_right m j⟩ :
          {j : ℕ // m ≤ j})), heatKernel d (j : ℕ) 0 y := by
    rw [smoothedCoeff, Finset.sum_image]
    intro a _ b _ hab
    have : m + a = m + b := congrArg Subtype.val hab
    omega
  rw [himg]
  exact hsummable.sum_le_tsum _ (fun j _ => heatKernel_nonneg _ _ _)

/-- The averaging operator fixes constants, so it commutes with subtracting one. -/
theorem avg_iterate_sub_const (hd : 1 ≤ d) (m : ℕ) (f : Site d → ℝ) (c : ℝ) (x : Site d) :
    (avg^[m] fun z => f z - c) x = (avg^[m] f) x - c := by
  rw [avg_iterate, avg_iterate, tsum_heatKernel_mul_eq_sum, tsum_heatKernel_mul_eq_sum]
  have hexp : ∀ z ∈ boxFinset x m, heatKernel d m x z * (f z - c)
      = heatKernel d m x z * f z - heatKernel d m x z * c := fun z _ => by ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_heatKernel_boxFinset hd m x, one_mul]

theorem avg_iterate_zero (m : ℕ) (x : Site d) :
    (avg^[m] fun _ : Site d => (0 : ℝ)) x = 0 := by
  rw [avg_iterate]
  simp

theorem boxFinset_mono {x : Site d} {r r' : ℕ} (h : r ≤ r') :
    boxFinset x r ⊆ boxFinset x r' := by
  intro y hy
  exact mem_boxFinset (le_trans (mem_boxFinset_iff.mp hy) h)

/-- Some coefficient is nonzero, which is what the concentration lemma asks
for. -/
theorem exists_smoothedCoeff_ne_zero (hd : 1 ≤ d) (m n : ℕ) (hn : 1 ≤ n) :
    ∃ i : Fin (boxFinset (0 : Site d) (m + n)).card,
      smoothedCoeff d m n 0 (siteEnum (boxFinset (0 : Site d) (m + n)) i) ≠ 0 := by
  classical
  have hone := sum_heatKernel_boxFinset hd m (0 : Site d)
  have hne : ∑ z ∈ boxFinset (0 : Site d) m, heatKernel d m 0 z ≠ 0 := by
    rw [hone]; norm_num
  obtain ⟨z, hz, hpz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hzmem : z ∈ boxFinset (0 : Site d) (m + n) :=
    boxFinset_mono (Nat.le_add_right m n) hz
  refine ⟨(boxFinset (0 : Site d) (m + n)).equivFin ⟨z, hzmem⟩, ?_⟩
  have hidx : siteEnum (boxFinset (0 : Site d) (m + n))
      ((boxFinset (0 : Site d) (m + n)).equivFin ⟨z, hzmem⟩) = z := by
    simp [siteEnum]
  rw [hidx]
  have hle : heatKernel d m 0 z ≤ smoothedCoeff d m n 0 z := by
    have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
    have hstep := Finset.single_le_sum (f := fun j => heatKernel d (m + j) 0 z)
      (fun j _ => heatKernel_nonneg _ _ _) h0
    rw [smoothedCoeff]
    simpa using hstep
  have hpos : 0 < heatKernel d m 0 z :=
    lt_of_le_of_ne (heatKernel_nonneg m 0 z) (Ne.symm hpz)
  exact ne_of_gt (lt_of_lt_of_le hpos hle)

/-- The `ℓ²` mass of the smoothed coefficients is at most that of the time-tail
kernel. -/
theorem sum_smoothedCoeff_sq_le (m n : ℕ)
    (hsum : ∀ y : Site d, Summable fun j : {j : ℕ // m ≤ j} => heatKernel d (j : ℕ) 0 y)
    (hs2 : Summable fun y : Site d => Sandpile.External.tailKernel d m y ^ 2) :
    ∑ i : Fin (boxFinset (0 : Site d) (m + n)).card,
        smoothedCoeff d m n 0 (siteEnum (boxFinset (0 : Site d) (m + n)) i) ^ 2
      ≤ ∑' y : Site d, Sandpile.External.tailKernel d m y ^ 2 := by
  classical
  rw [sum_siteEnum (boxFinset (0 : Site d) (m + n)) fun y => smoothedCoeff d m n 0 y ^ 2]
  refine le_trans (Finset.sum_le_sum fun y _ => ?_)
    (hs2.sum_le_tsum (boxFinset (0 : Site d) (m + n)) fun y _ => sq_nonneg _)
  exact pow_le_pow_left₀ (smoothedCoeff_nonneg m n 0 y)
    (smoothedCoeff_le_tailKernel m n y (hsum y)) 2

end Sandpile
