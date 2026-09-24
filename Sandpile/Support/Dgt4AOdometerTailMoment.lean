/-
The variance of `P^ju_n(0)` at the tail-kernel coefficients.  The functional reads the box
`Q(0,n+j)`, its coordinate Lipschitz coefficient at `z` is the tail kernel
`\sum_{r\geq j}p_r(0,z)`, and those are square summable in `d\geq5`
(`eq:dgt4-tail-kernel`, `sandpile.tex:1303-1306`), so the product moment bound gives a
second moment bounded by the square sum of the tail kernel.
-/
import Sandpile.Support.Dgt4AOdometerTailLip
import Sandpile.Support.Dgt4ATailKernelSq
import Sandpile.Support.Concentration
import Sandpile.Support.BlockIncrement

open LatticeProb

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

theorem tailKernel_nonneg (j : ℕ) (y : Site d) :
    0 ≤ Sandpile.External.tailKernel d j y :=
  tsum_nonneg fun _ => heatKernel_nonneg _ _ _

/-- `P^ju_n(0)` reads only the box `Q(0,n+j)`. -/
theorem avgIterate_odometerOf_congr_box (n j : ℕ) (ζ η : Site d → ℝ)
    (he : ∀ z ∈ boxFinset (0 : Site d) (n + j), ζ z = η z) :
    (avg^[j] (fun y => odometerOf ζ n y)) 0 = (avg^[j] (fun y => odometerOf η n y)) 0 := by
  rw [avg_iterate_eq_finsetSum, avg_iterate_eq_finsetSum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzj : boxDist (0 : Site d) z ≤ j := mem_boxFinset_iff.mp hz
  have hcong : odometerOf ζ n z = odometerOf η n z := by
    refine odometerOf_congr_box n z ζ η fun w hw => he w ?_
    have h := boxDist_trans (0 : Site d) z w
    exact mem_boxFinset (by omega)
  rw [hcong]

/-- `P^ju_n(0)` read as a function of the coordinates of `Q(0,n+j)`. -/
noncomputable def boxAvgIterateOdometer (n j : ℕ)
    (ξ : Fin (boxFinset (0 : Site d) (n + j)).card → ℝ) : ℝ :=
  (avg^[j] (fun y => odometerOf (siteExtend (boxFinset (0 : Site d) (n + j)) ξ) n y)) 0

theorem measurable_boxAvgIterateOdometer (n j : ℕ) :
    Measurable (boxAvgIterateOdometer (d := d) n j) :=
  (measurable_avg_iterate_odometerOf j n 0).comp (measurable_siteExtend _)

theorem boxAvgIterateOdometer_pick (n j : ℕ) (ζ : Site d → ℝ) :
    boxAvgIterateOdometer n j
        (fun i => ζ (siteEnum (boxFinset (0 : Site d) (n + j)) i))
      = (avg^[j] (fun y => odometerOf ζ n y)) 0 :=
  avgIterate_odometerOf_congr_box n j _ ζ fun _ hz => siteExtend_siteEnum _ ζ hz

theorem abs_boxAvgIterateOdometer_update_le (hd : 5 ≤ d) (n j : ℕ)
    (ξ : Fin (boxFinset (0 : Site d) (n + j)).card → ℝ)
    (i : Fin (boxFinset (0 : Site d) (n + j)).card) (v : ℝ) :
    |boxAvgIterateOdometer n j ξ - boxAvgIterateOdometer n j (Function.update ξ i v)|
      ≤ Sandpile.External.tailKernel d j
          (siteEnum (boxFinset (0 : Site d) (n + j)) i) * |ξ i - v| := by
  have hval : siteExtend (boxFinset (0 : Site d) (n + j)) ξ
      (siteEnum (boxFinset (0 : Site d) (n + j)) i) = ξ i := by
    simp [siteExtend, siteEnum]
  have h := abs_avgIterate_odometerOf_update_le hd
    (siteExtend (boxFinset (0 : Site d) (n + j)) ξ)
    (siteEnum (boxFinset (0 : Site d) (n + j)) i) v n j
  simpa only [boxAvgIterateOdometer, siteExtend_update, hval] using h

/-- The `p`-th moment of `P^ju_n(0)` about its mean, at the tail-kernel coefficients. -/
theorem exists_integral_avgIterate_odometerOf_moment_le
    (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ} (hp : 2 ≤ p)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n j : ℕ, 1 ≤ j →
      (∫ ζ, |(avg^[j] (fun y => odometerOf ζ n y)) 0
          - ∫ η, (avg^[j] (fun y => odometerOf η n y)) 0 ∂(LatticeProb.iidLaw d ν)| ^ p
          ∂(LatticeProb.iidLaw d ν))
        ≤ C * pairMoment ν p
          * (∑' z : Site d, Sandpile.External.tailKernel d j z ^ 2) ^ (p / 2) := by
  obtain ⟨C, hC, hb⟩ := exists_pick_moment_bound (d := d) hp
  refine ⟨C, hC, fun n j hj => ?_⟩
  have h := hb ν inferInstance hmom (boxFinset (0 : Site d) (n + j)).card
    (siteEnum (boxFinset (0 : Site d) (n + j))) (siteEnum_injective _)
    (boxAvgIterateOdometer n j) (measurable_boxAvgIterateOdometer n j)
    (fun i => Sandpile.External.tailKernel d j
      (siteEnum (boxFinset (0 : Site d) (n + j)) i))
    (fun i => tailKernel_nonneg j _)
    (abs_boxAvgIterateOdometer_update_le hd n j)
  simp only [boxAvgIterateOdometer_pick n j] at h
  refine h.trans ?_
  have hsum : (∑ i : Fin (boxFinset (0 : Site d) (n + j)).card,
        Sandpile.External.tailKernel d j
          (siteEnum (boxFinset (0 : Site d) (n + j)) i) ^ 2)
      ≤ ∑' z : Site d, Sandpile.External.tailKernel d j z ^ 2 := by
    rw [sum_siteEnum (boxFinset (0 : Site d) (n + j))
      (fun z => Sandpile.External.tailKernel d j z ^ 2)]
    exact (summable_tailKernel_sq hGH hd hj).sum_le_tsum _ (fun _ _ => sq_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => sq_nonneg _) hsum (by linarith))
    (mul_nonneg hC.le (pairMoment_nonneg ν p))

end Sandpile
