/-
The smoothed difference `P^n(u_{t-n} - V_{t-n})(x)` as a function of finitely
many scenery coordinates, with its coordinate Lipschitz bound.

Step 2 of `prop:d4-pointwise-linearization` (`sandpile.tex:3100-3125`) reads the
first summand of the backward decomposition through
`lem:difference-representation`: changing one coordinate `ζ(z)` by `h` moves
`u_{t-n}(y) - V_{t-n}(y)` by at most `|h| ∑_{j<t-n} p_j(y,z)`, and averaging
against `p_n(x,y)` turns that into `|h| ∑_{k=n}^{t-1} p_k(x,z)`.  Here the same
coefficient is obtained without the optimal-stopping representation: the
odometer's own Lipschitz bound is `Sandpile.abs_odometerOf_update_le` and the
membrane is linear with the same kernel, so the difference has twice that
coefficient, which changes only the constants of the tail.
-/
import Sandpile.Support.Smoothed
import Sandpile.Support.D4Linearization

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### The membrane as a sum of iterates -/

/-- `V_n = ∑_{k<n} P^k ζ`. -/
theorem membrane_eq_sum_avg_iterate (ζ : Site d → ℝ) :
    ∀ (n : ℕ) (y : Site d), membrane ζ n y = ∑ k ∈ Finset.range n, (avg^[k] ζ) y := by
  intro n
  induction n with
  | zero => intro y; simp [membrane]
  | succ n ih =>
      intro y
      have hfun : membrane ζ n = fun w => ∑ k ∈ Finset.range n, (avg^[k] ζ) w := funext ih
      have hstep : avg (fun w => ∑ k ∈ Finset.range n, (avg^[k] ζ) w) y
          = ∑ k ∈ Finset.range n, avg (avg^[k] ζ) y :=
        LatticeProb.walkOp_finsetSum (Finset.range n) (fun k => avg^[k] ζ) y
      have hsucc : ∀ k ∈ Finset.range n, avg (avg^[k] ζ) y = (avg^[k + 1] ζ) y := by
        intro k _
        rw [Function.iterate_succ_apply']
      show ζ y + avg (membrane ζ n) y = _
      rw [hfun, hstep, Finset.sum_congr rfl hsucc,
        Finset.sum_range_succ' (fun k => (avg^[k] ζ) y) n]
      simp [add_comm]

theorem avg_iterate_finsetSum {ι : Type*} (s : Finset ι) :
    ∀ (m : ℕ) (F : ι → Site d → ℝ) (x : Site d),
      (avg^[m] fun y => ∑ k ∈ s, F k y) x = ∑ k ∈ s, (avg^[m] (F k)) x := by
  intro m
  induction m with
  | zero => intro F x; simp
  | succ m ih =>
      intro F x
      have hfun : (avg fun y => ∑ k ∈ s, F k y) = fun w => ∑ k ∈ s, avg (F k) w :=
        funext fun w => LatticeProb.walkOp_finsetSum s F w
      rw [Function.iterate_succ_apply, hfun, ih (fun k => avg (F k)) x]
      exact Finset.sum_congr rfl fun k _ =>
        congrFun (Function.iterate_succ_apply avg m (F k)).symm x

/-- `P^m V_n(x) = ∑_z (∑_{j<n} p_{m+j}(x,z)) ζ(z)`. -/
theorem avg_iterate_membrane (m n : ℕ) (x : Site d) (ζ : Site d → ℝ) :
    (avg^[m] (membrane ζ n)) x = ∑' z : Site d, smoothedCoeff d m n x z * ζ z := by
  have hfun : membrane ζ n = fun y => ∑ k ∈ Finset.range n, (avg^[k] ζ) y :=
    funext (membrane_eq_sum_avg_iterate ζ n)
  rw [hfun, avg_iterate_finsetSum (Finset.range n) m (fun k => avg^[k] ζ) x]
  have hshift : ∀ k ∈ Finset.range n,
      (avg^[m] (avg^[k] ζ)) x = ∑' z : Site d, heatKernel d (m + k) x z * ζ z := by
    intro k _
    rw [← Function.iterate_add_apply avg m k ζ]
    exact avg_iterate (m + k) ζ x
  rw [Finset.sum_congr rfl hshift,
    ← Summable.tsum_finsetSum fun k (_ : k ∈ Finset.range n) =>
      summable_heatKernel_mul (m + k) x ζ]
  exact tsum_congr fun z => by rw [smoothedCoeff, Finset.sum_mul]

/-- The window coefficient vanishes outside the box of radius `m + n`. -/
theorem smoothedCoeff_eq_zero_of_lt (m n : ℕ) (x z : Site d) (h : m + n < boxDist x z) :
    smoothedCoeff d m n x z = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : j < n := Finset.mem_range.mp hj
  exact heatKernel_eq_zero_of_lt (m + j) x z (by omega)

theorem tsum_smoothedCoeff_mul_eq_sum (m n : ℕ) (x : Site d) (f : Site d → ℝ) :
    ∑' z : Site d, smoothedCoeff d m n x z * f z
      = ∑ z ∈ boxFinset x (m + n), smoothedCoeff d m n x z * f z := by
  refine tsum_eq_sum fun z hz => ?_
  have hzero : smoothedCoeff d m n x z = 0 :=
    smoothedCoeff_eq_zero_of_lt m n x z
      (by by_contra hc; exact hz (mem_boxFinset (Nat.le_of_not_lt hc)))
  simp [hzero]

theorem tsum_smoothedCoeff_sq_eq_sum (m n : ℕ) (x : Site d) :
    ∑' z : Site d, smoothedCoeff d m n x z ^ 2
      = ∑ z ∈ boxFinset x (m + n), smoothedCoeff d m n x z ^ 2 := by
  have h := tsum_smoothedCoeff_mul_eq_sum m n x (fun z => smoothedCoeff d m n x z)
  simpa [sq] using h

/-! ### The smoothed difference in box coordinates -/

/-- `P^m V_n(x)` as a linear functional of the coordinates of a finite set. -/
noncomputable def windowLinear (s : Finset (Site d)) (m n : ℕ) (x : Site d)
    (ξ : Fin s.card → ℝ) : ℝ :=
  ∑ i, smoothedCoeff d m n x (siteEnum s i) * ξ i

/-- `P^m (u_n - V_n)(x)` as a function of the coordinates of a finite set. -/
noncomputable def diffSmoothed (s : Finset (Site d)) (m n : ℕ) (x : Site d)
    (ξ : Fin s.card → ℝ) : ℝ :=
  scenerySmoothed s m n x ξ - windowLinear s m n x ξ

/-- `P^m (u_n - V_n) = P^m u_n - P^m V_n`. -/
theorem avg_iterate_diffField (m n : ℕ) (x : Site d) (ζ : Site d → ℝ) :
    (avg^[m] (diffField ζ n)) x
      = (avg^[m] fun z => odometerOf ζ n z) x - (avg^[m] (membrane ζ n)) x := by
  have hneg : diffField ζ n = fun y => odometerOf ζ n y + (-1) * membrane ζ n y := by
    funext y; rw [diffField]; ring
  rw [hneg, avg_iterate_add m (fun z => odometerOf ζ n z)
    (fun z => (-1) * membrane ζ n z) x]
  have hmul : (avg^[m] fun z => (-1 : ℝ) * membrane ζ n z) x
      = (-1 : ℝ) * (avg^[m] (membrane ζ n)) x := by
    rw [avg_iterate, avg_iterate, ← tsum_mul_left]
    exact tsum_congr fun z => by ring
  rw [hmul]; ring

theorem windowLinear_pick {s : Finset (Site d)} {m n : ℕ} {x : Site d}
    (hsub : boxFinset x (m + n) ⊆ s) (ζ : Site d → ℝ) :
    windowLinear s m n x (fun i => ζ (siteEnum s i)) = (avg^[m] (membrane ζ n)) x := by
  classical
  rw [avg_iterate_membrane, tsum_smoothedCoeff_mul_eq_sum]
  rw [windowLinear, sum_siteEnum s fun z => smoothedCoeff d m n x z * ζ z]
  refine (Finset.sum_subset hsub fun z _ hz => ?_).symm
  have hzero : smoothedCoeff d m n x z = 0 :=
    smoothedCoeff_eq_zero_of_lt m n x z
      (by by_contra hc; exact hz (mem_boxFinset (Nat.le_of_not_lt hc)))
  simp [hzero]

theorem diffSmoothed_pick {s : Finset (Site d)} {m n : ℕ} {x : Site d}
    (hsub : boxFinset x (m + n) ⊆ s) (ζ : Site d → ℝ) :
    diffSmoothed s m n x (fun i => ζ (siteEnum s i)) = (avg^[m] (diffField ζ n)) x := by
  have hsub' : boxFinset x (m + n) ⊆ s := hsub
  have hodo : scenerySmoothed s m n x (fun i => ζ (siteEnum s i))
      = (avg^[m] fun z => odometerOf ζ n z) x := scenerySmoothed_pick hsub' ζ
  rw [diffSmoothed, hodo, windowLinear_pick hsub' ζ, avg_iterate_diffField m n x ζ]

theorem measurable_windowLinear (s : Finset (Site d)) (m n : ℕ) (x : Site d) :
    Measurable (windowLinear s m n x) := by
  unfold windowLinear
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _

theorem measurable_diffSmoothed (s : Finset (Site d)) (m n : ℕ) (x : Site d) :
    Measurable (diffSmoothed s m n x) :=
  (measurable_scenerySmoothed s m n x).sub (measurable_windowLinear s m n x)

/-- **The coordinate Lipschitz bound for the smoothed difference.**  Twice the
window coefficient: once from the odometer, once from the membrane. -/
theorem abs_diffSmoothed_update_le (s : Finset (Site d)) (m n : ℕ) (x : Site d)
    (ξ : Fin s.card → ℝ) (i : Fin s.card) (y : ℝ) :
    |diffSmoothed s m n x ξ - diffSmoothed s m n x (Function.update ξ i y)|
      ≤ 2 * smoothedCoeff d m n x (siteEnum s i) * |ξ i - y| := by
  classical
  have hlin : windowLinear s m n x ξ - windowLinear s m n x (Function.update ξ i y)
      = smoothedCoeff d m n x (siteEnum s i) * (ξ i - y) := by
    unfold windowLinear
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · rw [Function.update_self]; ring
    · intro j _ hj; rw [Function.update_of_ne hj]; ring
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hodo := abs_scenerySmoothed_update_le s m n x ξ i y
  have hsplit : diffSmoothed s m n x ξ - diffSmoothed s m n x (Function.update ξ i y)
      = (scenerySmoothed s m n x ξ - scenerySmoothed s m n x (Function.update ξ i y))
        - (windowLinear s m n x ξ - windowLinear s m n x (Function.update ξ i y)) := by
    unfold diffSmoothed; ring
  rw [hsplit, hlin]
  refine le_trans (abs_sub _ _) ?_
  rw [abs_mul, abs_of_nonneg (smoothedCoeff_nonneg m n x (siteEnum s i))]
  have := smoothedCoeff_nonneg (d := d) m n x (siteEnum s i)
  nlinarith [abs_nonneg (ξ i - y), hodo]



/-! ### The window coefficient at a general site -/

/-- Some window coefficient is nonzero, which is what the concentration lemma
asks for.  This is `exists_smoothedCoeff_ne_zero` at a general site. -/
theorem exists_smoothedCoeff_ne_zero' (hd : 1 ≤ d) (m n : ℕ) (hn : 1 ≤ n) (x : Site d) :
    ∃ i : Fin (boxFinset x (m + n)).card,
      smoothedCoeff d m n x (siteEnum (boxFinset x (m + n)) i) ≠ 0 := by
  classical
  have hone := sum_heatKernel_boxFinset hd m x
  have hne : ∑ z ∈ boxFinset x m, heatKernel d m x z ≠ 0 := by
    rw [hone]; norm_num
  obtain ⟨z, hz, hpz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hzmem : z ∈ boxFinset x (m + n) := boxFinset_mono (Nat.le_add_right m n) hz
  refine ⟨(boxFinset x (m + n)).equivFin ⟨z, hzmem⟩, ?_⟩
  have hidx : siteEnum (boxFinset x (m + n))
      ((boxFinset x (m + n)).equivFin ⟨z, hzmem⟩) = z := by
    simp [siteEnum]
  rw [hidx]
  have hle : heatKernel d m x z ≤ smoothedCoeff d m n x z := by
    have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
    have hstep := Finset.single_le_sum (f := fun j => heatKernel d (m + j) x z)
      (fun j _ => heatKernel_nonneg _ _ _) h0
    rw [smoothedCoeff]
    simpa using hstep
  have hpos : 0 < heatKernel d m x z :=
    lt_of_le_of_ne (heatKernel_nonneg m x z) (Ne.symm hpz)
  exact ne_of_gt (lt_of_lt_of_le hpos hle)

/-- The window coefficient of `eq:d4-window-l2` is the smoothed coefficient with
the window written as a time interval: `∑_{j<t-n} p_{n+j} = ∑_{k=n}^{t-1} p_k`. -/
theorem smoothedCoeff_eq_windowKernel (n t : ℕ) (x z : Site 4) :
    smoothedCoeff 4 n (t - n) x z = Sandpile.External.Variance.windowKernel n t x z := by
  rw [smoothedCoeff, Sandpile.External.Variance.windowKernel,
    Finset.sum_Ico_eq_sum_range]

/-- The mean of the smoothed difference is the mean odometer: the membrane part
is centred. -/
theorem integral_diffSmoothed (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z => max z 0) ν) (m n : ℕ) (x : Site d) :
    ∫ ξ, diffSmoothed (boxFinset x (m + n)) m n x ξ
        ∂(Measure.pi fun _ : Fin (boxFinset x (m + n)).card => ν)
      = ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
  classical
  have hbox : ∀ ζ : Site d → ℝ, (avg^[m] fun z => odometerOf ζ n z) x
      = ∑ z ∈ boxFinset x m, heatKernel d m x z * odometerOf ζ n z := fun ζ => by
    rw [avg_iterate, tsum_heatKernel_mul_eq_sum]
  have hI1 : Integrable (fun ζ : Site d → ℝ => (avg^[m] fun z => odometerOf ζ n z) x)
      (LatticeProb.iidLaw d ν) := by
    refine (Integrable.congr ?_ (Filter.Eventually.of_forall fun ζ => (hbox ζ).symm))
    exact integrable_finsetSum _ fun z _ => (integrable_odometerOf d ν hpos n z).const_mul _
  have hmem : ∀ ζ : Site d → ℝ, (avg^[m] (membrane ζ n)) x
      = ∑ i : Fin (boxFinset x (m + n)).card,
          smoothedCoeff d m n x (boxEnum x (m + n) i) * ζ (boxEnum x (m + n) i) := fun ζ => by
    rw [avg_iterate_membrane, tsum_smoothedCoeff_mul_eq_sum,
      ← sum_boxEnum x (m + n) fun z => smoothedCoeff d m n x z * ζ z]
  have hI2 : Integrable (fun ζ : Site d → ℝ => (avg^[m] (membrane ζ n)) x)
      (LatticeProb.iidLaw d ν) := by
    refine (Integrable.congr ?_ (Filter.Eventually.of_forall fun ζ => (hmem ζ).symm))
    exact integrable_finsetSum _ fun i _ =>
      (integrable_coord ν hint (boxEnum x (m + n) i)).const_mul _
  have hzero : ∫ ζ, (avg^[m] (membrane ζ n)) x ∂(LatticeProb.iidLaw d ν) = 0 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hmem),
      integral_finsetSum _ (fun i _ =>
        (integrable_coord ν hint (boxEnum x (m + n) i)).const_mul _)]
    simp only [integral_const_mul, integral_coord ν hint, hmean, mul_zero,
      Finset.sum_const_zero]
  rw [← integral_pick ν (siteEnum (boxFinset x (m + n))) (siteEnum_injective _) _
      (measurable_diffSmoothed _ m n x).aestronglyMeasurable,
    integral_congr_ae (Filter.Eventually.of_forall fun ζ =>
      diffSmoothed_pick (subset_refl (boxFinset x (m + n))) ζ),
    integral_congr_ae (Filter.Eventually.of_forall fun ζ => avg_iterate_diffField m n x ζ),
    integral_sub hI1 hI2, hzero, sub_zero,
    integral_avg_odometerOf hd ν hpos m n x]

end Sandpile
