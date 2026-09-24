/-
The first-passage decomposition of the Green function on path space.
The stopped Poisson identity gives the decomposition at each bounded horizon.
Transience makes exits from finite domains almost surely finite, and the
uniform Green bound permits passage to the full exit time.
-/
import Sandpile.Support.FiniteRange
import Sandpile.Support.HitProb
import LatticeProb.Graph.ExitDecomp
import LatticeProb.Graph.ExitTime

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

theorem stopped_poisson_telescope (f : Site d → ℝ) (t : ℕ) (X : ℕ → Site d)
    (N : ℕ) (hN : N ≤ t) :
    sceneryPartialSum (fun y => f y - avg f y) N X + f (X N) =
      f (X 0) + ∑ n ∈ Finset.range t, (if n < N then (1 : ℝ) else 0) *
        (f (X (n + 1)) - avg f (X n)) := by
  classical
  set a := fun n => sceneryPartialSum (fun y => f y - avg f y) n X + f (X n)
  have ha := telescope_stopped a hN
  have h0 : a 0 = f (X 0) := by simp [a, sceneryPartialSum]
  rw [h0] at ha
  change a N = _
  rw [ha]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n < N
  · simp only [if_pos hn, one_mul, a, sceneryPartialSum, Finset.sum_range_succ]
    ring
  · rw [if_neg hn, if_neg hn, zero_mul]

/-- The stopped Poisson identity follows by integrating the stopped martingale
differences of a deterministic field. -/
theorem integral_stopped_poisson (hd : 1 ≤ d) (x : Site d) (f : Site d → ℝ) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    (∫ X, sceneryPartialSum (fun y => f y - avg f y) (τ X) X + f (X (τ X)) ∂walkLaw d x)
      = f x := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  set P := Measure.infinitePi (fun _ : ℕ => stepLaw d)
  have hpay : Integrable (fun X => sceneryPartialSum (fun y => f y - avg f y) (τ X) X +
      f (X (τ X))) (walkLaw d x) :=
    (integrable_stoppedScenery_walk hd x (fun y => f y - avg f y) t hτ hτt).add
      (integrable_stopped_value hd x t (fun _ => f) hτ hτt)
  rw [integral_walkLaw x hpay.aestronglyMeasurable]
  have hinc := fun n => integral_stopped_field_increment hd x f n hτ
  have hsum : Integrable (fun ξ : ℕ → Site d => ∑ n ∈ Finset.range t,
      (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
        (f (walkPath x ξ (n + 1)) - avg f (walkPath x ξ n))) P :=
    integrable_finsetSum _ fun n _ => (hinc n).1
  have hpt : ∀ ξ : ℕ → Site d,
      sceneryPartialSum (fun y => f y - avg f y) (τ (walkPath x ξ)) (walkPath x ξ) +
        f (walkPath x ξ (τ (walkPath x ξ))) =
      f x + ∑ n ∈ Finset.range t, (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
        (f (walkPath x ξ (n + 1)) - avg f (walkPath x ξ n)) := by
    intro ξ
    rw [stopped_poisson_telescope f t _ _ (hτt _), walkPath_zero]
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (integrable_const _) hsum, integral_const,
    integral_finsetSum (Finset.range t) (fun n _ => (hinc n).1)]
  simp only [(hinc _).2, Finset.sum_const_zero, add_zero, probReal_univ, one_smul]

theorem avg_translate_field (f : Site d → ℝ) (w x : Site d) :
    avg (fun y => f (y - w)) x = avg f (x - w) := by
  unfold avg LatticeProb.walkOp LatticeProb.nbrSum
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp : x + unit i - w = (x - w) + unit i := by abel
  have hm : x - unit i - w = (x - w) - unit i := by abel
  dsimp only
  rw [hp, hm]

theorem avg_green (hd : 3 ≤ d) (x y : Site d) :
    avg (fun w => green d w y) x = green d x y - (if x = y then 1 else 0) := by
  simp only [External.Sec16.green_eq]
  rw [avg_translate_field]
  simpa only [avg, sub_eq_zero] using LatticeProb.walkOp_srwGreenInf hd (x - y)

theorem summable_heatKernel_transient (hd : 3 ≤ d) (x y : Site d) :
    Summable fun k => heatKernel d k x y := by
  simpa only [External.heatKernel_eq_srwHeat] using LatticeProb.summable_srwHeat hd (x - y)

theorem summable_killedKernel_transient (hd : 3 ≤ d) (D : Set (Site d)) (x y : Site d) :
    Summable fun k => killedKernel D k x y :=
  Summable.of_nonneg_of_le (fun k => killedKernel_nonneg D k x y)
    (fun k => killedKernel_le_heatKernel D k x y) (summable_heatKernel_transient hd x y)

theorem killedGreenPair_single (D : Set (Site d)) (N : ℕ) (x y : Site d) :
    killedGreenPair D N (fun w => if w = y then 1 else 0) x = killedGreenTime D N x y := by
  classical
  rw [killedGreenPair, tsum_eq_single y]
  · simp
  · intro z hz
    simp [hz]

theorem integral_green_at_truncatedExit (hd : 3 ≤ d) (x y : Site d)
    (D : Set (Site d)) (N : ℕ) :
    (∫ X, green d (X (stopBeforeExit D N (fun _ => N) X)) y ∂walkLaw d x) =
      green d x y - killedGreenTime D N x y := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hτ := isWalkStopping_stopBeforeExit (D := D) (isWalkStopping_const N) (fun _ => le_rfl)
  have hτN := stopBeforeExit_le (D := D) (fun _ : ℕ → Site d => le_refl N)
  have hp := integral_stopped_poisson hd1 x (fun w => green d w y) N hτ hτN
  have he : (fun w => green d w y - avg (fun w => green d w y) w) =
      fun w => if w = y then (1 : ℝ) else 0 := by
    funext w
    rw [avg_green hd]
    ring
  rw [he, integral_add (integrable_stoppedScenery_walk hd1 x _ N hτ hτN)
    (integrable_stopped_value hd1 x N (fun _ w => green d w y) hτ hτN),
    integral_stoppedScenery_killed hd1 D N x, killedGreenPair_single] at hp
  linarith

theorem green_nonneg (x y : Site d) : 0 ≤ green d x y :=
  tsum_nonneg fun k => heatKernel_nonneg k x y

theorem green_le_diagonal (hd : 3 ≤ d) (x y : Site d) : green d x y ≤ green d 0 0 := by
  rw [External.Sec16.green_eq, External.Sec16.green_eq, sub_self,
    LatticeProb.srwGreenInf_eq_hitProb_mul hd]
  exact (mul_le_mul_of_nonneg_right (LatticeProb.srwHitProb_le_one (by omega) _)
    (LatticeProb.srwGreenInf_nonneg _)).trans_eq (one_mul _)

theorem killedKernel_eq_graph (D : Set (Site d)) (n : ℕ) (x y : Site d) :
    killedKernel D n x y = LatticeProb.Graph.killedHeat (LatticeProb.lattice d) D n x y := by
  classical
  induction n generalizing x with
  | zero =>
    by_cases hx : x ∈ D
    · simp [killedKernel, LatticeProb.Network.killedHeat_zero, hx]
    · simp [killedKernel, LatticeProb.Network.killedHeat_zero, hx]
  | succ n ih =>
    rw [LatticeProb.Graph.Zd.killedHeat_succ_walkOp]
    by_cases hx : x ∈ D
    · simp only [killedKernel, Set.indicator_of_mem hx, if_pos hx,
        LatticeProb.walkOp, LatticeProb.nbrSum, ih]
    · simp [killedKernel, hx]

theorem killedKernel_symm (hd : 1 ≤ d) (D : Set (Site d)) (n : ℕ) (x y : Site d) :
    killedKernel D n x y = killedKernel D n y x := by
  have h := LatticeProb.Network.killedHeat_reversible (G := LatticeProb.lattice d) D n x y
  simp only [LatticeProb.Graph.Zd.degree_eq] at h
  rw [killedKernel_eq_graph, killedKernel_eq_graph]
  exact mul_left_cancel₀ (by exact_mod_cast (show 2 * d ≠ 0 by omega)) h

theorem killedGreen_symm (hd : 1 ≤ d) (D : Set (Site d)) (x y : Site d) :
    killedGreen D x y = killedGreen D y x :=
  tsum_congr fun k => killedKernel_symm hd D k x y

theorem killedKernel_univ (n : ℕ) (x y : Site d) :
    killedKernel Set.univ n x y = heatKernel d n x y := by
  induction n generalizing x with
  | zero => simp [killedKernel, heatKernel, LatticeProb.LocalCLT.heatKernel]
  | succ n ih => simp [killedKernel, heatKernel, LatticeProb.LocalCLT.heatKernel, ih]

theorem green_symm (hd : 1 ≤ d) (x y : Site d) : green d x y = green d y x := by
  refine tsum_congr fun k => ?_
  rw [← killedKernel_univ, ← killedKernel_univ]
  exact killedKernel_symm hd Set.univ k x y

theorem measure_walk_mem_finset (hd : 1 ≤ d) (x : Site d) (n : ℕ) (C : Finset (Site d)) :
    (walkLaw d x).real {X : ℕ → Site d | X n ∈ C} = ∑ y ∈ C, heatKernel d n x y := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  have hp := integral_pastIn_mul hd Set.univ n x (fun y => if y ∈ C then 1 else 0) 1
    (fun y => by split_ifs <;> norm_num)
  have hl : (fun X : ℕ → Site d => pastIn Set.univ n X * (if X n ∈ C then 1 else 0)) =
      Set.indicator {X : ℕ → Site d | X n ∈ C} (fun _ => (1 : ℝ)) := by
    funext X
    simp [pastIn, Set.indicator]
  have hm : MeasurableSet {X : ℕ → Site d | X n ∈ C} :=
    (measurable_pi_apply n) (Set.to_countable _).measurableSet
  rw [hl, integral_indicator_const (μ := walkLaw d x) (1 : ℝ) hm, smul_eq_mul, mul_one] at hp
  rw [hp, killedPair]
  have he : (fun y => killedKernel Set.univ n x y * (if y ∈ C then (1 : ℝ) else 0)) =
      fun y => if y ∈ C then heatKernel d n x y else 0 := by
    funext y
    simp only [killedKernel_univ]
    split_ifs <;> simp
  rw [he, tsum_eq_sum (s := C) (fun y hy => if_neg hy)]
  exact Finset.sum_congr rfl fun y hy => if_pos hy

/-- In a transient dimension a walk exits every finite set almost surely.
Finite sums of one-time transition probabilities tend to zero. -/
theorem ae_exitTime_ne_top_of_finite (hd : 3 ≤ d) (D : Set (Site d)) (hD : D.Finite)
    (x : Site d) : ∀ᵐ X ∂walkLaw d x, exitTime D X ≠ ⊤ := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  have hlim : Tendsto (fun n : ℕ => (walkLaw d x).real {X : ℕ → Site d | X n ∈ D})
      atTop (𝓝 0) := by
    have he : ∀ n : ℕ, (walkLaw d x).real {X : ℕ → Site d | X n ∈ D} =
        ∑ y ∈ hD.toFinset, heatKernel d n x y := by
      intro n
      simpa only [hD.mem_toFinset] using measure_walk_mem_finset (by omega) x n hD.toFinset
    simp only [he]
    simpa using tendsto_finsetSum _ (fun y _ => (summable_heatKernel_transient hd x y).tendsto_atTop_zero)
  have hle : ∀ n : ℕ, (walkLaw d x).real {X : ℕ → Site d | exitTime D X = ⊤} ≤
      (walkLaw d x).real {X : ℕ → Site d | X n ∈ D} := by
    intro n
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro X hX
    by_contra hnot
    have hex : exitTime D X ≤ (n : ℕ∞) := sInf_le ⟨n, rfl, hnot⟩
    rw [hX] at hex
    exact (ENat.coe_ne_top n) (top_le_iff.mp hex)
  have hz : (walkLaw d x).real {X : ℕ → Site d | exitTime D X = ⊤} = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hle)) (measureReal_nonneg)
  rw [ae_iff]
  simp only [not_not]
  rw [← ofReal_measureReal, hz, ENNReal.ofReal_zero]

theorem stoppedExit_eq_toNat {D : Set (Site d)} {N : ℕ} {X : ℕ → Site d}
    (hX : exitTime D X ≤ (N : ℕ∞)) :
    stopBeforeExit D N (fun _ => N) X = (exitTime D X).toNat := by
  have h := exitTime_le_iff.mp hX
  rw [stopBeforeExit, min_eq_right h, exitTime_eq_exitNat h, ENat.toNat_coe]

/-- The path-space first-passage decomposition of the Green function. -/
theorem integral_green_at_exit (hd : 3 ≤ d) (D : Set (Site d)) (hD : D.Finite)
    (x y : Site d) :
    (∫ X, green d (X (exitTime D X).toNat) y ∂walkLaw d x) =
      green d x y - killedGreen D x y := by
  haveI : NeZero d := ⟨by omega⟩
  set F : ℕ → (ℕ → Site d) → ℝ :=
    fun N X => green d (X (stopBeforeExit D N (fun _ => N) X)) y
  have hFm : ∀ N, AEStronglyMeasurable (F N) (walkLaw d x) := by
    intro N
    exact (integrable_stopped_value (by omega) x N (fun _ w => green d w y)
      (isWalkStopping_stopBeforeExit (D := D) (isWalkStopping_const N) (fun _ => le_rfl))
      (stopBeforeExit_le (fun _ : ℕ → Site d => le_refl N))).aestronglyMeasurable
  have hb : ∀ N, ∀ᵐ X ∂walkLaw d x, ‖F N X‖ ≤ green d 0 0 := by
    intro N
    exact Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (green_nonneg _ _)]
      exact green_le_diagonal hd _ _
  have hlim : ∀ᵐ X ∂walkLaw d x,
      Tendsto (fun N => F N X) atTop (𝓝 (green d (X (exitTime D X).toNat) y)) := by
    filter_upwards [ae_exitTime_ne_top_of_finite hd D hD x] with X hX
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hX
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k] with N hN
    have hle : exitTime D X ≤ (N : ℕ∞) := by rw [← hk]; exact_mod_cast hN
    simp only [F, stoppedExit_eq_toNat hle]
  have hI := tendsto_integral_of_dominated_convergence (μ := walkLaw d x) (F := F)
    (f := fun X => green d (X (exitTime D X).toNat) y) (fun _ => green d 0 0)
    hFm (integrable_const _) hb hlim
  have hg : Tendsto (fun N : ℕ => green d x y - killedGreenTime D N x y)
      atTop (𝓝 (green d x y - killedGreen D x y)) :=
    tendsto_const_nhds.sub (summable_killedKernel_transient hd D x y).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hI (hg.congr fun N => (integral_green_at_truncatedExit hd x y D N).symm)

theorem measurable_exit_site (D : Set (Site d)) :
    Measurable (fun X : ℕ → Site d => X (exitTime D X).toNat) := by
  have ht : Measurable (fun X : ℕ → Site d => (exitTime D X).toNat) :=
    LatticeProb.Graph.measurable_exitNat D
  have heval : Measurable (fun q : (ℕ → Site d) × ℕ => q.1 q.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  exact heval.comp (measurable_id.prodMk ht)

theorem integrable_green_at_exit (hd : 3 ≤ d) (D : Set (Site d)) (x y : Site d) :
    Integrable (fun X : ℕ → Site d => green d (X (exitTime D X).toNat) y) (walkLaw d x) := by
  haveI : NeZero d := ⟨by omega⟩
  refine (integrable_const (green d 0 0)).mono'
    ((measurable_of_countable (fun w => green d w y)).comp
      (measurable_exit_site D)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun X => by
    rw [Real.norm_eq_abs, abs_of_nonneg (green_nonneg _ _)]
    exact green_le_diagonal hd _ _

theorem exitTime_toNat_notMem {D : Set (Site d)} {X : ℕ → Site d}
    (hX : exitTime D X ≠ ⊤) : X (exitTime D X).toNat ∉ D := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hX
  have hk' : exitTime D X ≤ (k : ℕ∞) := by rw [← hk]
  have hn := exitTime_le_iff.mp hk'
  rw [exitTime_eq_exitNat hn, ENat.toNat_coe]
  exact notMem_exitNat hn

/-- Reversibility transfers an exit average to a walk started at its target. -/
theorem integral_green_at_exit_symm (hd : 3 ≤ d) (D : Set (Site d)) (hD : D.Finite)
    (x y : Site d) :
    (∫ X, green d (X (exitTime D X).toNat) y ∂walkLaw d x) =
      ∫ X, green d (X (exitTime D X).toNat) x ∂walkLaw d y := by
  rw [integral_green_at_exit hd D hD, integral_green_at_exit hd D hD,
    green_symm (by omega) x y, killedGreen_symm (by omega) D x y]

theorem integral_green_at_exit_le_of_outside (hd : 3 ≤ d) (D : Set (Site d)) (hD : D.Finite)
    (x y : Site d) (M : ℝ) (hout : ∀ w ∉ D, green d w x ≤ M) :
    (∫ X, green d (X (exitTime D X).toNat) y ∂walkLaw d x) ≤ M := by
  haveI : NeZero d := ⟨by omega⟩
  rw [integral_green_at_exit_symm hd D hD x y]
  have h := integral_mono_ae (integrable_green_at_exit hd D y x) (integrable_const M) ?_
  · simpa using h
  · filter_upwards [ae_exitTime_ne_top_of_finite hd D hD y] with X hX
    exact hout _ (exitTime_toNat_notMem hX)

theorem finite_real_cube (x : Site d) (r : ℕ) :
    {y : Site d | ∀ i, |(y i : ℝ) - (x i : ℝ)| ≤ r}.Finite := by
  have he : {y : Site d | ∀ i, |(y i : ℝ) - (x i : ℝ)| ≤ r} =
      (boxFinset x r : Set (Site d)) := by
    ext y
    simp only [Finset.mem_coe, mem_boxFinset_iff, Set.mem_setOf_eq]
    exact (boxDist_le_iff_real_coords x y r).symm
  rw [he]
  exact Finset.finite_toSet _

end Sandpile
