import Sandpile.Support.LimPathHit

/-!
# Transferring the ball-stopped reward across motions

The law of the stopped state of a ball-exit rule depends only on the law of the
motion, hence not on the starting point beyond the translation, nor on the space.

The expected reward at the exit from a ball, truncated at a horizon, is approximated
by discretizing the exit time on the dyadic grid of `[0,T]`.  The discretized reward
is a bounded measurable function OF THE PATH — the discretized time is the grid time
whose index counts the grid points the path has not yet used to leave the ball, and
that count is a finite sum of indicators of the events `pathHit` — so its expectation
depends only on the law of the centred path, which is the same for every motion
(`map_centredPath_eq`).  Letting the resolution grow and using the continuity of the
reward and of the paths gives the same for the undiscretized reward.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum
open scoped ENNReal NNReal

namespace Sandpile.Support

open Classical in
/-- The `j`-th point of the dyadic grid of `[0,T]` at resolution `n`. -/
noncomputable def gridTime (T : ℝ≥0) (n j : ℕ) : ℝ≥0 := T * j / 2 ^ n

/-- Grid times are monotone in the grid index. -/
theorem gridTime_mono (T : ℝ≥0) (n : ℕ) {j k : ℕ} (h : j ≤ k) :
    gridTime T n j ≤ gridTime T n k := by
  have hjk : (j : ℝ≥0) ≤ (k : ℝ≥0) := by exact_mod_cast h
  unfold gridTime
  gcongr

/-- The grid time at an index within the resolution `2^n` does not exceed the horizon `T`. -/
theorem gridTime_le (T : ℝ≥0) (n : ℕ) {j : ℕ} (h : j ≤ 2 ^ n) : gridTime T n j ≤ T := by
  unfold gridTime
  rw [div_le_iff₀ (by positivity)]
  have hjk : (j : ℝ≥0) ≤ ((2 ^ n : ℕ) : ℝ≥0) := by exact_mod_cast h
  calc T * (j : ℝ≥0) ≤ T * ((2 ^ n : ℕ) : ℝ≥0) := by gcongr
    _ = T * 2 ^ n := by push_cast; ring

/-- Consecutive grid points differ by one mesh width `T / 2^n`. -/
theorem gridTime_succ (T : ℝ≥0) (n j : ℕ) :
    gridTime T n (j + 1) = gridTime T n j + T / 2 ^ n := by
  unfold gridTime
  push_cast
  rw [mul_add, mul_one, add_div]

/-- Grid times at resolution `n` are injective in the index, provided the horizon `T` is
nonzero: the grid spacing `T / 2^n` is nonzero, so distinct indices give distinct points. -/
theorem gridTime_injOn (T : ℝ≥0) (hT : T ≠ 0) (n : ℕ) {j k : ℕ}
    (h : gridTime T n j = gridTime T n k) : j = k := by
  unfold gridTime at h
  have h2 : ((2 : ℝ≥0) ^ n) ≠ 0 := by positivity
  have hTpos : (0 : ℝ≥0) < T := pos_iff_ne_zero.mpr hT
  have h4 := congrArg (fun z : ℝ≥0 => z * (2 : ℝ≥0) ^ n) h
  simp only [div_mul_cancel₀ _ h2] at h4
  have hj : (j : ℝ≥0) = (k : ℝ≥0) := mul_left_cancel₀ hTpos.ne' h4
  exact_mod_cast hj

section

variable {d : ℕ}

open Classical in
/-- The number of grid points at which the path has not yet reached distance `s`. -/
noncomputable def gridCount (d : ℕ) (s : ℝ) (T : ℝ≥0) (n : ℕ) (ξ : ℝ≥0 → Space d) : ℕ :=
  ((Finset.range (2 ^ n)).filter (fun k => ξ ∉ pathHit d s (gridTime T n k))).card

/-- The exit time of the path, discretized on the grid and capped at the horizon. -/
noncomputable def gridStop (d : ℕ) (s : ℝ) (T : ℝ≥0) (n : ℕ) (ξ : ℝ≥0 → Space d) : ℝ≥0 :=
  gridTime T n (gridCount d s T n ξ)

/-- The grid count never exceeds the total number of grid points `2^n`, being the
cardinality of a filtered subset of `Finset.range (2^n)`. -/
theorem gridCount_le (d : ℕ) (s : ℝ) (T : ℝ≥0) (n : ℕ) (ξ : ℝ≥0 → Space d) :
    gridCount d s T n ξ ≤ 2 ^ n := by
  classical
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

/-- The grid points the path has not used form an initial segment. -/
theorem gridCount_down (d : ℕ) (s : ℝ) (T : ℝ≥0) (n : ℕ) (ξ : ℝ≥0 → Space d)
    {j k : ℕ} (hjk : j ≤ k) (hk : ξ ∉ pathHit d s (gridTime T n k)) :
    ξ ∉ pathHit d s (gridTime T n j) :=
  fun h => hk (pathHit_mono d s (gridTime_mono T n hjk) h)

/-- Every grid index below the grid count is itself an unused grid point: a converse
direction to `gridCount_down`, proved by a cardinality argument on the finset of unused
indices below `2^n`. -/
theorem not_mem_pathHit_of_lt_gridCount (d : ℕ) (s : ℝ) (T : ℝ≥0) (n : ℕ)
    (ξ : ℝ≥0 → Space d) {j : ℕ} (hj : j < gridCount d s T n ξ) :
    ξ ∉ pathHit d s (gridTime T n j) := by
  classical
  by_contra hmem
  set S := (Finset.range (2 ^ n)).filter (fun k => ξ ∉ pathHit d s (gridTime T n k)) with hS
  have hsub : S ⊆ Finset.range j := by
    intro k hk
    rw [hS, Finset.mem_filter] at hk
    rw [Finset.mem_range]
    by_contra hkj
    exact hk.2 (pathHit_mono d s (gridTime_mono T n (not_lt.mp hkj)) hmem)
  have hcard : gridCount d s T n ξ = S.card := rfl
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_range] at h2
  omega

/-- If the grid count is below the full resolution `2^n`, the path HAS used the grid
point right at the grid count: the point where the "not yet used" count stops counting
is itself a used point, by a pigeonhole/cardinality argument dual to
`not_mem_pathHit_of_lt_gridCount`. -/
theorem mem_pathHit_gridCount (d : ℕ) (s : ℝ) (T : ℝ≥0) (n : ℕ) (ξ : ℝ≥0 → Space d)
    (h : gridCount d s T n ξ < 2 ^ n) :
    ξ ∈ pathHit d s (gridTime T n (gridCount d s T n ξ)) := by
  classical
  by_contra hmem
  set c := gridCount d s T n ξ with hc
  set S := (Finset.range (2 ^ n)).filter (fun k => ξ ∉ pathHit d s (gridTime T n k)) with hS
  have hsub : Finset.range (c + 1) ⊆ S := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [hS, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, gridCount_down d s T n ξ (by omega : k ≤ c) hmem⟩
  have hcard : c = S.card := rfl
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_range] at h2
  omega

end

section

variable {Ω : Type*} {d : ℕ} {B : ℝ≥0 → Ω → Space d} {x : Space d} {s : ℝ}

/-- The discretized time is at least the truncated exit time. -/
theorem exitTimeTrunc_le_gridStop (hc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) :
    LatticeProb.exitTimeTrunc B x s T ω ≤ gridStop d s T n (fun t => B t ω - x) := by
  classical
  rcases eq_or_lt_of_le (gridCount_le d s T n (fun t => B t ω - x)) with heq | hlt
  · have hval : gridStop d s T n (fun t => B t ω - x) = T := by
      rw [gridStop, heq]
      unfold gridTime
      rw [mul_comm]
      have h2 : ((2 : ℝ≥0) ^ n) ≠ 0 := by positivity
      rw [show ((2 ^ n : ℕ) : ℝ≥0) = (2 : ℝ≥0) ^ n by push_cast; ring]
      field_simp
    rw [hval]
    have h : ((LatticeProb.exitTimeTrunc B x s T ω : ℝ≥0) : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by
      rw [LatticeProb.coe_exitTimeTrunc]
      exact inf_le_right
    exact_mod_cast h
  · have hmem := mem_pathHit_gridCount d s T n (fun t => B t ω - x) hlt
    have hle : LatticeProb.exitTime B x s ω
        ≤ ((gridTime T n (gridCount d s T n (fun t => B t ω - x)) : ℝ≥0) : ℝ≥0∞) :=
      (mem_pathHit_centredPath hc _ ω).mp hmem
    have h2 : ((LatticeProb.exitTimeTrunc B x s T ω : ℝ≥0) : ℝ≥0∞)
        ≤ ((gridTime T n (gridCount d s T n (fun t => B t ω - x)) : ℝ≥0) : ℝ≥0∞) := by
      rw [LatticeProb.coe_exitTimeTrunc]
      exact le_trans inf_le_left hle
    rw [gridStop]
    exact_mod_cast h2

/-- The discretized time overshoots the truncated exit time by at most one mesh. -/
theorem gridStop_le_exitTimeTrunc_add (hc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) :
    gridStop d s T n (fun t => B t ω - x)
      ≤ LatticeProb.exitTimeTrunc B x s T ω + T / 2 ^ n := by
  classical
  have hcle := gridCount_le d s T n (fun t => B t ω - x)
  rcases Nat.eq_zero_or_pos (gridCount d s T n (fun t => B t ω - x)) with hc0 | hc1
  · have hval : gridStop d s T n (fun t => B t ω - x) = 0 := by
      rw [gridStop, hc0]
      unfold gridTime
      simp
    rw [hval]
    exact zero_le
  · obtain ⟨m, hm⟩ : ∃ m, gridCount d s T n (fun t => B t ω - x) = m + 1 :=
      ⟨gridCount d s T n (fun t => B t ω - x) - 1, by omega⟩
    have hnot : (fun t => B t ω - x) ∉ pathHit d s (gridTime T n m) :=
      not_mem_pathHit_of_lt_gridCount d s T n (fun t => B t ω - x) (by omega)
    have hgt : ((gridTime T n m : ℝ≥0) : ℝ≥0∞) < LatticeProb.exitTime B x s ω := by
      by_contra hle
      exact hnot ((mem_pathHit_centredPath hc (gridTime T n m) ω).mpr (not_lt.mp hle))
    have hmT : gridTime T n m ≤ T := gridTime_le T n (by omega)
    have hle2 : ((gridTime T n m : ℝ≥0) : ℝ≥0∞)
        ≤ ((LatticeProb.exitTimeTrunc B x s T ω : ℝ≥0) : ℝ≥0∞) := by
      rw [LatticeProb.coe_exitTimeTrunc]
      exact le_inf hgt.le (by exact_mod_cast hmT)
    have hle3 : gridTime T n m ≤ LatticeProb.exitTimeTrunc B x s T ω := by exact_mod_cast hle2
    rw [gridStop, hm, gridTime_succ]
    gcongr

end


section Payoff

variable {d : ℕ}

open Classical in
/-- The reward at the discretized stopped state, read off the path. -/
noncomputable def gridPayoff (d : ℕ) (s : ℝ) (T : ℝ≥0) (n : ℕ) (F : ℝ≥0 × Space d → ℝ)
    (ξ : ℝ≥0 → Space d) : ℝ :=
  ∑ j ∈ Finset.range (2 ^ n + 1),
    if gridStop d s T n ξ = gridTime T n j then F (gridTime T n j, ξ (gridTime T n j)) else 0

/-- The grid count is measurable, rewritten as a finite sum of `if`/`then`/`else`
indicators of the measurable sets `pathHit d s (gridTime T n k)`. -/
theorem measurable_gridCount (d : ℕ) (s : ℝ) (T : ℝ≥0) (n : ℕ) :
    Measurable (gridCount d s T n) := by
  classical
  have hEq : gridCount d s T n = fun ξ : ℝ≥0 → Space d =>
      ∑ k ∈ Finset.range (2 ^ n), if ξ ∉ pathHit d s (gridTime T n k) then 1 else 0 := by
    funext ξ
    rw [gridCount, Finset.card_filter]
  rw [hEq]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact Measurable.ite (measurableSet_pathHit d s (gridTime T n k)).compl
    measurable_const measurable_const

/-- The discretized stopping time is measurable, as the composite of the measurable
grid count and the (finitely many values, hence measurable) function `gridTime T n`. -/
theorem measurable_gridStop (d : ℕ) (s : ℝ) (T : ℝ≥0) (n : ℕ) :
    Measurable (gridStop d s T n) :=
  (measurable_from_top (f := gridTime T n)).comp (measurable_gridCount d s T n)

/-- The discretized reward is measurable, as a finite sum of `if`/`then`/`else` terms
each measurable in the path. -/
theorem measurable_gridPayoff (d : ℕ) (s : ℝ) (T : ℝ≥0) (n : ℕ) {F : ℝ≥0 × Space d → ℝ}
    (hF : Measurable F) : Measurable (gridPayoff d s T n F) := by
  classical
  refine Finset.measurable_sum _ fun j _ => ?_
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurable_gridStop d s T n) (measurableSet_singleton (gridTime T n j))
  · exact hF.comp (measurable_const.prodMk (measurable_pi_apply (gridTime T n j)))

/-- The sum defining `gridPayoff` collapses to its single nonzero term, the reward read
off at the discretized stopped time and position, using injectivity of grid times
(`gridTime_injOn`, which needs `T ≠ 0`). -/
theorem gridPayoff_eq {T : ℝ≥0} (hT : T ≠ 0) (s : ℝ) (n : ℕ) (F : ℝ≥0 × Space d → ℝ)
    (ξ : ℝ≥0 → Space d) :
    gridPayoff d s T n F ξ = F (gridStop d s T n ξ, ξ (gridStop d s T n ξ)) := by
  classical
  have hmem : gridCount d s T n ξ ∈ Finset.range (2 ^ n + 1) :=
    Finset.mem_range.mpr (by have := gridCount_le d s T n ξ; omega)
  rw [gridPayoff, Finset.sum_eq_single_of_mem _ hmem]
  · simp [gridStop]
  · intro j _ hj
    refine if_neg fun hcon => ?_
    exact hj (gridTime_injOn T hT n hcon).symm

end Payoff


section Limit

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The mesh width `T / 2^n` tends to `0` as the resolution `n` grows. -/
theorem tendsto_div_pow_two (T : ℝ≥0) : Tendsto (fun n : ℕ => T / 2 ^ n) atTop (𝓝 0) := by
  rw [← NNReal.tendsto_coe]
  push_cast
  have h : Tendsto (fun n : ℕ => (T : ℝ) * (1 / 2 : ℝ) ^ n) atTop (𝓝 ((T : ℝ) * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  rw [div_pow, one_pow]
  ring

omit [MeasurableSpace Ω] in
/-- The discretized stopping time converges to the truncated exit time. -/
theorem tendsto_gridStop {B : ℝ≥0 → Ω → Space d} {x : Space d} {s : ℝ}
    (hc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => gridStop d s T n (fun t => B t ω - x)) atTop
      (𝓝 (LatticeProb.exitTimeTrunc B x s T ω)) := by
  have hup : Tendsto (fun n : ℕ => LatticeProb.exitTimeTrunc B x s T ω + T / 2 ^ n) atTop
      (𝓝 (LatticeProb.exitTimeTrunc B x s T ω)) := by
    have h : Tendsto (fun n : ℕ => LatticeProb.exitTimeTrunc B x s T ω + T / 2 ^ n) atTop
        (𝓝 (LatticeProb.exitTimeTrunc B x s T ω + 0)) :=
      (tendsto_const_nhds (x := LatticeProb.exitTimeTrunc B x s T ω)).add
        (tendsto_div_pow_two T)
    rwa [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => exitTimeTrunc_le_gridStop hc T n ω)
    (fun n => gridStop_le_exitTimeTrunc_add hc T n ω)

/-- The discretized rewards converge to the reward at the stopped state. -/
theorem tendsto_integral_gridPayoff (P : Measure Ω) [IsProbabilityMeasure P]
    {y : Space d} {C : ℝ≥0 → Ω → Space d} (hmS : ∀ t, StronglyMeasurable (C t))
    (hc : ∀ ω, Continuous fun t => C t ω) {s : ℝ} {T : ℝ≥0} (hT : T ≠ 0)
    {F : ℝ≥0 × Space d → ℝ} (hFc : Continuous F) {M : ℝ} (hFb : ∀ p, |F p| ≤ M) :
    Tendsto (fun n => ∫ ω, gridPayoff d s T n F (fun t => C t ω - y) ∂P) atTop
      (𝓝 (∫ ω, F (LatticeProb.exitTimeTrunc C y s T ω,
        C (LatticeProb.exitTimeTrunc C y s T ω) ω - y) ∂P)) := by
  have hpath : Measurable (fun ω => (fun t => C t ω - y) : Ω → (ℝ≥0 → Space d)) :=
    measurable_pi_lambda _ fun t => (hmS t).measurable.sub measurable_const
  refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun n => ?_)
    (integrable_const M) (fun n => ?_) ?_
  · exact (((measurable_gridPayoff d s T n hFc.measurable).comp hpath)).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, gridPayoff_eq hT]
    exact hFb _
  · filter_upwards with ω
    have hstop := tendsto_gridStop (B := C) (x := y) (s := s) hc T ω
    have hval : Tendsto (fun n => (gridStop d s T n (fun t => C t ω - y),
        C (gridStop d s T n (fun t => C t ω - y)) ω - y)) atTop
        (𝓝 (LatticeProb.exitTimeTrunc C y s T ω,
          C (LatticeProb.exitTimeTrunc C y s T ω) ω - y)) := by
      refine Tendsto.prodMk_nhds hstop ?_
      exact (((hc ω).sub continuous_const).tendsto _).comp hstop
    have hlim := (hFc.tendsto _).comp hval
    refine hlim.congr fun n => ?_
    rw [gridPayoff_eq hT]
    rfl

end Limit

section Transfer

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'} [IsProbabilityMeasure Q]
  {x x' : Space d} {B : ℝ≥0 → Ω → Space d} {B' : ℝ≥0 → Ω' → Space d}

/-- The centred path at the starting point has the same law for two motions. -/
theorem map_centredPath_start_eq (hB : IsBrownian d x B P) (hB' : IsBrownian d x' B' Q)
    (hm : ∀ t, Measurable (B t)) (hm' : ∀ t, Measurable (B' t)) :
    P.map (fun ω (t : ℝ≥0) => B t ω - x) = Q.map (fun ω (t : ℝ≥0) => B' t ω - x') := by
  have h1 : P.map (fun ω (t : ℝ≥0) => B t ω - x)
      = P.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω) := by
    refine Measure.map_congr ?_
    filter_upwards [hB.start] with ω hω
    funext t
    rw [hω]
  have h2 : Q.map (fun ω (t : ℝ≥0) => B' t ω - x')
      = Q.map (fun ω (t : ℝ≥0) => B' t ω - B' 0 ω) := by
    refine Measure.map_congr ?_
    filter_upwards [hB'.start] with ω hω
    funext t
    rw [hω]
  rw [h1, h2, map_centredPath_eq hB hB' hm hm']

/-- The discretized reward has the same expectation for two motions. -/
theorem integral_gridPayoff_eq (hB : IsBrownian d x B P) (hB' : IsBrownian d x' B' Q)
    (hm : ∀ t, Measurable (B t)) (hm' : ∀ t, Measurable (B' t)) (s : ℝ) (T : ℝ≥0) (n : ℕ)
    {F : ℝ≥0 × Space d → ℝ} (hF : Measurable F) :
    (∫ ω, gridPayoff d s T n F (fun t => B t ω - x) ∂P)
      = ∫ ω, gridPayoff d s T n F (fun t => B' t ω - x') ∂Q := by
  have hpath : Measurable (fun ω => (fun t => B t ω - x) : Ω → (ℝ≥0 → Space d)) :=
    measurable_pi_lambda _ fun t => (hm t).sub measurable_const
  have hpath' : Measurable (fun ω => (fun t => B' t ω - x') : Ω' → (ℝ≥0 → Space d)) :=
    measurable_pi_lambda _ fun t => (hm' t).sub measurable_const
  have hg := measurable_gridPayoff d s T n hF
  rw [← integral_map hpath.aemeasurable hg.aestronglyMeasurable,
    ← integral_map hpath'.aemeasurable hg.aestronglyMeasurable,
    map_centredPath_start_eq hB hB' hm hm']

/-- **The expected reward at the ball-stopped state depends only on the law of the motion.**
Two Brownian motions, on two spaces and started at two points, give the same expectation of
any bounded continuous reward evaluated at the time they leave the ball of radius `s` about
their own starting point, truncated at the horizon, and at their displacement there. -/
theorem integral_stoppedState_eq (hB : IsBrownian d x B P) (hB' : IsBrownian d x' B' Q)
    (hmS : ∀ t, StronglyMeasurable (B t)) (hmS' : ∀ t, StronglyMeasurable (B' t))
    (hc : ∀ ω, Continuous fun t => B t ω) (hc' : ∀ ω, Continuous fun t => B' t ω)
    {s : ℝ} {T : ℝ≥0} (hT : T ≠ 0) {F : ℝ≥0 × Space d → ℝ} (hFc : Continuous F)
    {M : ℝ} (hFb : ∀ p, |F p| ≤ M) :
    (∫ ω, F (LatticeProb.exitTimeTrunc B x s T ω,
        B (LatticeProb.exitTimeTrunc B x s T ω) ω - x) ∂P)
      = ∫ ω, F (LatticeProb.exitTimeTrunc B' x' s T ω,
        B' (LatticeProb.exitTimeTrunc B' x' s T ω) ω - x') ∂Q := by
  have h1 := tendsto_integral_gridPayoff P hmS hc hT hFc hFb (y := x) (s := s)
  have h2 := tendsto_integral_gridPayoff Q hmS' hc' hT hFc hFb (y := x') (s := s)
  refine tendsto_nhds_unique h1 ?_
  refine h2.congr fun n => ?_
  exact (integral_gridPayoff_eq hB hB' (fun t => (hmS t).measurable)
    (fun t => (hmS' t).measurable) s T n hFc.measurable).symm

end Transfer

end Sandpile.Support
