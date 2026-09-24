/-
The ball-stopped field is continuous in the plane point.

This is not structural.  The family of motions `B` is arbitrary, so the motions
`B (planePoint u)` and `B (planePoint v)` started at two nearby points need have
nothing to do with each other, and the expected reward at the exit from the ball
is a priori an arbitrary function of `u`.  It is continuous because the expected
reward depends only on the LAW of the motion
(`Sandpile.Support.integral_stoppedState_eq`): the expectation at `u` may be
computed along ONE motion, the one started at a fixed base point, with the whole
dependence on `u` moved into the reward, where it is the continuity of the heat
potential in space.

The reward has to be made bounded before the transfer can be applied, and that is
where the stopped position is used: the motion has not left the ball of radius `s`
when it is stopped (`norm_stopped_le`), so multiplying the reward by a cutoff which
is one on that ball changes nothing.
-/
import Sandpile.Support.LimStoppedTransfer
import Sandpile.Support.LimStoppedKernel

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal

namespace Sandpile.Support

/-! ### A continuous cutoff of the ball -/

/-- A continuous function which is one on the ball of radius `s` and vanishes outside the
ball of radius `s + 1`. -/
noncomputable def ballCutoff {d : ℕ} (s : ℝ) (z : Space d) : ℝ :=
  max 0 (min 1 (s + 1 - ‖z‖))

theorem continuous_ballCutoff (d : ℕ) (s : ℝ) : Continuous (ballCutoff (d := d) s) := by
  unfold ballCutoff
  fun_prop

theorem ballCutoff_eq_one {d : ℕ} {s : ℝ} {z : Space d} (h : ‖z‖ ≤ s) :
    ballCutoff s z = 1 := by
  unfold ballCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem ballCutoff_eq_zero {d : ℕ} {s : ℝ} {z : Space d} (h : s + 1 ≤ ‖z‖) :
    ballCutoff s z = 0 := by
  unfold ballCutoff
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

theorem ballCutoff_nonneg {d : ℕ} (s : ℝ) (z : Space d) : 0 ≤ ballCutoff s z :=
  le_max_left _ _

theorem ballCutoff_le_one {d : ℕ} (s : ℝ) (z : Space d) : ballCutoff s z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-! ### The stopped motion has not left the ball -/

/-- **The stopped position is in the closed ball.**  If the motion were outside the ball at
the stopping time, continuity would put it outside at a strictly earlier time, and the exit
time would be smaller than the stopping time, which it is not. -/
theorem norm_stopped_le {Ω : Type*} {d : ℕ} {B : ℝ≥0 → Ω → Space d} {x : Space d}
    (hc : ∀ ω, Continuous fun t => B t ω) {s : ℝ} (hs : 0 ≤ s) (T : ℝ≥0) (ω : Ω)
    (h0 : B 0 ω = x) :
    ‖B (LatticeProb.exitTimeTrunc B x s T ω) ω - x‖ ≤ s := by
  set τ := LatticeProb.exitTimeTrunc B x s T ω with hτ
  by_contra hcon
  rw [not_le] at hcon
  have hg : Continuous fun t : ℝ≥0 => ‖B t ω - x‖ := ((hc ω).sub continuous_const).norm
  rcases eq_or_lt_of_le (zero_le (a := τ)) with h0τ | h0τ
  · rw [← h0τ] at hcon
    rw [h0, sub_self, norm_zero] at hcon
    linarith
  · obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (hg.continuousAt (x := τ))
      (‖B τ ω - x‖ - s) (by linarith)
    set t : ℝ≥0 := τ - Real.toNNReal (δ / 2) with htdef
    have hδ2 : (0 : ℝ≥0) < Real.toNNReal (δ / 2) := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by positivity)]
      simpa using half_pos hδ
    have htτ : t < τ := tsub_lt_self h0τ hδ2
    have hdist : dist t τ < δ := by
      have hle : (t : ℝ) ≤ (τ : ℝ) := by exact_mod_cast htτ.le
      have hge : (τ : ℝ) - δ / 2 ≤ (t : ℝ) := by
        rcases le_total (τ : ℝ≥0) (Real.toNNReal (δ / 2)) with h | h
        · have : t = 0 := by
            rw [htdef]
            exact tsub_eq_zero_of_le h
          rw [this]
          have : (τ : ℝ) ≤ δ / 2 := by
            have := h
            rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)] at this
            exact this
          simp only [NNReal.coe_zero]
          linarith
        · rw [htdef, NNReal.coe_sub h, Real.coe_toNNReal _ (by positivity)]
      rw [NNReal.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
    have h1 := hball hdist
    rw [Real.dist_eq, abs_lt] at h1
    have h2 : s ≤ ‖B t ω - x‖ := by linarith [h1.1]
    have h3 : LatticeProb.exitTime B x s ω ≤ (t : ℝ≥0∞) :=
      (LatticeProb.exitTime_le_iff hc x s ω t).mpr ⟨t, le_rfl, h2⟩
    have h4 : ((τ : ℝ≥0) : ℝ≥0∞) ≤ LatticeProb.exitTime B x s ω := by
      rw [hτ, LatticeProb.coe_exitTimeTrunc]
      exact inf_le_left
    have h5 : τ ≤ t := by exact_mod_cast le_trans h4 h3
    exact absurd htτ (not_lt.mpr h5)

/-! ### The reward of the stopped rule, as a bounded continuous function of the state -/

/-- The reward the ball-stopped field integrates, cut off outside the ball so that it is a
bounded continuous function of the stopped state. -/
noncomputable def stoppedReward {ΩW : Type*} (d : ℕ) (Z : ℝ → Space d → ΩW → ℝ) (ω : ΩW)
    (s T : ℝ) (u : Space 2) (p : ℝ≥0 × Space d) : ℝ :=
  -Z (T - min (p.1 : ℝ) T) (p.2 + planePoint u) ω * ballCutoff s p.2

theorem continuous_stoppedReward {ΩW : Type*} {d : ℕ} {Z : ℝ → Space d → ΩW → ℝ} {ω : ΩW}
    {T : ℝ} (hT : 0 ≤ T)
    (hZω : ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (s : ℝ) (u : Space 2) : Continuous (stoppedReward d Z ω s T u) := by
  have hmap : Continuous fun p : ℝ≥0 × Space d => ((T - min (p.1 : ℝ) T), p.2 + planePoint u) := by
    fun_prop
  have hmem : ∀ p : ℝ≥0 × Space d,
      ((T - min (p.1 : ℝ) T), p.2 + planePoint u) ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)) := by
    intro p
    refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
    · have : min (p.1 : ℝ) T ≤ T := min_le_right _ _
      linarith
    · have : (0 : ℝ) ≤ min (p.1 : ℝ) T := le_min p.1.coe_nonneg hT
      linarith
  have h1 : Continuous fun p : ℝ≥0 × Space d => Z (T - min (p.1 : ℝ) T) (p.2 + planePoint u) ω :=
    (hZω.comp_continuous hmap hmem)
  unfold stoppedReward
  exact (h1.neg).mul ((continuous_ballCutoff d s).comp continuous_snd)


theorem continuous_planePoint (d : ℕ) : Continuous (planePoint (d := d)) := by
  unfold planePoint
  refine (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp ?_
  refine continuous_pi fun i => ?_
  by_cases h : (i : ℕ) < 2
  · simp only [dif_pos h]
    exact (EuclideanSpace.proj (⟨(i : ℕ), h⟩ : Fin 2)).continuous
  · simp only [dif_neg h]
    exact continuous_const

/-- The reward is continuous in the plane point as well. -/
theorem continuous_stoppedReward_point {ΩW : Type*} {d : ℕ} {Z : ℝ → Space d → ΩW → ℝ}
    {ω : ΩW} {T : ℝ} (hT : 0 ≤ T)
    (hZω : ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (s : ℝ) (p : ℝ≥0 × Space d) :
    Continuous fun u : Space 2 => stoppedReward d Z ω s T u p := by
  have hmap : Continuous fun u : Space 2 => ((T - min (p.1 : ℝ) T), p.2 + planePoint u) := by
    exact continuous_const.prodMk (continuous_const.add (continuous_planePoint d))
  have hmem : ∀ u : Space 2, ((T - min (p.1 : ℝ) T), p.2 + planePoint u)
      ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)) := by
    intro u
    refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
    · have : min (p.1 : ℝ) T ≤ T := min_le_right _ _
      linarith
    · have : (0 : ℝ) ≤ min (p.1 : ℝ) T := le_min p.1.coe_nonneg hT
      linarith
  have h1 : Continuous fun u : Space 2 => Z (T - min (p.1 : ℝ) T) (p.2 + planePoint u) ω :=
    hZω.comp_continuous hmap hmem
  unfold stoppedReward
  exact h1.neg.mul continuous_const

/-- A bound on the reward, uniform over the plane points of a bounded set. -/
theorem exists_bound_stoppedReward {ΩW : Type*} {d : ℕ} {Z : ℝ → Space d → ΩW → ℝ} {ω : ΩW}
    {T : ℝ} (hT : 0 ≤ T)
    (hZω : ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (s : ℝ) (u₀ : Space 2) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : Space 2, ‖planePoint (d := d) u - planePoint (d := d) u₀‖ ≤ R →
      ∀ p : ℝ≥0 × Space d, |stoppedReward d Z ω s T u p| ≤ M := by
  set K : Set (ℝ × Space d) :=
    Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall (planePoint (d := d) u₀) (s + 1 + R) with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKsub : K ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)) :=
    Set.prod_mono (subset_refl _) (Set.subset_univ _)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hZω.mono hKsub)
  refine ⟨max C 0, le_max_right _ _, fun u hu p => ?_⟩
  by_cases hp : s + 1 ≤ ‖p.2‖
  · rw [stoppedReward, ballCutoff_eq_zero hp, mul_zero, abs_zero]
    exact le_max_right _ _
  · have hmem : ((T - min (p.1 : ℝ) T), p.2 + planePoint (d := d) u) ∈ K := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have : min (p.1 : ℝ) T ≤ T := min_le_right _ _
        linarith
      · have : (0 : ℝ) ≤ min (p.1 : ℝ) T := le_min p.1.coe_nonneg hT
        linarith
      · rw [Metric.mem_closedBall, dist_eq_norm]
        have hsplit : p.2 + planePoint (d := d) u - planePoint (d := d) u₀
            = p.2 + (planePoint (d := d) u - planePoint (d := d) u₀) := by abel
        rw [hsplit]
        calc ‖p.2 + (planePoint (d := d) u - planePoint (d := d) u₀)‖
            ≤ ‖p.2‖ + ‖planePoint (d := d) u - planePoint (d := d) u₀‖ := norm_add_le _ _
          _ ≤ (s + 1) + R := by
              have := not_le.mp hp
              linarith
          _ = s + 1 + R := by ring
    have hZle : |Z (T - min (p.1 : ℝ) T) (p.2 + planePoint (d := d) u) ω| ≤ C := by
      have := hC _ hmem
      rwa [Real.norm_eq_abs] at this
    rw [stoppedReward, abs_mul, abs_neg]
    calc |Z (T - min (p.1 : ℝ) T) (p.2 + planePoint (d := d) u) ω| * |ballCutoff s p.2|
        ≤ C * 1 := by
          refine mul_le_mul hZle ?_ (abs_nonneg _) (le_trans (abs_nonneg _) hZle)
          rw [abs_of_nonneg (ballCutoff_nonneg s p.2)]
          exact ballCutoff_le_one s p.2
      _ = C := mul_one C
      _ ≤ max C 0 := le_max_left _ _


/-! ### The continuity of the ball-stopped field -/

section Main

variable {ΩW ΩB : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩB] {d : ℕ}

omit [MeasurableSpace ΩW] in
/-- The cut-off reward computes the reward of the ball-stopped rule. -/
theorem ae_stoppedReward_state {PB : Measure ΩB} [IsProbabilityMeasure PB]
    {B : Space d → ℝ≥0 → ΩB → Space d} (hB : ∀ y, IsBrownian d y (B y) PB)
    (hBc : ∀ y ω, Continuous fun t => B y t ω) {Z : ℝ → Space d → ΩW → ℝ} {ω : ΩW}
    {s T : ℝ} (hs : 0 ≤ s) (hT : 0 < T) (u : Space 2) :
    ∀ᵐ b ∂PB, stoppedReward d Z ω s T u
        (ballStopTime d B s T u b,
          B (planePoint u) (ballStopTime d B s T u b) b - planePoint u)
      = -Z (T - (ballStopTime d B s T u b : ℝ))
          (B (planePoint u) (ballStopTime d B s T u b) b) ω := by
  filter_upwards [(hB (planePoint u)).start] with b hb
  have hnorm : ‖B (planePoint u) (ballStopTime d B s T u b) b - planePoint u‖ ≤ s :=
    norm_stopped_le (hBc (planePoint u)) hs T.toNNReal b hb
  rw [stoppedReward, ballCutoff_eq_one hnorm, mul_one,
    min_eq_left (ballStopTime_le_real B hT.le u b), sub_add_cancel]

omit [MeasurableSpace ΩW] in
/-- The stopped state is measurable. -/
theorem measurable_stoppedState {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    (s T : ℝ) (u : Space 2) :
    Measurable fun b => (ballStopTime d B s T u b,
      B (planePoint u) (ballStopTime d B s T u b) b - planePoint u) := by
  have hτ : Measurable (ballStopTime d B s T u) := measurable_ballStopTime hBc hBm s T u
  have hj : StronglyMeasurable (Function.uncurry (B (planePoint u))) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (hBc _) (hBm _)
  refine hτ.prodMk ?_
  exact (hj.measurable.comp (hτ.prodMk measurable_id)).sub measurable_const

omit [MeasurableSpace ΩW] in
/-- **The expected reward of the ball-stopped rule may be computed along one motion.** -/
theorem integral_stoppedReward_transfer {PB : Measure ΩB} [IsProbabilityMeasure PB]
    {B : Space d → ℝ≥0 → ΩB → Space d} (hB : ∀ y, IsBrownian d y (B y) PB)
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {Z : ℝ → Space d → ΩW → ℝ} {ω : ΩW} {s T : ℝ} (hT : 0 < T)
    (hZω : ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (u u₀ : Space 2) :
    (∫ b, stoppedReward d Z ω s T u (ballStopTime d B s T u b,
        B (planePoint u) (ballStopTime d B s T u b) b - planePoint u) ∂PB)
      = ∫ b, stoppedReward d Z ω s T u (ballStopTime d B s T u₀ b,
          B (planePoint u₀) (ballStopTime d B s T u₀ b) b - planePoint u₀) ∂PB := by
  obtain ⟨M, hM0, hMb⟩ := exists_bound_stoppedReward hT.le hZω s u 0
  have hTne : T.toNNReal ≠ 0 := by
    rw [ne_eq, ← NNReal.coe_eq_zero, Real.coe_toNNReal T hT.le]
    exact hT.ne'
  exact integral_stoppedState_eq (hB (planePoint u)) (hB (planePoint u₀)) (hBm _) (hBm _)
    (hBc _) (hBc _) hTne (continuous_stoppedReward hT.le hZω s u)
    (hMb u (by simp) )

omit [MeasurableSpace ΩW] in
/-- **The ball-stopped field is continuous in the plane point.** -/
theorem continuous_ballStoppedField {PB : Measure ΩB} [IsProbabilityMeasure PB]
    {B : Space d → ℝ≥0 → ΩB → Space d} (hB : ∀ y, IsBrownian d y (B y) PB)
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {Z : ℝ → Space d → ΩW → ℝ} {ω : ΩW} {s T : ℝ} (hs : 0 ≤ s) (hT : 0 < T)
    (hZω : ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) :
    Continuous fun u : Space 2 => ballStoppedField d Z PB B s T u ω := by
  set st : ΩB → ℝ≥0 × Space d := fun b => (ballStopTime d B s T 0 b,
    B (planePoint 0) (ballStopTime d B s T 0 b) b - planePoint 0) with hst
  have hstm : Measurable st := measurable_stoppedState hBc hBm s T 0
  have hrep : ∀ u : Space 2, ballStoppedField d Z PB B s T u ω
      = (2 * (d : ℝ))⁻¹ * (Z T (planePoint u) ω
        + ∫ b, stoppedReward d Z ω s T u (st b) ∂PB) := by
    intro u
    rw [ballStoppedField]
    congr 2
    rw [← integral_stoppedReward_transfer hB hBc hBm hT hZω u 0]
    exact (integral_congr_ae (ae_stoppedReward_state hB hBc hs hT u)).symm
  simp only [hrep]
  refine continuous_const.mul (Continuous.add ?_ ?_)
  · have hmem : ∀ u : Space 2, (T, planePoint (d := d) u)
        ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)) :=
      fun u => ⟨⟨hT.le, le_rfl⟩, Set.mem_univ _⟩
    exact hZω.comp_continuous (continuous_const.prodMk (continuous_planePoint d)) hmem
  · refine continuous_iff_seqContinuous.mpr ?_
    intro v w hvw
    obtain ⟨M, hM0, hMb⟩ := exists_bound_stoppedReward hT.le hZω s w 1
    have hpp : Tendsto (fun n => planePoint (d := d) (v n)) atTop
        (𝓝 (planePoint (d := d) w)) := ((continuous_planePoint d).tendsto w).comp hvw
    have hclose : ∀ᶠ n in atTop,
        ‖planePoint (d := d) (v n) - planePoint (d := d) w‖ ≤ 1 := by
      have := hpp.eventually (Metric.closedBall_mem_nhds (planePoint (d := d) w) one_pos)
      filter_upwards [this] with n hn
      rwa [← dist_eq_norm]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_
      (integrable_const M) ?_
    · filter_upwards with n
      exact (((continuous_stoppedReward hT.le hZω s (v n)).measurable).comp
        hstm).aestronglyMeasurable
    · filter_upwards [hclose] with n hn
      filter_upwards with b
      rw [Real.norm_eq_abs]
      exact hMb (v n) hn (st b)
    · filter_upwards with b
      exact ((continuous_stoppedReward_point hT.le hZω s (st b)).tendsto w).comp hvw


/-- **The approximation on a set is decided by countably many points.**  Both fields are
continuous in the plane point on one event of full measure, and being within `c` is a closed
condition, so the bad event for a set is contained, up to a null set, in the bad event for any
dense subset of it.  This is what reduces `Sandpile.Support.BallStoppedApproximation` to a bound
on the supremum over a COUNTABLE set of points; that bound is the residual of the node. -/
theorem measure_ballStopped_bad_le_countable {PW : Measure ΩW} {PB : Measure ΩB}
    [IsProbabilityMeasure PB] {W : (Space d → ℝ) → ΩW → ℝ} {Z : ℝ → Space d → ΩW → ℝ}
    {B : Space d → ℝ≥0 → ΩB → Space d} (hB : ∀ y, IsBrownian d y (B y) PB)
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {s T : ℝ} (hs : 0 ≤ s) (hT : 0 < T) (hZc : ContinuousHeatPotential d Z PW)
    (hXc : ∀ᵐ ω ∂PW, Continuous fun u : Space 2 => ballField d W s u ω)
    {K D : Set (Space 2)} (hKD : K ⊆ closure D) (c : ℝ) :
    PW {ω | ∀ u ∈ K, |ballStoppedField d Z PB B s T u ω - ballField d W s u ω| ≤ c}ᶜ
      ≤ PW {ω | ∀ u ∈ D, |ballStoppedField d Z PB B s T u ω - ballField d W s u ω| ≤ c}ᶜ := by
  refine measure_mono_ae ?_
  filter_upwards [hXc, hZc T hT] with ω h1 h2 hbad hgood
  refine hbad fun u hu => ?_
  have hcont : Continuous fun v : Space 2 =>
      |ballStoppedField d Z PB B s T v ω - ballField d W s v ω| :=
    ((continuous_ballStoppedField hB hBc hBm hs hT h2).sub h1).abs
  have hclosed : IsClosed {v : Space 2 |
      |ballStoppedField d Z PB B s T v ω - ballField d W s v ω| ≤ c} :=
    isClosed_le hcont continuous_const
  exact hclosed.closure_subset_iff.mpr (fun v hv => hgood v hv) (hKD hu)

end Main

end Sandpile.Support
