import Sandpile.External.Stopping.WalkSeparatedClockIndependence
import Sandpile.External.Stopping.IndependentObservationsLimit
import Sandpile.External.Stopping.FutureIndependentLimits

/-!
# Weak limits of walk clocks

Independence of future increments from the stopped past and clipped clock
passes to joint weak limits. This supplies the weak-filtration step in the
stopping-time convergence argument of Coquet and Toldo, Section 2.3.1.
-/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A fixed positive time gap eventually contains a separating lattice time
under diffusive scaling. -/
theorem eventually_exists_separating_grid (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (t u : ℝ≥0) (htu : t < u) :
    ∀ᶠ n in atTop, 0 < R n ∧ ∃ k : ℕ,
      R n ^ 2 * (t : ℝ) ≤ k ∧ k ≤ ⌊R n ^ 2 * (u : ℝ)⌋₊ := by
  have hdiff : 0 < (u : ℝ) - (t : ℝ) := by exact sub_pos.mpr (by exact_mod_cast htu)
  have hgap : Tendsto (fun n => ((u : ℝ) - (t : ℝ)) * R n ^ 2) atTop atTop :=
    (tendsto_const_mul_pow_atTop (n := 2) (by norm_num) hdiff).comp hR
  filter_upwards [hR.eventually_gt_atTop 0, hgap.eventually_ge_atTop 1] with n hn hg
  refine ⟨hn, ⌈R n ^ 2 * (t : ℝ)⌉₊, Nat.le_ceil _, ?_⟩
  apply (Nat.le_floor_iff (by positivity : 0 ≤ R n ^ 2 * (u : ℝ))).2
  have hc := Nat.ceil_lt_add_one (show 0 ≤ R n ^ 2 * (t : ℝ) by positivity)
  nlinarith

/-- Independence of continuous observations passes to a weak limit when it
holds eventually along the sequence. -/
theorem indepFun_of_weak_limit_of_continuous_eventually
    {S E F : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace E] [TopologicalSpace F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    [PseudoMetrizableSpace E] [PseudoMetrizableSpace F]
    (μ : ℕ → ProbabilityMeasure S) (ν : ProbabilityMeasure S)
    (hlim : Tendsto μ atTop (𝓝 ν)) (f : S → E) (g : S → F)
    (hf : Continuous f) (hg : Continuous g)
    (hindep : ∀ᶠ n in atTop, IndepFun f g (μ n : Measure S)) :
    IndepFun f g (ν : Measure S) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hindep
  apply indepFun_of_weak_limit_of_continuous (fun n => μ (n + N)) ν
    (hlim.comp (tendsto_add_atTop_nat N)) f g hf hg
  intro n
  exact hN _ (Nat.le_add_left N n)

/-- Any joint weak limit of interpolated walk paths and diffusive stopping
clocks has future increments independent of the stopped past and clipped
clock. -/
theorem indepFun_future_stopped_of_walk_joint_weak_limit {d : ℕ} [NeZero d]
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (q : ℕ → Site d)
    (τ : ℕ → (ℕ → Site d) → ℕ) (hτ : ∀ n, IsWalkStopping (τ n))
    (hτm : ∀ n, Measurable (τ n))
    (μ : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0))
    (ρ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0))
    (hμ : ∀ n, (μ n : Measure _) = (walkLaw d (q n)).map
      (fun X => (diffusiveWalkPath (R n) X,
        (τ n X : ℝ≥0) / ⟨R n ^ 2, sq_nonneg (R n)⟩)))
    (hlim : Tendsto μ atTop (𝓝 ρ)) (t : ℝ≥0) :
    IndepFun (fun p : C(ℝ≥0, Continuum.Space d) × ℝ≥0 => futureIncrementPath t p.1)
      (fun p : C(ℝ≥0, Continuum.Space d) × ℝ≥0 =>
        (LatticeProb.stoppedPath (t : ℝ≥0∞) p.1, min p.2 t))
      (ρ : Measure (C(ℝ≥0, Continuum.Space d) × ℝ≥0)) := by
  let f : (C(ℝ≥0, Continuum.Space d) × ℝ≥0) → C(ℝ≥0, Continuum.Space d) × ℝ≥0 :=
    fun p => (LatticeProb.stoppedPath (t : ℝ≥0∞) p.1, min p.2 t)
  let g (u : ℝ≥0) : (C(ℝ≥0, Continuum.Space d) × ℝ≥0) →
      C(ℝ≥0, Continuum.Space d) := fun p => futureIncrementPath u p.1
  have hf : Continuous f :=
    (LatticeProb.continuous_stoppedPath.comp (continuous_const.prodMk continuous_fst)).prodMk
      (continuous_snd.min continuous_const)
  have hg (u : ℝ≥0) : Continuous (g u) :=
    (continuous_futureIncrementPath u).comp continuous_fst
  have hfuture (u : ℝ≥0) (htu : t < u) : IndepFun (g u) f (ρ : Measure _) := by
    apply indepFun_of_weak_limit_of_continuous_eventually μ ρ hlim (g u) f (hg u) hf
    filter_upwards [eventually_exists_separating_grid R hR t u htu] with n hn
    obtain ⟨hRn, k, htk, hku⟩ := hn
    have hsrc := (indepFun_stoppedWalk_clippedClock_future (R n) hRn (q n)
      (τ n) (hτ n) t u k htk hku).symm
    let : IsProbabilityMeasure (walkLaw d (q n)) := by
      change IsProbabilityMeasure (LatticeProb.siteWalkLaw d (q n))
      infer_instance
    let c : ℝ≥0 := ⟨R n ^ 2, sq_nonneg (R n)⟩
    have hclockm : Measurable (fun X => ((τ n X : ℝ≥0) / c)) :=
      (measurable_of_countable (fun z : ℕ => (z : ℝ≥0) / c)).comp (hτm n)
    have hm : Measurable (fun X => (diffusiveWalkPath (R n) X,
        (τ n X : ℝ≥0) / ⟨R n ^ 2, sq_nonneg (R n)⟩)) :=
      (measurable_diffusiveWalkPath (R n)).prodMk hclockm
    rw [hμ n]
    apply indepFun_map_of_comp _ _ hm (g u) f (hg u).measurable hf.measurable
    exact hsrc
  let : MetricSpace (C(ℝ≥0, Continuum.Space d) × ℝ≥0) :=
    TopologicalSpace.metrizableSpaceMetric _
  let u : ℕ → ℝ≥0 := fun n => t + 1 / (n + 1)
  have hu : Tendsto u atTop (𝓝 t) := by
    dsimp [u]
    simpa using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (1 : ℝ≥0) / (n + 1)) atTop (𝓝 0))
  apply indepFun_futureIncrementPath_of_tendsto (ρ : Measure _) Prod.fst f
    measurable_fst hf.measurable u t hu
  intro n
  apply hfuture
  dsimp [u]
  exact lt_add_of_pos_right _ (by positivity)

end Sandpile.External.Stopping
