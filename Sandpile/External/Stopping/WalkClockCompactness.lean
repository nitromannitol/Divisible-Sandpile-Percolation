import Sandpile.External.Stopping.NormalizedWalkClock
import Sandpile.External.Stopping.JointClockCompactness
import Sandpile.External.Stopping.WalkPathConvergence
import LatticeProb.Topology.PolishContinuousMap

/-!
# Joint compactness of walks and stopping clocks

The normalized lattice stopping clocks live in a compact interval, so joint
laws have subsequential limits with the prescribed limiting path marginal. The
limiting rewards are bounded by that marginal's stopping value.
-/

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped NNReal ENNReal ProbabilityTheory BoundedContinuousFunction

namespace Sandpile.External.Stopping

/-- The joint law of a diffusive walk and a normalized lattice clock. -/
noncomputable def normalizedWalkClockLaw {d : ℕ} [NeZero d]
    (R : ℝ) (q : Site d) (c : ℝ≥0) (τ : (ℕ → Site d) → ℕ) (hτ : Measurable τ) :
    ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × I) :=
  ⟨(walkLaw d q).map (fun X => (diffusiveWalkPath R X, normalizedWalkClock R c τ X)),
    (Measure.isProbabilityMeasure_map_iff
      ((measurable_diffusiveWalkPath R).prodMk (measurable_normalizedWalkClock R c τ hτ)).aemeasurable).2
      (by change IsProbabilityMeasure (LatticeProb.siteWalkLaw d q); infer_instance)⟩

/-- The path marginal of a normalized walk-clock law is the original walk law. -/
theorem normalizedWalkClockLaw_fst {d : ℕ} [NeZero d]
    (R : ℝ) (q : Site d) (c : ℝ≥0) (τ : (ℕ → Site d) → ℕ) (hτ : Measurable τ) :
    (normalizedWalkClockLaw R q c τ hτ).map Prod.fst = diffusiveWalkPathLaw d R q := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((walkLaw d q).map (fun X => (diffusiveWalkPath R X,
    normalizedWalkClock R c τ X))).map Prod.fst = _
  exact Measure.fst_map_prodMk (measurable_diffusiveWalkPath R)
    (measurable_normalizedWalkClock R c τ hτ)

/-- At any lattice time, interpolation of the diffusive walk recovers the
corresponding scaled site. -/
theorem diffusiveWalkPath_diffusiveLatticeClock {d : ℕ} (R : ℝ) (hR : 0 < R)
    (X : ℕ → Site d) (k : ℕ) :
    diffusiveWalkPath R X (diffusiveLatticeClock R k) = Lclt.scaledSite R (X k) := by
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hc : 0 < c := by change 0 < R ^ 2; positivity
  change linearWalk R (c * ((k : ℝ≥0) / c)) X = _
  rw [mul_div_cancel₀ _ hc.ne', linearWalk_nat]

/-- Bounded stopping clocks admit a joint weak-limit subsequence whose expected
reward is bounded by the stopping value of the limiting path marginal. -/
theorem exists_walk_clock_limit_with_reward_bound {d : ℕ} [NeZero d]
    {ι : Type*} [Countable ι]
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (q : ℕ → Site d) (H : ℕ → ℝ≥0) (T c : ℝ≥0) (hc : 0 < c)
    (hH : Tendsto H atTop (𝓝 T)) (hHc : ∀ n, H n ≤ c)
    (τ : ℕ → (ℕ → Site d) → ℕ) (hτ : ∀ n, IsWalkStopping (τ n))
    (hτH : ∀ n X, τ n X ≤ ⌊R n ^ 2 * (H n : ℝ)⌋₊)
    (ν : ProbabilityMeasure C(ℝ≥0, Continuum.Space d))
    (hpath : Tendsto (fun n => diffusiveWalkPathLaw d (R n) (q n)) atTop (𝓝 ν))
    (time : ι → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    ∃ (φ : ℕ → ℕ) (ρ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × I)),
      StrictMono φ ∧ ρ.map Prod.fst = ν ∧
      Tendsto (fun n => normalizedWalkClockLaw (R (φ n)) (q (φ n)) c (τ (φ n))
        (LatticeProb.measurable_isWalkStopping (hτ (φ n)) (hτH (φ n)))) atTop (𝓝 ρ) ∧
      (∀ F : (C(ℝ≥0, Continuum.Space d) × I) →ᵇ ℝ,
        Tendsto (fun n => ∫ X, F (diffusiveWalkPath (R (φ n)) X,
          normalizedWalkClock (R (φ n)) c (τ (φ n)) X) ∂(walkLaw d (q (φ n))))
          atTop (𝓝 (∫ p, F p ∂(ρ : Measure (C(ℝ≥0, Continuum.Space d) × I))))) ∧
      (∫ p, G ((T : ℝ) - (c * unitClock id p.2 : ℝ≥0))
        (p.1 (c * unitClock id p.2)) ∂(ρ : Measure (C(ℝ≥0, Continuum.Space d) × I))) ≤
        Continuum.brownianDiscount (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
          (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I)).fst (fun s z => -G s z) T := by
  have hτm (n : ℕ) : Measurable (τ n) :=
    LatticeProb.measurable_isWalkStopping (hτ n) (hτH n)
  let θ (n : ℕ) := normalizedWalkClock (R n) c (τ n)
  let μ (n : ℕ) := normalizedWalkClockLaw (R n) (q n) c (τ n) (hτm n)
  have hθ (n : ℕ) : Measurable (θ n) := measurable_normalizedWalkClock _ _ _ (hτm n)
  have hμ (n : ℕ) : (μ n : Measure (C(ℝ≥0, Continuum.Space d) × I)) = (walkLaw d (q n)).map
      (fun X => (diffusiveWalkPath (R n) X, θ n X)) := rfl
  have hmarg : Tendsto (fun n => (μ n).map Prod.fst) atTop (𝓝 ν) := by
    simpa only [μ, normalizedWalkClockLaw_fst] using hpath
  let : PolishSpace C(ℝ≥0, Continuum.Space d) := LatticeProb.polishSpace_continuousMap _ _
  let := TopologicalSpace.upgradeIsCompletelyMetrizable C(ℝ≥0, Continuum.Space d)
  obtain ⟨φ, ρ, hφ, hlim, hmarg'⟩ :=
    exists_subseq_joint_law_of_compact_clock_of_tendsto μ ν hmarg
  refine ⟨φ, ρ, hφ, hmarg', hlim, ?_, ?_⟩
  · intro F
    have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) F
    have heq (n : ℕ) : ∫ p, F p ∂(μ (φ n) : Measure (C(ℝ≥0, Continuum.Space d) × I)) =
        ∫ X, F (diffusiveWalkPath (R (φ n)) X, θ (φ n) X) ∂(walkLaw d (q (φ n))) := by
      rw [hμ]
      exact integral_map ((measurable_diffusiveWalkPath _).prodMk (hθ _)).aemeasurable
        F.continuous.measurable.aestronglyMeasurable
    simpa only [heq] using h
  have hclock (n : ℕ) (X : ℕ → Site d) :
      diffusiveLatticeClock (R n) (τ n X) ≤ H n :=
    diffusiveLatticeClock_le_horizon (R n) (hRpos n) (H n) (τ n X) (hτH n X)
  have hdecode (n : ℕ) (X : ℕ → Site d) :
      c * unitClock id (θ n X) = diffusiveLatticeClock (R n) (τ n X) :=
    decode_normalizedWalkClock (R n) c hc (τ n) X ((hclock n X).trans (hHc n))
  have hbound (n : ℕ) : ∀ᵐ p ∂(μ (φ n) : Measure (C(ℝ≥0, Continuum.Space d) × I)), c * unitClock id p.2 ≤ H (φ n) := by
    rw [hμ]
    have hmap : Measurable (fun X => (diffusiveWalkPath (R (φ n)) X, θ (φ n) X)) :=
      (measurable_diffusiveWalkPath _).prodMk (hθ _)
    have hset : MeasurableSet {p : C(ℝ≥0, Continuum.Space d) × I |
        c * unitClock id p.2 ≤ H (φ n)} :=
      measurableSet_le (measurable_const.mul (measurable_unitClock.comp measurable_snd))
        measurable_const
    apply (ae_map_iff hmap.aemeasurable hset).2
    filter_upwards with X
    rw [hdecode]
    exact hclock (φ n) X
  exact integral_walk_clock_limit_le_discount (R ∘ φ) (hR.comp hφ.tendsto_atTop)
    (q ∘ φ) (τ ∘ φ) (fun n => hτ (φ n)) (fun n => hτm (φ n))
    (θ ∘ φ) (fun n => hθ (φ n)) c hc (fun n => hdecode (φ n))
    (μ ∘ φ) ρ (fun n => hμ (φ n)) hlim (H ∘ φ) T
    (hH.comp hφ.tendsto_atTop) hbound time hdense G hGc M hG

end Sandpile.External.Stopping
