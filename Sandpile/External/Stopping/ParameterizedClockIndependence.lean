import Sandpile.External.Stopping.IndependentClockEvent

/-!
# Future independence for parameterized clocks

A compact clock parameter can encode physical time through any continuous
map. Future independence for weak limits transfers through this encoding,
allowing the clock compactness argument to use a fixed parameter space.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Independence under a pushforward measure pulls back along its measurable
map. -/
theorem IndepFun.comp_of_map {Ω Ξ E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ξ] [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → Ξ) (hg : Measurable g)
    (f : Ξ → E) (h : Ξ → F) (hf : Measurable f) (hh : Measurable h)
    (hind : IndepFun f h (μ.map g)) : IndepFun (f ∘ g) (h ∘ g) μ := by
  let : IsProbabilityMeasure (μ.map g) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  have hi := (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hh.aemeasurable).1 hind
  rw [Measure.map_map (hf.prodMk hh) hg, Measure.map_map hf hg, Measure.map_map hh hg] at hi
  exact (indepFun_iff_map_prod_eq_prod_map_map
    (hf.comp hg).aemeasurable (hh.comp hg).aemeasurable).2 hi

/-- A lattice clock expressed in diffusive time. -/
noncomputable def diffusiveLatticeClock (R : ℝ) (n : ℕ) : ℝ≥0 :=
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  (n : ℝ≥0) / c

/-- Decoding a parameterized joint walk law gives the physical path-clock
law. -/
theorem map_parameterized_walk_clock_law {d : ℕ} {T : Type*}
    [MeasurableSpace T] (R : ℝ) (q : Site d)
    (τ : (ℕ → Site d) → ℕ) (θ : (ℕ → Site d) → T) (hθ : Measurable θ)
    (clock : T → ℝ≥0) (hclock : Measurable clock)
    (hdecode : ∀ X, clock (θ X) = diffusiveLatticeClock R (τ X)) :
    ((walkLaw d q).map (fun X => (diffusiveWalkPath R X, θ X))).map
      (fun p : C(ℝ≥0, Continuum.Space d) × T => (p.1, clock p.2)) =
    (walkLaw d q).map (fun X => (diffusiveWalkPath R X,
      diffusiveLatticeClock R (τ X))) := by
  let D : C(ℝ≥0, Continuum.Space d) × T → C(ℝ≥0, Continuum.Space d) × ℝ≥0 :=
    fun p => (p.1, clock p.2)
  have hD : Measurable D := measurable_fst.prodMk (hclock.comp measurable_snd)
  calc
    _ = (walkLaw d q).map (D ∘ fun X => (diffusiveWalkPath R X, θ X)) :=
      Measure.map_map hD ((measurable_diffusiveWalkPath R).prodMk hθ)
    _ = _ := by
      congr 1
      funext X
      exact Prod.ext rfl (hdecode X)

/-- Independence of decoded clock observations pulls back to the parameter
space. -/
theorem indepFun_future_stopped_of_clock_map {d : ℕ} {T : Type*}
    [MeasurableSpace T] (ρ : Measure (C(ℝ≥0, Continuum.Space d) × T))
    [IsProbabilityMeasure ρ] (clock : T → ℝ≥0) (hclock : Measurable clock) (t : ℝ≥0)
    (hind : IndepFun (fun p : C(ℝ≥0, Continuum.Space d) × ℝ≥0 =>
        futureIncrementPath t p.1)
      (fun p : C(ℝ≥0, Continuum.Space d) × ℝ≥0 =>
        (LatticeProb.stoppedPath (t : ℝ≥0∞) p.1, min p.2 t))
      (ρ.map (fun p => (p.1, clock p.2)))) :
    IndepFun (fun p : C(ℝ≥0, Continuum.Space d) × T => futureIncrementPath t p.1)
      (fun p : C(ℝ≥0, Continuum.Space d) × T =>
        (LatticeProb.stoppedPath (t : ℝ≥0∞) p.1, min (clock p.2) t)) ρ := by
  let D : C(ℝ≥0, Continuum.Space d) × T → C(ℝ≥0, Continuum.Space d) × ℝ≥0 :=
    fun p => (p.1, clock p.2)
  have hD : Measurable D := measurable_fst.prodMk (hclock.comp measurable_snd)
  have hf : Measurable (fun p : C(ℝ≥0, Continuum.Space d) × ℝ≥0 =>
      futureIncrementPath t p.1) := (continuous_futureIncrementPath t).measurable.comp measurable_fst
  have hg : Measurable (fun p : C(ℝ≥0, Continuum.Space d) × ℝ≥0 =>
      (LatticeProb.stoppedPath (t : ℝ≥0∞) p.1, min p.2 t)) :=
    (LatticeProb.continuous_stoppedPath.measurable.comp
      (measurable_const.prodMk measurable_fst)).prodMk
      ((continuous_snd.min continuous_const).measurable)
  exact IndepFun.comp_of_map ρ D hD _ _ hf hg hind

/-- Independence of future increments survives joint weak limits of paths and
clock parameters when a continuous function decodes their physical time. -/
theorem indepFun_future_stopped_of_parameterized_walk_joint_weak_limit
    {d : ℕ} [NeZero d] {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (q : ℕ → Site d)
    (τ : ℕ → (ℕ → Site d) → ℕ) (hτ : ∀ n, IsWalkStopping (τ n))
    (hτm : ∀ n, Measurable (τ n))
    (θ : ℕ → (ℕ → Site d) → T) (hθ : ∀ n, Measurable (θ n))
    (clock : T → ℝ≥0) (hclock : Continuous clock)
    (hdecode : ∀ n X, clock (θ n X) =
      diffusiveLatticeClock (R n) (τ n X))
    (μ : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × T))
    (ρ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × T))
    (hμ : ∀ n, (μ n : Measure _) = (walkLaw d (q n)).map
      (fun X => (diffusiveWalkPath (R n) X, θ n X)))
    (hlim : Tendsto μ atTop (𝓝 ρ)) (t : ℝ≥0) :
    IndepFun (fun p : C(ℝ≥0, Continuum.Space d) × T => futureIncrementPath t p.1)
      (fun p : C(ℝ≥0, Continuum.Space d) × T =>
        (LatticeProb.stoppedPath (t : ℝ≥0∞) p.1, min (clock p.2) t))
      (ρ : Measure (C(ℝ≥0, Continuum.Space d) × T)) := by
  let D : C(ℝ≥0, Continuum.Space d) × T → C(ℝ≥0, Continuum.Space d) × ℝ≥0 :=
    fun p => (p.1, clock p.2)
  have hD : Continuous D := continuous_fst.prodMk (hclock.comp continuous_snd)
  let ν : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0) :=
    fun n => (μ n).map D
  let κ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × ℝ≥0) := ρ.map D
  have hν : ∀ n, (ν n : Measure _) = (walkLaw d (q n)).map
      (fun X => (diffusiveWalkPath (R n) X,
        diffusiveLatticeClock (R n) (τ n X))) := by
    intro n
    change ((μ n : Measure _).map D) = _
    rw [hμ n]
    exact map_parameterized_walk_clock_law (R n) (q n) (τ n) (θ n) (hθ n)
      clock hclock.measurable (hdecode n)
  have hνlim : Tendsto ν atTop (𝓝 κ) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ρ hlim hD
  have hi := indepFun_future_stopped_of_walk_joint_weak_limit R hR q τ hτ hτm ν κ hν hνlim t
  exact indepFun_future_stopped_of_clock_map (ρ : Measure
    (C(ℝ≥0, Continuum.Space d) × T)) clock hclock.measurable t hi

end Sandpile.External.Stopping
