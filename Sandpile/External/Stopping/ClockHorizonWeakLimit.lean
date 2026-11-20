import Sandpile.External.Stopping.CubeConstraintWeakLimit
import Sandpile.External.Stopping.JointClockReward

/-!
# Clock bounds under weak convergence

Continuous clock parameters bounded by converging horizons remain bounded by
the limiting horizon almost surely. This is the horizon constraint for joint
weak limits of stopped walk laws.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set unitInterval
open scoped NNReal ENNReal ProbabilityTheory

namespace Sandpile.External.Stopping

/-- A continuous clock bounded by varying horizons remains bounded by their
limit under weak convergence. -/
theorem ae_clock_le_of_tendsto_probabilityMeasure {E T : Type*}
    [TopologicalSpace E] [TopologicalSpace T] [MeasurableSpace E] [MeasurableSpace T]
    [BorelSpace E] [BorelSpace T] [SecondCountableTopology E] [SecondCountableTopology T]
    [HasOuterApproxClosed (E × T)]
    (μ : ℕ → ProbabilityMeasure (E × T)) (ρ : ProbabilityMeasure (E × T))
    (hμ : Tendsto μ atTop (𝓝 ρ)) (clock : T → ℝ≥0) (hclock : Continuous clock)
    (H : ℕ → ℝ≥0) (h : ℝ≥0) (hH : Tendsto H atTop (𝓝 h))
    (hbound : ∀ n, ∀ᵐ p ∂(μ n : Measure (E × T)), clock p.2 ≤ H n) :
    ∀ᵐ p ∂(ρ : Measure (E × T)), clock p.2 ≤ h := by
  have hall : ∀ k : ℕ, ∀ᵐ p ∂(ρ : Measure (E × T)),
      clock p.2 ≤ h + 1 / (k + 1) := by
    intro k
    let a : ℝ≥0 := h + 1 / (k + 1)
    have ha : h < a := by dsimp [a]; exact lt_add_of_pos_right _ (by positivity)
    have hclose : ∀ᶠ n in atTop, H n ≤ a := by
      filter_upwards [hH.eventually (Iio_mem_nhds ha)] with n hn
      exact hn.le
    have hclosed : IsClosed {p : E × T | clock p.2 ≤ a} :=
      isClosed_le (hclock.comp continuous_snd) continuous_const
    apply ae_mem_closed_of_tendsto_probabilityMeasure μ ρ hμ _ hclosed
    filter_upwards [hclose] with n hn
    filter_upwards [hbound n] with p hp
    exact hp.trans hn
  filter_upwards [ae_all_iff.mpr hall] with p hp
  have hlim : Tendsto (fun k : ℕ => h + 1 / (k + 1)) atTop (𝓝 h) := by
    simpa using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => (1 : ℝ≥0) / (k + 1)) atTop (𝓝 0))
  exact ge_of_tendsto hlim (Eventually.of_forall hp)

/-- A joint weak limit of normalized walk clocks has reward at most the
stopping value of its limiting path marginal. -/
theorem integral_walk_clock_limit_le_discount {d : ℕ} [NeZero d]
    {ι : Type*} [Countable ι]
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (q : ℕ → Site d)
    (τ : ℕ → (ℕ → Site d) → ℕ) (hτ : ∀ n, IsWalkStopping (τ n))
    (hτm : ∀ n, Measurable (τ n))
    (θ : ℕ → (ℕ → Site d) → I) (hθ : ∀ n, Measurable (θ n))
    (c : ℝ≥0) (hc : 0 < c)
    (hdecode : ∀ n X, c * unitClock id (θ n X) = diffusiveLatticeClock (R n) (τ n X))
    (μ : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × I))
    (ρ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × I))
    (hμ : ∀ n, (μ n : Measure (C(ℝ≥0, Continuum.Space d) × I)) = (walkLaw d (q n)).map
      (fun X => (diffusiveWalkPath (R n) X, θ n X)))
    (hlim : Tendsto μ atTop (𝓝 ρ)) (H : ℕ → ℝ≥0) (T : ℝ≥0)
    (hH : Tendsto H atTop (𝓝 T))
    (hbound : ∀ n, ∀ᵐ p ∂(μ n : Measure (C(ℝ≥0, Continuum.Space d) × I)), c * unitClock id p.2 ≤ H n)
    (time : ι → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    (∫ p, G ((T : ℝ) - (c * unitClock id p.2 : ℝ≥0))
      (p.1 (c * unitClock id p.2)) ∂(ρ : Measure (C(ℝ≥0, Continuum.Space d) × I))) ≤
      Continuum.brownianDiscount (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
        (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I)).fst (fun s z => -G s z) T := by
  have hclock : Continuous (fun z : I => c * unitClock id z) :=
    continuous_const.mul continuous_unitClock
  have hclockT := ae_clock_le_of_tendsto_probabilityMeasure μ ρ hlim
    (fun z => c * unitClock id z) hclock H T hH hbound
  obtain ⟨sigma, hsigma, _, hmap⟩ := exists_stopping_version_of_walk_clock_limit
    R hR q τ hτ hτm θ hθ c hc hdecode μ ρ hμ hlim time hdense
  exact integral_joint_clock_reward_le_discount_of_ae_le (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I))
    (fun z => c * unitClock id z) hclock.measurable T G hGc M hG sigma hsigma hmap hclockT

end Sandpile.External.Stopping
