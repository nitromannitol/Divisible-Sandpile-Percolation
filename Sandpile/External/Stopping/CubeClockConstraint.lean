import LatticeProb.Prob.BrownianOpenExitStopping
import Sandpile.External.Stopping.SandpileBrownianCubeExit
import Sandpile.External.Stopping.CubeStoppedPathLimit
import Sandpile.External.Stopping.RightFiltrationKilledValue
import Sandpile.Support.ExplKilledValue

/-!
# Cube killing and regular exit clocks

At a regular cube exit, the condition of staying in the closed cube strictly
before stopping is equivalent to stopping no later than the exit clock.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- A regular first exit converts the closed-cube killing condition to an
inequality with the exit clock. -/
theorem cube_constraint_iff_le_regular_clock {d : ℕ}
    (f : ℝ≥0 → Continuum.Space d) (x : Continuum.Space d) (η τ : ℝ≥0)
    (hbefore : ∀ s < η, ∀ i, |f s i - x i| < 1)
    (hafter : ∀ t > η, ∃ s < t, ∃ i, 1 < |f s i - x i|) :
    (∀ s < τ, ∀ i, |f s i - x i| ≤ 1) ↔ τ ≤ η := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨s, hs, i, hi⟩ := hafter τ (lt_of_not_ge hn)
    exact (not_lt_of_ge (h s hs i)) hi
  · intro h s hs i
    exact (hbefore s (hs.trans_le h) i).le

/-- With a horizon bound, truncating the exit clock at the horizon leaves the
cube killing constraint unchanged. -/
theorem cube_constraint_iff_le_truncated_regular_clock {d : ℕ}
    (f : ℝ≥0 → Continuum.Space d) (x : Continuum.Space d) (η τ T : ℝ≥0)
    (hτT : τ ≤ T)
    (hbefore : ∀ s < η, ∀ i, |f s i - x i| < 1)
    (hafter : ∀ t > η, ∃ s < t, ∃ i, 1 < |f s i - x i|) :
    (∀ s < τ, ∀ i, |f s i - x i| ≤ 1) ↔ τ ≤ min η T := by
  rw [cube_constraint_iff_le_regular_clock f x η τ hbefore hafter, le_min_iff]
  exact ⟨fun h => ⟨h, hτT⟩, And.left⟩


/-- On regular Brownian paths, the cube payoff class is the class of stops
bounded by the truncated first exit from the open cube. -/
theorem cubeStoppingPayoffs_eq_clockPayoffs {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} [NeZero d] (P : Measure Ω) [IsProbabilityMeasure P]
    (x : Continuum.Space d) (B : ℝ≥0 → Ω → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ) :
    Continuum.cubeStoppingPayoffs B P (fun s z => -G s z) T 1 x =
      clockPayoffs B P T G
        (fun ω => (min (LatticeProb.openExitTime B {z | ∀ i, |z i - x i| < 1} ω)
          (T : ℝ≥0∞)).toNNReal)
        (Continuum.brownianFiltration B) := by
  have hreg := ae_sandpile_brownian_cube_exit_regular hB hm hc
  ext a
  simp only [Continuum.cubeStoppingPayoffs, clockPayoffs, Set.mem_ofPred_eq, neg_neg,
    NNReal.coe_le_coe]
  constructor
  · rintro ⟨τ, hτ, hτT, hkill, ha⟩
    refine ⟨τ, hτ, hτT, ?_, ha⟩
    filter_upwards [hreg, hkill] with ω hregω hkillω
    have hclock : (min (LatticeProb.openExitTime B {z | ∀ i, |z i - x i| < 1} ω)
        (T : ℝ≥0∞)).toNNReal =
        min (LatticeProb.openExitTime B {z | ∀ i, |z i - x i| < 1} ω).toNNReal T := by
      rw [← ENNReal.coe_toNNReal hregω.1, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
      simp only [ENNReal.toNNReal_coe]
    rw [hclock]
    exact (cube_constraint_iff_le_truncated_regular_clock (fun t => B t ω) x _ _ T
      (hτT ω) hregω.2.1 hregω.2.2).1 hkillω
  · rintro ⟨τ, hτ, hτT, hkill, ha⟩
    refine ⟨τ, hτ, hτT, ?_, ha⟩
    filter_upwards [hreg, hkill] with ω hregω hkillω
    have hclock : (min (LatticeProb.openExitTime B {z | ∀ i, |z i - x i| < 1} ω)
        (T : ℝ≥0∞)).toNNReal =
        min (LatticeProb.openExitTime B {z | ∀ i, |z i - x i| < 1} ω).toNNReal T := by
      rw [← ENNReal.coe_toNNReal hregω.1, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
      simp only [ENNReal.toNNReal_coe]
    rw [hclock] at hkillω
    exact (cube_constraint_iff_le_truncated_regular_clock (fun t => B t ω) x _ _ T
      (hτT ω) hregω.2.1 hregω.2.2).2 hkillω


/-- The open-cube exit truncated at a finite horizon is a natural-filtration
stopping time for a continuous process. -/
theorem isBrownianStopping_openUnitCubeExitTrunc {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (hc : ∀ ω, Continuous fun t => B t ω)
    (x : Continuum.Space d) (T : ℝ≥0) :
    Continuum.IsBrownianStopping B
      (fun ω => (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap (fun ω => fun t => B t ω) inferInstance
  have hp : Measurable (fun ω => fun t => B t ω) := measurable_iff_comap_le.mpr le_rfl
  have hm : ∀ t, StronglyMeasurable (B t) :=
    fun t => ((measurable_pi_apply t).comp hp).stronglyMeasurable
  apply (Continuum.isBrownianStopping_iff_natFiltration B hm _).2
  have h := (LatticeProb.isStoppingTime_openExitTime hm hc (isOpen_openUnitCube x)).min_const T
  have heq : (fun ω => (((min (LatticeProb.openExitTime B (openUnitCube x) ω)
      (T : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞)) =
      (fun ω => min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)) := by
    funext ω
    exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  rw [heq]
  exact h

/-- Cube-killed Brownian values are unchanged by right-continuation of the
natural filtration when all paths are continuous. -/
theorem sSup_rightCont_cubeClock_eq_brownianDiscountCube {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} [NeZero d] (P : Measure Ω) [IsProbabilityMeasure P]
    (x : Continuum.Space d) (B : ℝ≥0 → Ω → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    sSup (clockPayoffs B P T G
      (fun ω => (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal)
      (Continuum.brownianFiltration B).rightCont) =
      Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x := by
  let κ : Ω → ℝ≥0 := fun ω =>
    (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal
  have hκT : ∀ ω, κ ω ≤ T := by
    intro ω
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
    exact min_le_right _ _
  have h := sSup_clockPayoffs_rightCont_eq P B (fun t => (hm t).aemeasurable)
    (Filter.Eventually.of_forall hc) T G hGc M hG κ
    (isBrownianStopping_openUnitCubeExitTrunc B hc x T) hκT
  rw [h]
  unfold Continuum.brownianDiscountCube
  rw [cubeStoppingPayoffs_eq_clockPayoffs P x B hB hm hc T G]
  rfl

end Sandpile.External.Stopping
