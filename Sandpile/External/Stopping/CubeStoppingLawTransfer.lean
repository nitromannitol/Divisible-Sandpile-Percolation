import Sandpile.External.Stopping.StoppingLawTransfer
import Sandpile.External.Stopping.CubeClockConstraint

/-!
# Cube-clipped stopping rewards and path laws

A finite natural stopping rule, clipped at a cube exit, transfers between
continuous processes with equal path laws.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- A finite natural stopping rule clipped at cube exit has the same expected
reward under another continuous realization of the same path law. -/
theorem exists_cube_clipped_finite_stopping_reward_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) (Q : Measure Ω')
    (B : ℝ≥0 → Ω → Continuum.Space d) (C : ℝ≥0 → Ω' → Continuum.Space d)
    (hBm : ∀ t, StronglyMeasurable (B t)) (hCm : ∀ t, StronglyMeasurable (C t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (hCc : ∀ ω, Continuous fun t => C t ω)
    (hlaw : P.map (LatticeProb.pathMap B hBc) = Q.map (LatticeProb.pathMap C hCc))
    (x : Continuum.Space d) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : Continuum.IsBrownianStopping B τ) (hτT : ∀ ω, τ ω ≤ T)
    (hτfin : (Set.range τ).Finite) (G : ℝ → Continuum.Space d → ℝ)
    (hG : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2)) :
    ∃ σ : Ω' → ℝ≥0, Continuum.IsBrownianStopping C σ ∧
      (∀ ω, σ ω ≤ T) ∧
      (∀ ω, σ ω ≤ (min (LatticeProb.openExitTime C (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal) ∧
      (∫ ω, G ((T : ℝ) - min (τ ω)
          (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal)
        (B (min (τ ω) (min (LatticeProb.openExitTime B (openUnitCube x) ω)
          (T : ℝ≥0∞)).toNNReal) ω) ∂P) =
        ∫ ω, G ((T : ℝ) - σ ω) (C (σ ω) ω) ∂Q := by
  obtain ⟨ρ, hρ, _, hρeq⟩ :=
    LatticeProb.exists_pathStoppingTime_of_finite_range B hBm hBc τ hτ hτfin
  let E : ℝ≥0 → LatticeProb.BrownianPath d → Continuum.Space d := fun t w => w t
  have hEm (t : ℝ≥0) : StronglyMeasurable (E t) :=
    (continuous_eval_const t).measurable.stronglyMeasurable
  have hEc (w : LatticeProb.BrownianPath d) : Continuous fun t => E t w := w.continuous
  let κ : LatticeProb.BrownianPath d → ℝ≥0 := fun w =>
    (min (LatticeProb.openExitTime E (openUnitCube x) w) (T : ℝ≥0∞)).toNNReal
  have hκm : Measurable κ := ENNReal.measurable_toNNReal.comp
    ((LatticeProb.measurable_openExitTime hEm hEc (isOpen_openUnitCube x)).min measurable_const)
  let ρT := fun w => min (ρ w) T
  have hρT : IsStoppingTime (LatticeProb.brownianNaturalFiltration d)
      (fun w => (ρT w : ℝ≥0∞)) := by
    have heq : (fun w => (ρT w : ℝ≥0∞)) =
        (fun w => min (ρ w : ℝ≥0∞) T) := by
      funext w
      exact ENNReal.coe_min (ρ w) T
    rw [heq]
    exact hρ.min_const T
  have hρTm : Measurable ρT := measurable_coe_nnreal_ennreal_iff.1
    (hρT.measurable.mono hρT.measurableSpace_le le_rfl)
  let σ := fun ω => min (ρT (LatticeProb.pathMap C hCc ω))
    (min (LatticeProb.openExitTime C (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal
  have hσ : Continuum.IsBrownianStopping C σ := by
    have ha := LatticeProb.isStoppingTime_comp_pathMap C hCm hCc hρT
    have hb := isBrownianStopping_openUnitCubeExitTrunc C hCc x T
    change IsStoppingTime (Continuum.brownianFiltration C) (fun ω => (σ ω : ℝ≥0∞))
    have heq : (fun ω => (σ ω : ℝ≥0∞)) =
        (fun ω => min (ρT (LatticeProb.pathMap C hCc ω) : ℝ≥0∞)
          ((min (LatticeProb.openExitTime C (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal : ℝ≥0∞)) := by
      funext ω
      exact ENNReal.coe_min _ _
    rw [heq]
    exact ha.min hb
  let F : LatticeProb.BrownianPath d → ℝ := fun w =>
    G ((T : ℝ) - min (ρT w) (κ w)) (w (min (ρT w) (κ w)))
  have hFm : Measurable F := by
    have ht : Measurable (fun w => min (ρT w) (κ w)) := hρTm.min hκm
    have hev : Measurable (fun w : LatticeProb.BrownianPath d => w (min (ρT w) (κ w))) :=
      (continuous_eval : Continuous fun p : LatticeProb.BrownianPath d × ℝ≥0 => p.1 p.2).measurable.comp
        (measurable_id.prodMk ht)
    exact hG.comp ((measurable_const.sub (measurable_coe_nnreal_real.comp ht)).prodMk hev)
  refine ⟨σ, hσ, (fun ω => (min_le_left _ _).trans (min_le_right _ _)),
    (fun ω => min_le_right _ _), ?_⟩
  have hFP : (fun ω => F (LatticeProb.pathMap B hBc ω)) =
      (fun ω => G ((T : ℝ) - min (τ ω)
        (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal)
        (B (min (τ ω) (min (LatticeProb.openExitTime B (openUnitCube x) ω)
          (T : ℝ≥0∞)).toNNReal) ω)) := by
    funext ω
    simp only [F, ρT, LatticeProb.pathMap_apply, ← hρeq ω, min_eq_left (hτT ω)]
    rfl
  have hFQ : (fun ω => F (LatticeProb.pathMap C hCc ω)) =
      (fun ω => G ((T : ℝ) - σ ω) (C (σ ω) ω)) := by
    funext ω
    rfl
  rw [← hFP, ← hFQ,
    ← MeasureTheory.integral_map (LatticeProb.measurable_pathMap B (fun t => (hBm t).measurable) hBc).aemeasurable hFm.aestronglyMeasurable,
    ← MeasureTheory.integral_map (LatticeProb.measurable_pathMap C (fun t => (hCm t).measurable) hCc).aemeasurable hFm.aestronglyMeasurable,
    hlaw]

end Sandpile.External.Stopping
