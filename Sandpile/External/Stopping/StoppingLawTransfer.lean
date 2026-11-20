import Sandpile.External.Stopping.IndistinguishableStoppingValue
import LatticeProb.Prob.BrownianRestartBound
import LatticeProb.Prob.BoundedStopping

/-!
# Finite stopping rewards and path laws

Finitely valued natural stopping rules can be transferred between continuous
processes with the same path law, preserving bounded-horizon expected rewards.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- A bounded finite-valued stopping rule for one continuous process transfers
along an equal path law to a bounded rule with the same expected reward. -/
theorem exists_finite_stopping_reward_eq_of_path_law_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) (Q : Measure Ω')
    (B : ℝ≥0 → Ω → Continuum.Space d) (C : ℝ≥0 → Ω' → Continuum.Space d)
    (hBm : ∀ t, StronglyMeasurable (B t)) (hCm : ∀ t, StronglyMeasurable (C t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (hCc : ∀ ω, Continuous fun t => C t ω)
    (hlaw : P.map (LatticeProb.pathMap B hBc) = Q.map (LatticeProb.pathMap C hCc))
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : Continuum.IsBrownianStopping B τ)
    (hτT : ∀ ω, τ ω ≤ T) (hτfin : (Set.range τ).Finite)
    (G : ℝ → Continuum.Space d → ℝ)
    (hG : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2)) :
    ∃ σ : Ω' → ℝ≥0, Continuum.IsBrownianStopping C σ ∧
      (∀ ω, σ ω ≤ T) ∧ (Set.range σ).Finite ∧
      (∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P) =
        ∫ ω, G ((T : ℝ) - σ ω) (C (σ ω) ω) ∂Q := by
  obtain ⟨ρ, hρ, hρfin, hρeq⟩ :=
    LatticeProb.exists_pathStoppingTime_of_finite_range B hBm hBc τ hτ hτfin
  let ρT := fun w => min (ρ w) T
  have hρT : IsStoppingTime (LatticeProb.brownianNaturalFiltration d)
      (fun w => (ρT w : ℝ≥0∞)) := by
    have heq : (fun w => (ρT w : ℝ≥0∞)) =
        (fun w => min (ρ w : ℝ≥0∞) T) := by
      funext w
      exact ENNReal.coe_min (ρ w) T
    rw [heq]
    exact hρ.min_const T
  let σ := fun ω => ρT (LatticeProb.pathMap C hCc ω)
  have hσ : Continuum.IsBrownianStopping C σ :=
    LatticeProb.isStoppingTime_comp_pathMap C hCm hCc hρT
  have hρTm : Measurable ρT := measurable_coe_nnreal_ennreal_iff.1
    (hρT.measurable.mono hρT.measurableSpace_le le_rfl)
  let F : LatticeProb.BrownianPath d → ℝ := fun w =>
    G ((T : ℝ) - ρT w) (w (ρT w))
  have hFm : Measurable F := by
    have hev : Measurable (fun w : LatticeProb.BrownianPath d => w (ρT w)) :=
      (continuous_eval : Continuous fun p : LatticeProb.BrownianPath d × ℝ≥0 => p.1 p.2).measurable.comp
        (measurable_id.prodMk hρTm)
    exact hG.comp ((measurable_const.sub (measurable_coe_nnreal_real.comp hρTm)).prodMk hev)
  refine ⟨σ, hσ, (fun ω => min_le_right _ _), ?_, ?_⟩
  · exact (hρfin.image (fun t => min t T)).subset (by
      rintro _ ⟨ω, rfl⟩
      exact ⟨ρ (LatticeProb.pathMap C hCc ω), ⟨_, rfl⟩, rfl⟩)
  · have hFP : (fun ω => F (LatticeProb.pathMap B hBc ω)) =
        (fun ω => G ((T : ℝ) - τ ω) (B (τ ω) ω)) := by
      funext ω
      simp only [F, ρT, LatticeProb.pathMap_apply, ← hρeq ω, min_eq_left (hτT ω)]
    have hFQ : (fun ω => F (LatticeProb.pathMap C hCc ω)) =
        (fun ω => G ((T : ℝ) - σ ω) (C (σ ω) ω)) := by
      funext ω
      rfl
    rw [← hFP, ← hFQ, ← MeasureTheory.integral_map (LatticeProb.measurable_pathMap B (fun t => (hBm t).measurable) hBc).aemeasurable hFm.aestronglyMeasurable,
      ← MeasureTheory.integral_map (LatticeProb.measurable_pathMap C (fun t => (hCm t).measurable) hCc).aemeasurable hFm.aestronglyMeasurable,
      hlaw]

end Sandpile.External.Stopping
