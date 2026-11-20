import Sandpile.External.Stopping.StepWalkIndependence
import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Càdlàg paths of the step walk

The floor-time walk is right-continuous and has left limits. Its diffusive
rescaling preserves these properties at every positive scale.
-/

open Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Each step-walk trajectory is right-continuous and has left limits. -/
theorem isCadlag_stepWalk {d : ℕ} (R : ℝ) (X : ℕ → Site d) :
    IsCadlag (fun t => stepWalk R t X) := by
  constructor
  · intro t
    have hcoe : Tendsto (fun s : ℝ≥0 => (s : ℝ)) (𝓝[>] t) (𝓝[≥] (t : ℝ)) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · exact NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        change (t : ℝ) ≤ (s : ℝ)
        have hs' : t < s := hs
        exact_mod_cast hs'.le
    have hfloor := (tendsto_floor_right_pure_floor (t : ℝ)).comp hcoe
    have hev : ∀ᶠ s : ℝ≥0 in 𝓝[>] t, ⌊(s : ℝ)⌋ = ⌊(t : ℝ)⌋ := tendsto_pure.1 hfloor
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with s hs
    simp only [stepWalk, ← Int.floor_toNat, hs]
  · intro t
    have hcoe : Tendsto (fun s : ℝ≥0 => (s : ℝ)) (𝓝[<] t) (𝓝[<] (t : ℝ)) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · exact NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        change (s : ℝ) < (t : ℝ)
        exact_mod_cast hs
    have hfloor := (tendsto_floor_left_pure_ceil_sub_one (t : ℝ)).comp hcoe
    have hev : ∀ᶠ s : ℝ≥0 in 𝓝[<] t, ⌊(s : ℝ)⌋ = ⌈(t : ℝ)⌉ - 1 := tendsto_pure.1 hfloor
    refine ⟨Lclt.scaledSite R (X (⌈(t : ℝ)⌉ - 1).toNat), ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with s hs
    simp only [stepWalk, ← Int.floor_toNat, hs]

/-- Positive diffusive time scaling preserves the step walk's càdlàg paths. -/
theorem isCadlag_diffusiveStepWalk {d : ℕ} {R : ℝ} (hR : 0 < R) (X : ℕ → Site d) :
    IsCadlag (fun t => diffusiveStepWalk R t X) := by
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hc : 0 < c := by
    change (0 : ℝ) < R ^ 2
    exact sq_pos_of_pos hR
  have hpath := isCadlag_stepWalk R X
  constructor
  · intro t
    have htime : Tendsto (fun s : ℝ≥0 => c * s) (𝓝[>] t) (𝓝[>] (c * t)) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · exact (continuous_const.mul continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact mul_lt_mul_of_pos_left hs hc
    change Tendsto (fun s => stepWalk R (c * s) X) (𝓝[>] t) (𝓝 (stepWalk R (c * t) X))
    have hr : Tendsto (fun s => stepWalk R s X) (𝓝[>] (c * t)) (𝓝 (stepWalk R (c * t) X)) :=
      hpath.isRightContinuous (c * t)
    exact hr.comp htime
  · intro t
    obtain ⟨z, hz⟩ := hpath.tendsto_nhdsLT (c * t)
    refine ⟨z, ?_⟩
    have htime : Tendsto (fun s : ℝ≥0 => c * s) (𝓝[<] t) (𝓝[<] (c * t)) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · exact (continuous_const.mul continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact mul_lt_mul_of_pos_left hs hc
    exact hz.comp htime

end Sandpile.External.Stopping
