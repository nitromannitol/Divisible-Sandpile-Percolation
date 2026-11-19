import Sandpile.Support.D4MeshHeatLog
import Sandpile.Support.D4CenteredLogBound
import Sandpile.Support.D4RieszTightness

/-!
# Logarithmic covariance bound for the centered membrane

The finite-time covariance of the centered embedding has a logarithmic
singularity, uniformly in time and in all mesh scales at least one.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- On a fixed bounded set, the centered membrane covariance is uniformly
controlled by the logarithmic kernel. -/
theorem exists_membrane_omegaEmbed_log_covariance_bound
    (hPaired : External.PairedLocalCLTFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (w : Space 4 → ℝ) (hw : Integrable w) (hw0 : ∀ z, 0 ≤ w z)
    (hw1 : ∫ z, w z = 1) (W L : ℝ) (hW : 0 ≤ W)
    (hwB : ∀ z, |w z| ≤ W) (hwL : ∀ z, w z ≠ 0 → ‖z‖ ≤ L) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ t : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∀ u v : Space 4, ‖u‖ ≤ L → ‖v‖ ≤ L → u ≠ v →
      |covariance (fun σ => omegaEmbed R w (membrane (scenery 4 σ) t) u)
        (fun σ => omegaEmbed R w (membrane (scenery 4 σ) t) v)
        (centeredMassLaw 4 ν)| ≤ A + B * logKernel (u - v) := by
  obtain ⟨A, B, hA, hB, hmesh⟩ := exists_double_heat_mesh_log_bound hPaired (2 * L)
  let q : ℝ := variance id ν
  have hq : 0 ≤ q := variance_nonneg _ _
  let A' : ℝ := q * A
  let B' : ℝ := q * B
  have hA' : 0 ≤ A' := mul_nonneg hq hA
  have hB' : 0 ≤ B' := mul_nonneg hq hB
  have hi : 0 ≤ ∫ z : Space 4, logKernel z := integral_nonneg logKernel_nonneg
  refine ⟨4 * A' + 3 * B' * (W * ∫ z, logKernel z), B', by positivity, hB', ?_⟩
  intro t R hR u v hu hv huv
  let K : Site 4 → Site 4 → ℝ := fun x y =>
    q * ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, heatKernel 4 (a + b) x y
  let a : ℝ := q * doubleHeatReference t R
  let S : Set (Space 4) := {z | ‖z‖ ≤ L}
  let s := supportBox 4 R L
  have hs : ∀ z : Space 4, w z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s :=
    fun z hz => floor_mem_boxFinset R z (hwL z hz)
  have hbound : ∀ x y, x ∈ S → y ∈ S → x ≠ y →
      |K (fun i => ⌊R * x i⌋) (fun i => ⌊R * y i⌋) - a| ≤
        A' + B' * logKernel (x - y) := by
    intro x y hx hy hxy
    have hdist : ‖x - y‖ ≤ 2 * L := by
      have := norm_sub_le x y
      dsimp [S] at hx hy
      linarith
    have h := hmesh t R hR x y (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) hdist
    have hmul := mul_le_mul_of_nonneg_left h hq
    dsimp only [K, a, A', B']
    rw [← mul_sub, abs_mul, abs_of_nonneg hq]
    nlinarith
  have hc := abs_centeredKernel_le_of_log_bound R w hw hw0 hw1 W hwB s hs S
    (fun z hz => hwL z hz) K a A' B' hB' hbound u v hu hv huv
  have hcov := covariance_omegaEmbed_membrane (by norm_num) ν hsq R L w hw hwL t u v
  dsimp only at hc hcov
  rw [hcov]
  dsimp only [K, q, s] at hc
  nlinarith

end Sandpile.Support
