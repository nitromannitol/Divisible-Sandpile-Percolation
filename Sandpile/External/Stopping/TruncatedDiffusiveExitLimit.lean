import Sandpile.External.Stopping.TruncatedExitIndex
import Sandpile.External.Stopping.VaryingFloorTime
import LatticeProb.Walk.ConstantStepInterpolation

/-!
# Diffusive limits of truncated exit clocks

Convergent finite exit clocks remain convergent after truncation at a
parabolically rescaled lattice horizon.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A finite diffusive exit clock truncated at the floored lattice horizon
converges to the minimum of the limiting exit clock and the horizon. -/
theorem tendsto_truncated_diffusive_exit
    {d : ℕ} (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (D : ℕ → Set (Site d)) (X : ℕ → ℕ → Site d) (T τ : ℝ≥0)
    (hfin : ∀ n, Sandpile.exitTime (D n) (X n) ≠ ⊤)
    (hlim : Tendsto (fun n => LatticeProb.ConstantStepInterpolation.knot
      ⟨R n ^ 2, sq_nonneg (R n)⟩ (Sandpile.exitTime (D n) (X n)).toNat) atTop (𝓝 τ)) :
    Tendsto (fun n => walkStopToDiffusiveTime (R n) (hRpos n)
      (stopBeforeExit (D n) ⌊R n ^ 2 * (T : ℝ)⌋₊ (fun _ => ⌊R n ^ 2 * (T : ℝ)⌋₊))
      (X n)) atTop (𝓝 (min τ T)) := by
  have hfloor : Tendsto (fun n => (⌊R n ^ 2 * (T : ℝ)⌋₊ : ℝ≥0) /
      ⟨R n ^ 2, sq_nonneg (R n)⟩) atTop (𝓝 T) := by
    have hre := tendsto_varying_floor_time_div_sq R (fun _ => (T : ℝ)) hR
      (fun _ => T.coe_nonneg) tendsto_const_nhds
    apply (NNReal.tendsto_coe (m := fun n => (⌊R n ^ 2 * (T : ℝ)⌋₊ : ℝ≥0) /
      ⟨R n ^ 2, sq_nonneg (R n)⟩) (x := T)).mp
    have hc (n : ℕ) : (((⌊R n ^ 2 * (T : ℝ)⌋₊ : ℝ≥0) /
        ⟨R n ^ 2, sq_nonneg (R n)⟩ : ℝ≥0) : ℝ) =
        (⌊R n ^ 2 * (T : ℝ)⌋₊ : ℝ) / R n ^ 2 := by
      exact NNReal.coe_div _ _
    have heq : (fun n => (((⌊R n ^ 2 * (T : ℝ)⌋₊ : ℝ≥0) /
        ⟨R n ^ 2, sq_nonneg (R n)⟩ : ℝ≥0) : ℝ)) =
        (fun n => (⌊R n ^ 2 * (T : ℝ)⌋₊ : ℝ) / R n ^ 2) := funext hc
    rw [heq]
    exact hre
  have hmin := hfloor.min hlim
  have heq (n : ℕ) : walkStopToDiffusiveTime (R n) (hRpos n)
      (stopBeforeExit (D n) ⌊R n ^ 2 * (T : ℝ)⌋₊ (fun _ => ⌊R n ^ 2 * (T : ℝ)⌋₊))
      (X n) = min ((⌊R n ^ 2 * (T : ℝ)⌋₊ : ℝ≥0) / ⟨R n ^ 2, sq_nonneg (R n)⟩)
        (LatticeProb.ConstantStepInterpolation.knot ⟨R n ^ 2, sq_nonneg (R n)⟩
          (Sandpile.exitTime (D n) (X n)).toNat) := by
    rw [walkStopToDiffusiveTime, stopBeforeExit_const_eq_min_exitTime_toNat _ _ _ (hfin n)]
    simp only [Nat.cast_min, LatticeProb.ConstantStepInterpolation.knot]
    apply NNReal.coe_injective
    simp only [NNReal.coe_min]
    exact (min_div_div_right (sq_nonneg (R n)) _ _).symm
  simpa only [heq, min_comm] using hmin

end Sandpile.External.Stopping
