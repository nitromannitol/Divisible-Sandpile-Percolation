import Sandpile.Support.D4LogAverage
import Sandpile.Support.D4KernelCentering
import Sandpile.Support.D4OmegaEmbedCovariance

/-!
# Centered kernels with logarithmic mesh bounds

A kernel with a logarithmic residual after subtracting a spatial constant
retains the same singularity after centering by an averaging density.
-/

open MeasureTheory

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The logarithmic kernel is symmetric under interchange of its arguments. -/
theorem logKernel_sub_comm (u v : Space 4) : logKernel (u - v) = logKernel (v - u) := by
  simp only [logKernel, norm_sub_rev]

/-- Centering a logarithmically controlled lattice kernel preserves its
logarithmic singularity on the bounded set. -/
theorem abs_centeredKernel_le_of_log_bound (R : ℝ) (w : Space 4 → ℝ)
    (hw : Integrable w) (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∫ z, w z = 1)
    (W : ℝ) (hwB : ∀ z, |w z| ≤ W) (s : Finset (Site 4))
    (hs : ∀ z, w z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s)
    (S : Set (Space 4)) (hwS : ∀ z, w z ≠ 0 → z ∈ S)
    (K : Site 4 → Site 4 → ℝ) (a A B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ u v, u ∈ S → v ∈ S → u ≠ v →
      |K (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋) - a| ≤
        A + B * logKernel (u - v))
    (u v : Space 4) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    let x : Site 4 := fun i => ⌊R * u i⌋
    let y : Site 4 := fun i => ⌊R * v i⌋
    let m := cellMass R w
    |K x y - (∑ z ∈ s, m z * K x z) - (∑ z ∈ s, m z * K z y) +
        (∑ z ∈ s, ∑ z' ∈ s, m z * m z' * K z z')| ≤
      A + B * logKernel (u - v) + 3 * (A + B * (W * ∫ z, logKernel z)) := by
  dsimp only
  let m := cellMass R w
  let F : Site 4 → Site 4 → ℝ := fun x y => |K x y - a|
  let x : Site 4 := fun i => ⌊R * u i⌋
  let y : Site 4 := fun i => ⌊R * v i⌋
  let M : ℝ := A + B * (W * ∫ z, logKernel z)
  have hm : ∑ z ∈ s, m z = 1 := by
    rw [sum_cellMass_eq_integral R w hw s hs, hw1]
  have hm0 : ∀ z ∈ s, 0 ≤ m z := by
    intro z _
    exact integral_nonneg fun z => hw0 z
  have hrow : (∑ z ∈ s, m z * F x z) ≤ M := by
    have h := cellMass_sum_le_of_log_bound R w hw hw0 W hwB s hs
      (F x) u A B hB (fun z hz hzu => hbound u z hu (hwS z hz) hzu.symm)
    simpa only [hw1, mul_one] using h
  have hcol : (∑ z ∈ s, m z * F z y) ≤ M := by
    have h := cellMass_sum_le_of_log_bound R w hw hw0 W hwB s hs
      (fun z => F z y) v A B hB (fun z hz hzv => by
        simpa only [logKernel_sub_comm z v] using hbound z v (hwS z hz) hv hzv)
    simpa only [hw1, mul_one] using h
  have hdouble : (∑ z ∈ s, ∑ z' ∈ s, m z * m z' * F z z') ≤ M := by
    have h := double_cellMass_sum_le_of_log_bound R w hw hw0 W hwB s hs F A B hB
      (fun z z' hz hz' hne => hbound z z' (hwS z hz) (hwS z' hz') hne)
    simpa only [hw1, mul_one] using h
  have hpoint : F x y ≤ A + B * logKernel (u - v) := hbound u v hu hv huv
  have h := abs_centeredKernel_le s m hm hm0 K a x y
  change _ ≤ F x y + (∑ z ∈ s, m z * F x z) + (∑ z ∈ s, m z * F z y) +
    (∑ z ∈ s, ∑ z' ∈ s, m z * m z' * F z z') at h
  dsimp only [M] at hrow hcol hdouble
  linarith

end Sandpile.Support
