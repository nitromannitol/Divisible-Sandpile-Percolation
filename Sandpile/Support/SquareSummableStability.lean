import Mathlib

/-!
# Stability of square-summable coefficient rows

The uniform smallness of the coordinates and the limiting `ℓ²` norm of a
coefficient family are preserved by perturbations whose `ℓ²` norm tends to zero.
This transfers the hypotheses of a weighted central limit theorem from an
infinite potential kernel to finitely supported approximations.
-/

open Filter Topology
open scoped lp ENNReal

namespace Sandpile.Support

/-- If two families in `ℓ²` are asymptotically equal, the norms of their rows
have the same limit. -/
theorem tendsto_norm_of_sub_norm_tendsto_zero {α ι : Type*} (l : Filter α)
    (a b : α → ℓ²(ι, ℝ)) (B : ℝ)
    (hB : Tendsto (fun j => ‖b j‖) l (𝓝 B))
    (hsub : Tendsto (fun j => ‖a j - b j‖) l (𝓝 0)) :
    Tendsto (fun j => ‖a j‖) l (𝓝 B) := by
  have hlo : Tendsto (fun j => ‖b j‖ - ‖a j - b j‖) l (𝓝 B) := by
    simpa only [sub_zero] using hB.sub hsub
  have hhi : Tendsto (fun j => ‖b j‖ + ‖a j - b j‖) l (𝓝 B) := by
    simpa only [add_zero] using hB.add hsub
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · exact Filter.Eventually.of_forall fun j => by
      have h := norm_sub_norm_le (b j) (a j)
      rw [norm_sub_rev] at h
      linarith
  · exact Filter.Eventually.of_forall fun j => by
      have h := norm_sub_norm_le (a j) (b j)
      linarith

/-- A perturbation tending to zero in `ℓ²` preserves uniform convergence of
the coordinates to zero. -/
theorem eventually_coordinate_bound_of_sub_norm_tendsto_zero {α ι : Type*}
    (l : Filter α) (a b : α → ℓ²(ι, ℝ))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ j in l, ∀ i, |b j i| ≤ δ)
    (hsub : Tendsto (fun j => ‖a j - b j‖) l (𝓝 0)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j in l, ∀ i, |a j i| ≤ δ := by
  intro δ hδ
  have herr : ∀ᶠ j in l, ‖a j - b j‖ < δ / 2 :=
    hsub.eventually (gt_mem_nhds (half_pos hδ))
  filter_upwards [hsmall (δ / 2) (by linarith), herr] with j hj he i
  have hcoord : |a j i - b j i| ≤ ‖a j - b j‖ := by
    simpa only [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] using
      lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (a j - b j) i
  have htriangle := abs_add_le (a j i - b j i) (b j i)
  have hsum : |a j i| ≤ |a j i - b j i| + |b j i| := by
    convert htriangle using 1; congr 1; ring
  linarith [hj i]

end Sandpile.Support
