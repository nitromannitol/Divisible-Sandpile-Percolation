import Sandpile.External.LocalCLT

/-!
# Scaled lattice starting sites

Rounding each coordinate down to the lattice changes a rescaled starting site
by at most one mesh step in each coordinate.
-/

open Filter Topology

namespace Sandpile.External.Stopping

/-- If starting points converge and scales diverge, their rounded rescaled
lattice sites converge to the same limit. -/
theorem tendsto_scaled_floor_start {d : ℕ} (R : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) (x : ℕ → Continuum.Space d)
    (a : Continuum.Space d) (hx : Tendsto x atTop (𝓝 a)) :
    Tendsto (fun n => Lclt.scaledSite (R n) (fun i => ⌊R n * x n i⌋)) atTop (𝓝 a) := by
  have hi : ∀ i : Fin d, Tendsto (fun n => ((⌊R n * x n i⌋ : ℤ) : ℝ) / R n)
      atTop (𝓝 (a i)) := by
    intro i
    have hxi := (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).continuousAt.tendsto.comp hx
    have hinv : Tendsto (fun n => 1 / R n) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hR
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hxi.sub hinv) hxi ?_ ?_
    · filter_upwards [hR.eventually_gt_atTop 0] with n hn
      have hf := Int.lt_floor_add_one (R n * x n i)
      rw [le_div_iff₀ hn]
      have hdiv : (1 / R n) * R n = 1 := by field_simp
      simp only [one_div] at hdiv
      nlinarith
    · filter_upwards [hR.eventually_gt_atTop 0] with n hn
      have hf := Int.floor_le (R n * x n i)
      rw [div_le_iff₀ hn]
      simpa only [Function.comp_apply, mul_comm] using hf
  have hpi : Tendsto (fun n i => ((⌊R n * x n i⌋ : ℤ) : ℝ) / R n)
      atTop (𝓝 (fun i => a i)) := tendsto_pi_nhds.mpr hi
  have h := (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).continuousAt.tendsto.comp hpi
  simpa only [Function.comp_def, Lclt.scaledSite, WithLp.toLp_ofLp] using h

end Sandpile.External.Stopping
