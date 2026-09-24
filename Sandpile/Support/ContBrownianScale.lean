/-
Brownian scaling of the motion of `ssec:brownian-stopping`.

The proof of `prop:continuum-value-selfsimilar` at `sandpile.tex:1991-1993` reads
"Rescaling time by $T$ identifies Brownian stopping times bounded by $T$ with
Brownian stopping times bounded by $1$".  The map it uses is
`s ↦ T^{-1/2}(B_{Ts}-x)`, and this file proves that it carries a Brownian motion
on `ℝ^d` with generator `Δ/(2d)` started at `x` to one started at the origin.
Each coordinate is Mathlib's `IsBrownianReal.smul`; the independence of the
coordinates is carried along the coordinatewise map.
-/
import Sandpile.Continuum.Stopping

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The rescaled motion starts at the origin. -/
theorem isBrownian_scaled_start {ΩB : Type*} [MeasurableSpace ΩB] (d : ℕ)
    (PB : Measure ΩB) (x : Space d) (B : ℝ≥0 → ΩB → Space d)
    (hB : IsBrownian d x B PB) (T : ℝ≥0) :
    ∀ᵐ ω ∂PB, (Real.sqrt T)⁻¹ • (B (T * 0) ω - x) = (0 : Space d) := by
  filter_upwards [hB.start] with ω hω
  simp [mul_zero, hω]

/-- Each coordinate of the rescaled motion, centred and scaled by `√d`, is a real
Brownian motion.  This is Mathlib's `IsBrownianReal.smul` at `c = T`. -/
theorem isBrownian_scaled_coord {ΩB : Type*} [MeasurableSpace ΩB] (d : ℕ)
    (PB : Measure ΩB) (x : Space d) (B : ℝ≥0 → ΩB → Space d)
    (hB : IsBrownian d x B PB) {T : ℝ≥0} (hT : T ≠ 0) (i : Fin d) :
    IsBrownianReal (fun t ω => Real.sqrt d *
      (((Real.sqrt (T : ℝ))⁻¹ • (B (T * t) ω - x)) i - (0 : Space d) i)) PB := by
  have h := (hB.coord i).smul hT
  have heq : (fun (t : ℝ≥0) (ω : ΩB) => Real.sqrt d *
        (((Real.sqrt (T : ℝ))⁻¹ • (B (T * t) ω - x)) i - (0 : Space d) i))
      = fun (t : ℝ≥0) (ω : ΩB) => (Real.sqrt (T : ℝ))⁻¹ *
        (Real.sqrt d * (B (T * t) ω i - x i)) := by
    funext t ω
    simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.zero_apply, smul_eq_mul, sub_zero]
    ring
  rw [heq]
  simpa using h

/-- The coordinates of the rescaled motion are independent, because they are the
images of the coordinates of `B` under one measurable map of the path. -/
theorem isBrownian_scaled_indep {ΩB : Type*} [MeasurableSpace ΩB] (d : ℕ)
    (PB : Measure ΩB) (x : Space d) (B : ℝ≥0 → ΩB → Space d)
    (hB : IsBrownian d x B PB) (T : ℝ≥0) :
    iIndepFun (fun (i : Fin d) (ω : ΩB) =>
      fun s : ℝ≥0 => ((Real.sqrt (T : ℝ))⁻¹ • (B (T * s) ω - x)) i) PB := by
  have hg : ∀ i : Fin d, Measurable
      (fun p : ℝ≥0 → ℝ => fun s : ℝ≥0 => (Real.sqrt (T : ℝ))⁻¹ * (p (T * s) - x i)) := by
    intro i
    refine measurable_pi_lambda _ fun s => ?_
    have h1 : Measurable (fun p : ℝ≥0 → ℝ => p (T * s)) := measurable_pi_apply (T * s)
    exact (h1.sub_const (x i)).const_mul _
  have h := hB.indep.comp
    (fun i : Fin d => fun p : ℝ≥0 → ℝ => fun s : ℝ≥0 =>
      (Real.sqrt (T : ℝ))⁻¹ * (p (T * s) - x i)) hg
  have heq : (fun (i : Fin d) (ω : ΩB) =>
      fun s : ℝ≥0 => ((Real.sqrt (T : ℝ))⁻¹ • (B (T * s) ω - x)) i)
      = fun (i : Fin d) => (fun p : ℝ≥0 → ℝ => fun s : ℝ≥0 =>
          (Real.sqrt (T : ℝ))⁻¹ * (p (T * s) - x i)) ∘ (fun (ω : ΩB) => fun t : ℝ≥0 => B t ω i) := by
    funext i ω
    funext s
    simp [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  rw [heq]
  exact h

/-- **Brownian scaling of the motion**: `s ↦ T^{-1/2}(B_{Ts}-x)` is a Brownian motion
on `ℝ^d` with generator `Δ/(2d)` started at the origin.  This is the map by which
`sandpile.tex:1991-1993` identifies the stopping times bounded by `T` of the motion
started at `x` with the stopping times bounded by one of a motion started at the
origin. -/
theorem isBrownian_scaled {ΩB : Type*} [MeasurableSpace ΩB] (d : ℕ)
    (PB : Measure ΩB) (x : Space d) (B : ℝ≥0 → ΩB → Space d)
    (hB : IsBrownian d x B PB) {T : ℝ≥0} (hT : T ≠ 0) :
    IsBrownian d 0 (fun s ω => (Real.sqrt (T : ℝ))⁻¹ • (B (T * s) ω - x)) PB where
  start := isBrownian_scaled_start d PB x B hB T
  coord := fun i => isBrownian_scaled_coord d PB x B hB hT i
  indep := isBrownian_scaled_indep d PB x B hB T

/-- Undoing the space rescaling: `x + √T • B'_s = B_{Ts}`. -/
theorem scaled_point_eq {ΩB : Type*} (d : ℕ) {T : ℝ≥0} (hT : T ≠ 0)
    (x : Space d) (B : ℝ≥0 → ΩB → Space d) (s : ℝ≥0) (ω : ΩB) :
    x + Real.sqrt (T : ℝ) • ((Real.sqrt (T : ℝ))⁻¹ • (B (T * s) ω - x)) = B (T * s) ω := by
  have hTpos : (0:ℝ) < (T : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT)
  have hsq : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hTpos)
  rw [smul_smul, mul_inv_cancel₀ hsq, one_smul, add_sub_cancel]

/-- **Rescaling time by `T` carries stopping times of the motion to stopping times of the
rescaled motion.**  This is the first half of `sandpile.tex:1991-1992`. -/
theorem isBrownianStopping_scaled {ΩB : Type*} (d : ℕ) {T : ℝ≥0} (hT : T ≠ 0)
    {c : ℝ} (hc : c ≠ 0) (x : Space d) (B : ℝ≥0 → ΩB → Space d)
    (τ : ΩB → ℝ≥0) (hτ : IsBrownianStopping B τ) :
    IsBrownianStopping (fun s ω => c • (B (T * s) ω - x)) (fun ω => τ ω / T) := by
  intro t
  let B' : ℝ≥0 → ΩB → Sandpile.Continuum.Space d := fun s ω => c • (B (T * s) ω - x)
  have hle : Sandpile.Continuum.brownianFiltration B (T * t) ≤
      Sandpile.Continuum.brownianFiltration B' t := by
    refine Sandpile.Continuum.brownianFiltration_le B (T * t) _ fun s hs => ?_
    have hs' : s / T ≤ t := (div_le_iff₀ (pos_iff_ne_zero.mpr hT)).2
      (by simpa only [mul_comm] using hs)
    have hm := ((Sandpile.Continuum.measurable_brownianFiltration B' (s / T) t hs').const_smul c⁻¹).add_const x
    convert! hm using 1
    funext ω
    dsimp [B']
    rw [mul_div_cancel₀ _ hT, smul_smul, inv_mul_cancel₀ hc, one_smul, sub_add_cancel]
  have hm := hle _ (hτ (T * t))
  convert! hm using 1
  ext ω
  change ((τ ω / T : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞) ↔
    (τ ω : ℝ≥0∞) ≤ ((T * t : ℝ≥0) : ℝ≥0∞)
  rw [ENNReal.coe_le_coe, ENNReal.coe_le_coe, div_le_iff₀ (pos_iff_ne_zero.mpr hT), mul_comm]



/-- The converse: multiplying a stopping time of the rescaled motion by `T` gives a
stopping time of the original one.  Together with the previous lemma this is the
identification of the two families of stopping times. -/
theorem isBrownianStopping_unscaled {ΩB : Type*} (d : ℕ) {T : ℝ≥0}
    {c : ℝ} (x : Space d) (B : ℝ≥0 → ΩB → Space d)
    (σ : ΩB → ℝ≥0) (hσ : IsBrownianStopping (fun s ω => c • (B (T * s) ω - x)) σ) :
    IsBrownianStopping B (fun ω => T * σ ω) := by
  by_cases hT : T = 0
  · subst T
    simpa only [zero_mul] using
      (show Sandpile.Continuum.IsBrownianStopping B (fun _ => 0) from
        isStoppingTime_const (Sandpile.Continuum.brownianFiltration B) (0 : ℝ≥0))
  intro t
  let B' : ℝ≥0 → ΩB → Sandpile.Continuum.Space d := fun s ω => c • (B (T * s) ω - x)
  have hle : Sandpile.Continuum.brownianFiltration B' (t / T) ≤
      Sandpile.Continuum.brownianFiltration B t := by
    refine Sandpile.Continuum.brownianFiltration_le B' (t / T) _ fun s hs => ?_
    have hTs : T * s ≤ t := by
      have h := (le_div_iff₀ (pos_iff_ne_zero.mpr hT)).1 hs
      simpa only [mul_comm] using h
    exact ((Sandpile.Continuum.measurable_brownianFiltration B (T * s) t hTs).sub_const x).const_smul c
  have hm := hle _ (hσ (t / T))
  convert! hm using 1
  ext ω
  change ((T * σ ω : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞) ↔
    (σ ω : ℝ≥0∞) ≤ ((t / T : ℝ≥0) : ℝ≥0∞)
  rw [ENNReal.coe_le_coe, ENNReal.coe_le_coe, le_div_iff₀ (pos_iff_ne_zero.mpr hT), mul_comm]



end Sandpile.Support
