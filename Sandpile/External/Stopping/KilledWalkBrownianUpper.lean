import Sandpile.External.Stopping.KilledWalkValueSubsequence
import Sandpile.External.Stopping.BrownianPathLawBrownian
import Sandpile.External.Stopping.WalkBrownianUpper
import Sandpile.External.Stopping.CubeStoppingValueLaw
import Sandpile.External.Stopping.KilledRewardApproximation

/-!
# Brownian upper bounds for killed walk values

The Brownian invariance principle identifies the upper limit of killed walk
values with the cube stopping value of a continuous Brownian realization.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Killed grid values are eventually bounded by a continuous Brownian cube
value along converging starting points and horizons. -/
theorem eventually_killed_grid_value_le_continuous_brownian_cube
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d a B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    (T : ℝ≥0) (H : ℕ → ℝ≥0) (hH : Tendsto H atTop (𝓝 T))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, killedStoppingSup (supBox (q n) (R n)) ⌊R n ^ 2 * (H n : ℝ)⌋₊
      (q n) (fun k X => G
        (((⌊R n ^ 2 * (H n : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
        (Lclt.scaledSite (R n) (X k))) ≤
      Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 a + ε := by
  let V : ℝ≥0 → Ω → Continuum.Space d := fun t ω => B t ω - a
  obtain ⟨F, hFm, hF, hpath⟩ := exists_brownian_path_limit d R q hR a hstart P V
    (isBrownianSpace_sub_start hB)
  let ν : ProbabilityMeasure C(ℝ≥0, Continuum.Space d) :=
    ⟨P.map F, (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).2 inferInstance⟩
  let E : ℝ≥0 → C(ℝ≥0, Continuum.Space d) → Continuum.Space d := fun t f => f t
  have hEc : ∀ f, Continuous fun t => E t f := fun f => f.continuous
  have hpathmap : P.map F = P.map (LatticeProb.pathMap B hc) := by
    apply Measure.map_congr
    filter_upwards [hF] with ω hω
    apply ContinuousMap.ext
    intro t
    change F ω t = B t ω
    rw [hω t]
    dsimp [V]
    exact add_sub_cancel a (B t ω)
  have hEB : Continuum.IsBrownian d a E (ν : Measure _) := by
    change Continuum.IsBrownian d a E (P.map F)
    rw [hpathmap]
    exact isBrownian_eval_pathMap P a B hB hm hc
  have hElaw : (ν : Measure C(ℝ≥0, Continuum.Space d)).map (LatticeProb.pathMap E hEc) =
      P.map (LatticeProb.pathMap B hc) := by
    have heq : LatticeProb.pathMap E hEc = id := by
      funext f
      exact ContinuousMap.ext (fun _ => rfl)
    rw [heq, Measure.map_id]
    exact hpathmap
  have hval := brownianDiscountCube_eq_of_path_law_eq (ν : Measure _) P a E B hEB hB
    (fun t => (continuous_eval_const t).measurable) hm hEc hc hElaw T G hGc M hG
  obtain ⟨C, hC⟩ := hH.bddAbove_range
  let c : ℝ≥0 := C + 1
  have hc' : 0 < c := by dsimp [c]; positivity
  have hHc (n : ℕ) : H n ≤ c := (hC ⟨n, rfl⟩).trans (le_add_of_nonneg_right zero_le)
  have h := eventually_killed_walk_value_le_brownian_cube R hRpos hR q H T c hc' hH hHc
    ν hpath a hstart hEB rationalStoppingTime rationalStoppingTime_dense G hGc M hG ε hε
  change ∀ᶠ n in atTop, _ < Continuum.brownianDiscountCube E (ν : Measure _)
    (fun s z => -G s z) T 1 a + ε at h
  rw [hval] at h
  exact h.mono (fun _ hn => hn.le)

/-- Uniformly approximating rewards retain the sequential killed-grid upper
bound for a continuous Brownian realization. -/
theorem eventually_approx_killed_grid_value_le_continuous_brownian_cube
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d a B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    (T : ℝ≥0) (H : ℕ → ℝ≥0) (hH : Tendsto H atTop (𝓝 T))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (G' : ℕ → ℝ → Continuum.Space d → ℝ) (M : ℝ)
    (hG : ∀ s z, |G s z| ≤ M) (hG' : ∀ n s z, |G' n s z| ≤ M)
    (happrox : ∀ ε > 0, ∀ᶠ n in atTop, ∀ s ∈ Set.Icc (0 : ℝ) (H n : ℝ),
      ∀ z, |G s z - G' n s z| ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, killedStoppingSup (supBox (q n) (R n)) ⌊R n ^ 2 * (H n : ℝ)⌋₊
      (q n) (fun k X => G' n
        (((⌊R n ^ 2 * (H n : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
        (Lclt.scaledSite (R n) (X k))) ≤
      Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 a + ε := by
  have hupper := eventually_killed_grid_value_le_continuous_brownian_cube
    R q hRpos hR a hstart P B hB hm hc T H hH G hGc M hG (ε / 2) (by positivity)
  filter_upwards [hupper, happrox (ε / 2) (by positivity)] with n hn ha
  have hcmp := abs_killedGridReward_sub_le_of_uniform (hRpos n) (supBox (q n) (R n)) (q n)
    (H n : ℝ) M (ε / 2) (H n).property G (G' n) hG (hG' n)
    (fun s hs z => ha s hs z)
  linarith [(abs_le.mp hcmp).1]

end Sandpile.External.Stopping
