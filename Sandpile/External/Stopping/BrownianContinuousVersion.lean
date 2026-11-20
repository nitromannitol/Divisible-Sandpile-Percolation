import Sandpile.External.Stopping.AECubeClockStopping

/-!
# Continuous versions of sandpile Brownian motion

Every sandpile Brownian motion in positive dimension has an indistinguishable
measurable realization whose paths are continuous everywhere.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Sandpile.External.Stopping

/-- A sandpile Brownian motion has an indistinguishable everywhere-continuous
realization which is itself a sandpile Brownian motion. -/
theorem exists_continuous_sandpile_brownian_version
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    {P : Measure Ω} [IsProbabilityMeasure P] {x : Continuum.Space d}
    {B : ℝ≥0 → Ω → Continuum.Space d} (hB : Continuum.IsBrownian d x B P) :
    ∃ V : ℝ≥0 → Ω → Continuum.Space d,
      (∀ t, Measurable (V t)) ∧ (∀ ω, Continuous fun t => V t ω) ∧
      (∀ᵐ ω ∂P, ∀ t, B t ω = V t ω) ∧ Continuum.IsBrownian d x V P := by
  have hBL : LatticeProb.IsBrownianSpace d x B P := ⟨hB.start, hB.coord, hB.indep⟩
  obtain ⟨C, hCm, hCc, _, hCeq, _, _⟩ := hBL.exists_continuousVersion
  have hd : (Real.sqrt (d : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)))
  let V : ℝ≥0 → Ω → Continuum.Space d := fun t ω => x + (Real.sqrt d)⁻¹ • C t ω
  have hVm : ∀ t, Measurable (V t) := fun t =>
    measurable_const.add ((measurable_const : Measurable (fun _ : Ω => (Real.sqrt d)⁻¹)).smul (hCm t))
  have hVc : ∀ ω, Continuous fun t => V t ω := fun ω =>
    continuous_const.add ((continuous_const : Continuous (fun _ : ℝ≥0 => (Real.sqrt d)⁻¹)).smul (hCc ω))
  have hBV : ∀ᵐ ω ∂P, ∀ t, B t ω = V t ω := by
    filter_upwards [hCeq] with ω hω t
    change B t ω = x + (Real.sqrt d)⁻¹ • C t ω
    rw [hω t, smul_smul, inv_mul_cancel₀ hd, one_smul, add_sub_cancel]
  refine ⟨V, hVm, hVc, hBV, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hB.start, hBV] with ω hs heq
    rw [← heq 0]
    exact hs
  · intro i
    refine ⟨(hB.coord i).toIsPreBrownianReal.congr (fun t => ?_), ?_⟩
    · filter_upwards [hBV] with ω heq
      rw [heq t]
    · filter_upwards with ω
      exact continuous_const.mul (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp
        (hVc ω)).sub continuous_const)
  · apply (iIndepFun_congr fun i => ?_).mp hB.indep
    filter_upwards [hBV] with ω heq
    funext t
    rw [heq t]

end Sandpile.External.Stopping
