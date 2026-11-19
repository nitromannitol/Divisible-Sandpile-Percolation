import Sandpile.External.Stopping.BrownianCubeExit
import Sandpile.External.Stopping.RegularExitTime
import Sandpile.Continuum.Stopping

/-!
# Sandpile Brownian motion exits cubes regularly

For Brownian motion with generator `Δ/(2d)`, its first exit from the open unit
cube centered at its starting point is finite and is followed immediately by a
strict exit from the closed cube. The coordinate normalization is the one used
in `Sandpile.Continuum.IsBrownian`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The first exit of sandpile Brownian motion from its centered open unit cube
is finite, and the path goes strictly outside the closed cube immediately. -/
theorem ae_sandpile_brownian_cube_exit_regular
    {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {x : Continuum.Space d} {B : ℝ≥0 → Ω → Continuum.Space d}
    (hB : Continuum.IsBrownian d x B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) :
    ∀ᵐ ω ∂P,
      let U : Set (Continuum.Space d) := {z | ∀ i, |z i - x i| < 1}
      let τ := LatticeProb.openExitTime B U ω
      τ ≠ ⊤ ∧
        (∀ s : ℝ≥0, s < τ.toNNReal → ∀ i, |B s ω i - x i| < 1) ∧
        (∀ t : ℝ≥0, τ.toNNReal < t →
          ∃ s : ℝ≥0, s < t ∧ ∃ i, 1 < |B s ω i - x i|) := by
  have hd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  let D : Fin d → ℝ≥0 → Ω → ℝ := fun i t ω => Real.sqrt d * (B t ω i - x i)
  have hDm (i : Fin d) (t : ℝ≥0) : Measurable (D i t) := by
    exact measurable_const.mul (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable.comp (hm t)).sub measurable_const)
  have hDc (i : Fin d) (ω : Ω) : Continuous fun t => D i t ω := by
    exact continuous_const.mul (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp (hc ω)).sub continuous_const)
  filter_upwards [ae_brownian_cube_regular D (Real.sqrt d) hB.coord hDm hDc] with ω hω
  obtain ⟨σ, hbefore, hafter⟩ := hω
  have hbefore' : ∀ s : ℝ≥0, s < σ → ∀ i, |B s ω i - x i| < 1 := by
    intro s hs i
    have h := hbefore s hs i
    change |Real.sqrt d * (B s ω i - x i)| < Real.sqrt d at h
    rw [abs_mul, abs_of_pos hd] at h
    have h' : Real.sqrt d * |B s ω i - x i| < Real.sqrt d * 1 := by simpa only [mul_one] using h
    nlinarith [h']
  have hafter' : ∀ t : ℝ≥0, σ < t →
      ∃ s : ℝ≥0, s < t ∧ ∃ i, 1 < |B s ω i - x i| := by
    intro t ht
    obtain ⟨s, hs, i, hi⟩ := hafter t ht
    refine ⟨s, hs, i, ?_⟩
    change Real.sqrt d < |Real.sqrt d * (B s ω i - x i)| at hi
    rw [abs_mul, abs_of_pos hd] at hi
    have hi' : Real.sqrt d * 1 < Real.sqrt d * |B s ω i - x i| := by simpa only [mul_one] using hi
    nlinarith [hi']
  let U : Set (Continuum.Space d) := {z | ∀ i, |z i - x i| < 1}
  have heq : LatticeProb.openExitTime B U ω = (σ : ℝ≥0∞) := by
    apply openExitTime_eq_of_regular B U ω σ
    · exact hbefore'
    · intro t ht
      obtain ⟨s, hs, i, hi⟩ := hafter' t ht
      exact ⟨s, hs, fun h => (not_lt_of_ge (h i).le) hi⟩
  change LatticeProb.openExitTime B U ω ≠ ⊤ ∧ _
  rw [heq]
  refine ⟨ENNReal.coe_ne_top, ?_, ?_⟩
  · simpa only [ENNReal.toNNReal_coe] using hbefore'
  · simpa only [ENNReal.toNNReal_coe] using hafter'

end Sandpile.External.Stopping
