import Sandpile.External.Stopping.SandpileBrownianCubeExit
import LatticeProb.Prob.BrownianPathCoords

/-!
# Almost-sure regularity of Brownian cube exits

A finite family of Brownian coordinates exits its cube regularly even when
continuity and measurability are available only up to modification.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Brownian coordinates have a regular cube exit without any choice of
pointwise continuous versions in the statement. -/
theorem ae_brownian_cube_regular_of_brownian {ι Ω : Type*} [Finite ι] [Nonempty ι]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ι → ℝ≥0 → Ω → ℝ) (a : ℝ)
    (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, ∃ τ : ℝ≥0,
      (∀ s : ℝ≥0, s < τ → ∀ i, |B i s ω| < a) ∧
      (∀ t : ℝ≥0, τ < t → ∃ s : ℝ≥0, s < t ∧ ∃ i, a < |B i s ω|) := by
  choose C hCm hCB hCeq hCc using fun i =>
    LatticeProb.IsBrownianReal.exists_continuous_indistinguishable (hB i)
  filter_upwards [ae_brownian_cube_regular C a hCB hCm hCc, ae_all_iff.mpr hCeq] with ω hreg heq
  obtain ⟨τ, hbefore, hafter⟩ := hreg
  refine ⟨τ, ?_, ?_⟩
  · intro s hs i
    rw [heq i s]
    exact hbefore s hs i
  · intro t ht
    obtain ⟨s, hs, i, hi⟩ := hafter t ht
    exact ⟨s, hs, i, by rw [heq i s]; exact hi⟩

/-- The first exit of a Brownian motion from its centered unit cube is finite
and is followed immediately by a strict exit, almost surely. -/
theorem ae_sandpile_brownian_cube_exit_regular_of_brownian
    {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {x : Continuum.Space d} {B : ℝ≥0 → Ω → Continuum.Space d}
    (hB : Continuum.IsBrownian d x B P) :
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
  filter_upwards [ae_brownian_cube_regular_of_brownian D (Real.sqrt d) hB.coord] with ω hω
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
