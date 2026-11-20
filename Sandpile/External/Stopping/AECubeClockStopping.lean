import Sandpile.External.Stopping.AECubeClockConstraint

/-!
# Almost-sure cube exit stopping events

The truncated cube exit of Brownian motion is a stopping time up to null sets
for its raw natural filtration, even when exceptional paths are discontinuous.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- An event in the natural filtration of an indistinguishable process has an
almost surely equal representative in the original natural filtration. -/
theorem exists_brownianFiltration_event_of_indistinguishable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    (B C : ℝ≥0 → Ω → Continuum.Space d)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω) (t : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[Continuum.brownianFiltration C t] A) :
    ∃ D : Set Ω, MeasurableSet[Continuum.brownianFiltration B t] D ∧ A =ᵐ[P] D := by
  rw [Continuum.brownianFiltration, Filtration.natural_eq_comap] at hA
  obtain ⟨S, hS, rfl⟩ := hA
  refine ⟨(fun ω (s : Set.Iic t) => B s ω) ⁻¹' S, ?_, ?_⟩
  · rw [Continuum.brownianFiltration, Filtration.natural_eq_comap]
    exact ⟨S, hS, rfl⟩
  · filter_upwards [hBC] with ω hω
    apply propext
    change ((fun s : Set.Iic t => C s ω) ∈ S) ↔
      ((fun s : Set.Iic t => B s ω) ∈ S)
    rw [show (fun s : Set.Iic t => B s ω) = (fun s : Set.Iic t => C s ω) from
      funext fun s => hω s]

/-- A finite stopping time of an indistinguishable process has events agreeing
almost surely with events of the original process's natural filtration. -/
theorem ae_stopping_events_of_indistinguishable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    (B C : ℝ≥0 → Ω → Continuum.Space d)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω)
    (τ : Ω → ℝ≥0) (hτ : Continuum.IsBrownianStopping C τ) (t : ℝ≥0) :
    ∃ D : Set Ω, MeasurableSet[Continuum.brownianFiltration B t] D ∧
      {ω | τ ω ≤ t} =ᵐ[P] D := by
  apply exists_brownianFiltration_event_of_indistinguishable B C hBC t
  have h := hτ t
  change MeasurableSet[Continuum.brownianFiltration C t]
    {ω | (τ ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)} at h
  have heq : {ω | (τ ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)} = {ω | τ ω ≤ t} := by
    ext ω
    exact ENNReal.coe_le_coe
  rw [heq] at h
  exact h

/-- The horizon-truncated open-cube exit of Brownian motion has stopping events
up to null sets in its natural filtration. -/
theorem ae_stopping_events_openUnitCubeExitTrunc
    {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {x : Continuum.Space d} {B : ℝ≥0 → Ω → Continuum.Space d}
    (hB : Continuum.IsBrownian d x B P) (T t : ℝ≥0) :
    ∃ D : Set Ω, MeasurableSet[Continuum.brownianFiltration B t] D ∧
      {ω | (min (LatticeProb.openExitTime B (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal ≤ t} =ᵐ[P] D := by
  have hBL : LatticeProb.IsBrownianSpace d x B P := ⟨hB.start, hB.coord, hB.indep⟩
  obtain ⟨C, _, hCc, _, hCeq, _, _⟩ := hBL.exists_continuousVersion
  have hd : (Real.sqrt (d : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)))
  let V : ℝ≥0 → Ω → Continuum.Space d := fun s ω => x + (Real.sqrt d)⁻¹ • C s ω
  have hVc : ∀ ω, Continuous fun s => V s ω := by
    intro ω
    exact continuous_const.add ((continuous_const : Continuous (fun _ : ℝ≥0 => (Real.sqrt d)⁻¹)).smul (hCc ω))
  have hBV : ∀ᵐ ω ∂P, ∀ s, B s ω = V s ω := by
    filter_upwards [hCeq] with ω hω s
    change B s ω = x + (Real.sqrt d)⁻¹ • C s ω
    rw [hω s, smul_smul, inv_mul_cancel₀ hd, one_smul, add_sub_cancel]
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (LatticeProb.openExitTime V (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal
  obtain ⟨D, hD, hDeq⟩ := ae_stopping_events_of_indistinguishable B V hBV τ
    (isBrownianStopping_openUnitCubeExitTrunc V hVc x T) t
  refine ⟨D, hD, ?_⟩
  filter_upwards [hBV, hDeq] with ω hω hDω
  have hpath : (fun s => B s ω) = fun s => V s ω := funext hω
  have hexit : LatticeProb.openExitTime B (openUnitCube x) ω =
      LatticeProb.openExitTime V (openUnitCube x) ω := by
    exact congrArg (fun f : ℝ≥0 → Continuum.Space d =>
      LatticeProb.openExitTime (fun s (_ : Unit) => f s) (openUnitCube x) ()) hpath
  apply propext
  rw [hexit]
  exact iff_of_eq hDω

end Sandpile.External.Stopping
