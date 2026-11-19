import Sandpile.External.Stopping.WalkInterpolatedIncrement

/-!
# Deterministic time changes of stopping times

A positive linear time change transports stopping times between the natural
filtrations of a process and its time-changed version.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Multiplying a stopping time by the time-change factor gives a stopping
time for the original process. -/
theorem isBrownianStopping_mul_timeChange {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (c : ℝ≥0) (hc : 0 < c)
    (τ : Ω → ℝ≥0)
    (hτ : Continuum.IsBrownianStopping (fun t => B (c * t)) τ) :
    Continuum.IsBrownianStopping B (fun ω => c * τ ω) := by
  intro s
  have hfil : Continuum.brownianFiltration (fun t => B (c * t)) (s / c) ≤
      Continuum.brownianFiltration B s := by
    apply Continuum.brownianFiltration_le
    intro t ht
    apply Continuum.measurable_brownianFiltration
    have ht' := mul_le_mul_of_nonneg_left ht hc.le
    simpa [mul_div_cancel₀ s hc.ne'] using ht'
  have hset : {ω | ((c * τ ω : ℝ≥0) : ℝ≥0∞) ≤ (s : ℝ≥0∞)} =
      {ω | ((τ ω : ℝ≥0) : ℝ≥0∞) ≤ ((s / c : ℝ≥0) : ℝ≥0∞)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ENNReal.coe_le_coe]
    exact (le_div_iff₀' hc).symm
  change MeasurableSet[Continuum.brownianFiltration B s]
    {ω | ((c * τ ω : ℝ≥0) : ℝ≥0∞) ≤ (s : ℝ≥0∞)}
  rw [hset]
  exact hfil _ (hτ (s / c))

/-- The linearly interpolated rescaled walk in diffusive time. -/
noncomputable def diffusiveWalk {d : ℕ} (R : ℝ) (t : ℝ≥0) (X : ℕ → Site d) :
    Continuum.Space d :=
  linearWalk R (⟨R ^ 2, sq_nonneg R⟩ * t) X

/-- In diffusive time, increments after bounded stopping times are uniformly
small in probability as the interval shrinks and the scale tends to infinity. -/
theorem diffusiveWalk_increment_small (d : ℕ) (hd : 1 ≤ d) (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ R₀ : ℝ, 0 < δ ∧ 0 < R₀ ∧
      ∀ (R : ℝ), R₀ ≤ R → ∀ (H : ℝ≥0) (x : Site d)
        (τ σ : (ℕ → Site d) → ℝ≥0),
        Continuum.IsBrownianStopping (diffusiveWalk R) τ →
        (∀ X, τ X ≤ H) →
        (∀ X, τ X ≤ σ X ∧ (σ X : ℝ) ≤ (τ X : ℝ) + δ) →
        walkLaw d x {X | ε ≤ ‖diffusiveWalk R (σ X) X - diffusiveWalk R (τ X) X‖} ≤
          ENNReal.ofReal η := by
  obtain ⟨δ, R₀, hδ, hR₀, hsmall⟩ := linearWalk_increment_small d hd ε η hε hη
  refine ⟨δ, R₀, hδ, hR₀, ?_⟩
  intro R hR H x τ σ hτ hτH hτσ
  have hRpos : 0 < R := hR₀.trans_le hR
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hc : 0 < c := by
    change (0 : ℝ) < R ^ 2
    positivity
  have hstop : Continuum.IsBrownianStopping (linearWalk R) (fun X => c * τ X) :=
    isBrownianStopping_mul_timeChange (linearWalk R) c hc τ hτ
  have hbound : ∀ X, c * τ X ≤ c * H := fun X => mul_le_mul_of_nonneg_left (hτH X) hc.le
  have hshort : ∀ X, c * τ X ≤ c * σ X ∧
      ((c * σ X : ℝ≥0) : ℝ) ≤ ((c * τ X : ℝ≥0) : ℝ) + δ * R ^ 2 := by
    intro X
    refine ⟨mul_le_mul_of_nonneg_left (hτσ X).1 hc.le, ?_⟩
    have hm := mul_le_mul_of_nonneg_left (hτσ X).2 (sq_nonneg R)
    change R ^ 2 * (σ X : ℝ) ≤ R ^ 2 * (τ X : ℝ) + δ * R ^ 2
    nlinarith
  simpa [diffusiveWalk, c] using hsmall R hR (c * H) x
    (fun X => c * τ X) (fun X => c * σ X) hstop hbound hshort

end Sandpile.External.Stopping
