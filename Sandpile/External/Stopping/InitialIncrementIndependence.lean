import Sandpile.External.Stopping.StepWalkIndependence
import Sandpile.Support.KillBox

/-!
# Independence including the initial position

For a process with independent increments and deterministic initial position,
the initial observation and subsequent increments are independent. This is the
increment convention used in Coquet, Mémin and Słomiński, *On weak convergence
of filtrations*, Proposition 2.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- A deterministic starting point lets independent increments include the
first observed position. -/
theorem iIndepFun_initial_and_increments
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hX : HasIndepIncrements X P) (x : E) (hzero : X 0 =ᵐ[P] fun _ => x)
    (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    iIndepFun (Fin.cons (α := fun _ => Ω → E) (X (t 0))
      ((fun i ω => X (t i.succ) ω - X (t i.castSucc) ω) : Fin n → Ω → E)) P := by
  let u : Fin (n + 2) → ℝ≥0 := Fin.cons 0 t
  have hu : Monotone u := by
    apply Fin.monotone_iff_le_succ.2
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [u]
    · simpa [u] using ht (Fin.castSucc_le_succ j)
  have hind := hX (n + 1) u hu
  let adjust : Fin (n + 1) → E → E := Fin.cons (fun z => z + x) (fun _ z => z)
  have hcombined := hind.comp adjust (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_id.add measurable_const
    · exact measurable_id)
  apply hcombined.congr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · filter_upwards [hzero] with ω hω
    simp [adjust, u, hω]
  · filter_upwards [] with ω
    simp [adjust, u]

/-- The diffusively rescaled step walk has independent initial observation and
subsequent increments under its walk law. -/
theorem iIndepFun_diffusiveStepWalk_initial_and_increments {d : ℕ} [NeZero d]
    (R : ℝ) (q : Site d) (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    iIndepFun (Fin.cons (α := fun _ => (ℕ → Site d) → Continuum.Space d)
      (diffusiveStepWalk R (t 0))
      ((fun i X => diffusiveStepWalk R (t i.succ) X -
        diffusiveStepWalk R (t i.castSucc) X) : Fin n → (ℕ → Site d) → Continuum.Space d))
      (walkLaw d q) := by
  apply iIndepFun_initial_and_increments (walkLaw d q) (diffusiveStepWalk R)
    (hasIndepIncrements_diffusiveStepWalk R q) (Lclt.scaledSite R q)
  · filter_upwards [ae_walk_start q] with X hX
    let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
    change stepWalk R (c * 0) X = _
    rw [mul_zero]
    simpa only [stepWalk, NNReal.coe_zero, Nat.floor_zero] using
      congrArg (Lclt.scaledSite R) hX
  · exact ht

end Sandpile.External.Stopping
