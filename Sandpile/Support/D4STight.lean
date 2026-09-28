import Sandpile.Support.Concentration
import Sandpile.Support.Stationary
import Sandpile.Support.Dgt4OriginProb

/-!
# The uniform second moment of the centred odometer at small scales

The uniform second moment of the centred odometer over a bounded range of times
(`exists_uniform_second_moment_le`), the input the tightness clause of
`prop:d4-superdiffusive-limit` (`sandpile.tex:3324-3327`) needs at the small scales. Steps 2 and 3
send the two error terms to zero only as `R\to\infty`, while the tightness clause of the
proposition quantifies over every `R\geq1`. At the scales below any fixed `R_0` the time
`t_R=\lfloor R^\alpha\rfloor` is at most `\lfloor R_0^\alpha\rfloor` and the mesh meets at most a
fixed box, so the crude second moment of the centred odometer, uniform in the site and taken over
the finitely many times below `t_0`, bounds the whole field there. That second moment is clause
three of `prop:finite-time-concentration-scale`, whose bound is the membrane variance at the same
time.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- **The centred odometer has a second moment uniform in the site and bounded
over any range of times.**  The bound is the largest membrane variance over the
range, which is a finite maximum. -/
theorem exists_uniform_second_moment_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν) (t₀ : ℕ) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ t : ℕ, t ≤ t₀ → ∀ x : Site d,
      Integrable (fun ζ => (odometerOf ζ t x -
        ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)) ^ 2) (LatticeProb.iidLaw d ν) ∧
      ∫ ζ, (odometerOf ζ t x -
        ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)) ^ 2
          ∂(LatticeProb.iidLaw d ν) ≤ V := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_odometer_moment_variance (d := d) ν (p := 2) le_rfl
    (integrable_abs_rpow_two ν hsq)
  set s : Finset ℕ := Finset.range (t₀ + 1) with hs
  have hsne : s.Nonempty := ⟨0, by simp [hs]⟩
  set vmax : ℝ := s.sup' hsne
    (fun t => variance (fun ζ => membrane ζ t 0) (LatticeProb.iidLaw d ν)) with hvmax
  have hvmax0 : (0:ℝ) ≤ vmax := by
    have h0 : (0:ℝ) ≤ variance (fun ζ : Site d → ℝ => membrane ζ 0 0)
        (LatticeProb.iidLaw d ν) := variance_nonneg _ _
    have h1 : variance (fun ζ : Site d → ℝ => membrane ζ 0 0) (LatticeProb.iidLaw d ν) ≤ vmax :=
      Finset.le_sup' (fun t => variance (fun ζ : Site d → ℝ => membrane ζ t 0)
        (LatticeProb.iidLaw d ν)) (show 0 ∈ s by simp [hs])
    linarith
  refine ⟨C * vmax, by positivity, ?_⟩
  intro t ht x
  have hmem : MemLp (fun ζ : Site d → ℝ => odometerOf ζ t x) 2 (LatticeProb.iidLaw d ν) :=
    memLp_two_odometerOf ν hsq t x
  have hint : Integrable (fun ζ => (odometerOf ζ t x -
      ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)) ^ 2) (LatticeProb.iidLaw d ν) := by
    have hsub : MemLp (fun ζ : Site d → ℝ => odometerOf ζ t x -
        ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)) 2 (LatticeProb.iidLaw d ν) :=
      hmem.sub (memLp_const _)
    exact hsub.integrable_sq
  refine ⟨hint, ?_⟩
  have hmean : ∫ η, odometerOf η t x ∂(LatticeProb.iidLaw d ν)
      = ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν) := integral_odometerOf_eq d ν t x
  have hbx := hb t x
  rw [hmean] at hbx
  have hrw : ∀ ζ : Site d → ℝ, |odometerOf ζ t x -
      ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)| ^ (2:ℝ)
      = (odometerOf ζ t x - ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)) ^ 2 := by
    intro ζ
    set a : ℝ := odometerOf ζ t x - ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν) with ha
    have h1 : |a| ^ (2:ℝ) = |a| ^ (2:ℕ) := by
      have hcast : ((2:ℕ) : ℝ) = (2:ℝ) := by norm_num
      have h := Real.rpow_natCast |a| 2
      rw [hcast] at h
      exact h
    rw [h1, sq_abs]
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw)] at hbx
  refine le_trans hbx ?_
  have hexp : variance (fun ζ => membrane ζ t 0) (LatticeProb.iidLaw d ν) ^ ((2:ℝ) / 2)
      = variance (fun ζ => membrane ζ t 0) (LatticeProb.iidLaw d ν) := by
    norm_num
  rw [hexp]
  refine mul_le_mul_of_nonneg_left ?_ hC.le
  exact Finset.le_sup' (fun t => variance (fun ζ => membrane ζ t 0)
    (LatticeProb.iidLaw d ν)) (by simp [hs]; omega)

end Sandpile
