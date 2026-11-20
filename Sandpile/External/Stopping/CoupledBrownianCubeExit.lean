import Sandpile.External.Stopping.BrownianPathLawTransfer
import Sandpile.External.Stopping.BrownianCubeExit
import Sandpile.External.Stopping.RegularExitTime
import Sandpile.External.Stopping.CubeStoppedPathLimit

/-!
# Cube exits of coupled Brownian paths

A continuous path with the same law as a continuous version of sandpile
Brownian motion has a finite, regular unit-cube exit. This applies in
particular to the limit in the centered walk coupling.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Any continuous realization of the Brownian path law has a finite regular
exit from the open unit cube. -/
theorem ae_equalLaw_brownian_unitCube_exit_regular
    {d : ℕ} [NeZero d] {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : LatticeProb.IsBrownianSpace d 0 B P)
    (F : Ω → C(ℝ≥0, Continuum.Space d)) (hFm : Measurable F)
    (hF : ∀ᵐ ω ∂P, ∀ t, F ω t = B t ω)
    (Y : Ω' → C(ℝ≥0, Continuum.Space d)) (hYm : Measurable Y)
    (hmap : Q.map Y = P.map F) :
    ∀ᵐ ω ∂Q,
      let τ := LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω
      τ ≠ ⊤ ∧
        (∀ s : ℝ≥0, s < τ.toNNReal → ∀ i, |Y ω s i| < 1) ∧
        (∀ t : ℝ≥0, τ.toNNReal < t → ∃ s : ℝ≥0, s < t ∧ ∃ i, 1 < |Y ω s i|) := by
  have hd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  let φ : Fin d → C(ℝ≥0, Continuum.Space d) → ℝ≥0 → ℝ :=
    fun i f t => Real.sqrt d * f t i
  have hφm (i : Fin d) (t : ℝ≥0) : Measurable (fun f => φ i f t) := by
    exact measurable_const.mul ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable.comp
      (continuous_eval_const t).measurable)
  have hφc (i : Fin d) (f : C(ℝ≥0, Continuum.Space d)) : Continuous (φ i f) := by
    exact continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp f.continuous)
  have hsource (i : Fin d) : IsBrownianReal (fun t ω => φ i (F ω) t) P := by
    refine ⟨?_, Filter.Eventually.of_forall fun ω => hφc i (F ω)⟩
    apply (hB.coord i).toIsPreBrownianReal.congr
    intro t
    filter_upwards [hF] with ω hω
    change Real.sqrt d * (B t ω i - 0) = Real.sqrt d * F ω t i
    rw [hω t, sub_zero]
  have htarget (i : Fin d) : IsBrownianReal (fun t ω => φ i (Y ω) t) Q :=
    isBrownianReal_of_same_path_law hFm hYm hmap (φ i) (hφm i) (hφc i) (hsource i)
  let D : Fin d → ℝ≥0 → Ω' → ℝ := fun i t ω => φ i (Y ω) t
  have hDm (i : Fin d) (t : ℝ≥0) : Measurable (D i t) := (hφm i t).comp hYm
  have hDc (i : Fin d) (ω : Ω') : Continuous fun t => D i t ω := hφc i (Y ω)
  filter_upwards [ae_brownian_cube_regular D (Real.sqrt d) htarget hDm hDc] with ω hω
  obtain ⟨σ, hbefore, hafter⟩ := hω
  have hbefore' : ∀ s : ℝ≥0, s < σ → ∀ i, |Y ω s i| < 1 := by
    intro s hs i
    have hi := hbefore s hs i
    change |Real.sqrt d * Y ω s i| < Real.sqrt d at hi
    rw [abs_mul, abs_of_pos hd] at hi
    nlinarith
  have hafter' : ∀ t : ℝ≥0, σ < t → ∃ s : ℝ≥0, s < t ∧ ∃ i, 1 < |Y ω s i| := by
    intro t ht
    obtain ⟨s, hs, i, hi⟩ := hafter t ht
    refine ⟨s, hs, i, ?_⟩
    change Real.sqrt d < |Real.sqrt d * Y ω s i| at hi
    rw [abs_mul, abs_of_pos hd] at hi
    nlinarith
  have heq : LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω = (σ : ℝ≥0∞) := by
    apply openExitTime_eq_of_regular _ _ _ σ
    · intro s hs i
      simpa using hbefore' s hs i
    · intro t ht
      obtain ⟨s, hs, i, hi⟩ := hafter' t ht
      refine ⟨s, hs, fun hz => ?_⟩
      have hz' := hz i
      simp at hz'
      exact (not_lt_of_ge hz'.le) hi
  dsimp only
  rw [heq]
  refine ⟨ENNReal.coe_ne_top, ?_, ?_⟩
  · simpa only [ENNReal.toNNReal_coe] using hbefore'
  · simpa only [ENNReal.toNNReal_coe] using hafter'

end Sandpile.External.Stopping
