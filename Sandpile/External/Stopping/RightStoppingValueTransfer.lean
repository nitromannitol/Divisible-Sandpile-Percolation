import Sandpile.External.Stopping.FiniteRightStoppingRewardDensity
import Sandpile.External.Stopping.FiniteNaturalRewardTransfer
import Sandpile.External.Stopping.StoppingValueLowerLimit

/-!
# Right-continuous stopping values under pushforward laws

Finite-rule factorization and right-continuous approximation transfer bounded
natural stopping values from a realization to its pushforward law.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A right-continuous process has at least the stopping value of any
realization obtained by reading it along a measurable map. -/
theorem naturalStoppingValue_le_of_map
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (Z : ℝ≥0 → Ξ → Continuum.Space d) (hZm : ∀ t, StronglyMeasurable (Z t))
    (hZjoint : Measurable (fun p : ℝ≥0 × Ξ => Z p.1 p.2))
    (hZc : ∀ ξ t, ContinuousWithinAt (fun s => Z s ξ) (Set.Ici t) t)
    (f : Ω → Ξ) (hf : Measurable f) (hQ : P.map f = Q)
    (T : ℝ≥0) (G : ℝ≥0 → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ≥0 × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    sSup (naturalStoppingPayoffs P (fun t ω => Z t (f ω)) T G) ≤
      sSup (naturalStoppingPayoffs Q Z T G) := by
  let X : ℝ≥0 → Ω → Continuum.Space d := fun t ω => Z t (f ω)
  have hXm : ∀ t, Measurable (X t) := fun t => (hZm t).measurable.comp hf
  have hXjoint : Measurable (fun p : ℝ≥0 × Ω => X p.1 p.2) :=
    hZjoint.comp (measurable_fst.prodMk (hf.comp measurable_snd))
  have hXc : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t := fun ω t => hZc (f ω) t
  have hne : (naturalStoppingPayoffs P X T G).Nonempty :=
    ⟨_, fun _ => 0, Continuum.isBrownianStopping_const X 0, (fun _ => bot_le), rfl⟩
  have hbd : BddAbove (naturalStoppingPayoffs Q Z T G) := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, rfl⟩
    have hb := norm_integral_le_of_norm_le_const (μ := Q)
      (f := fun ξ => G (τ ξ) (Z (τ ξ) ξ)) (C := M)
      (Filter.Eventually.of_forall fun ξ => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  change sSup (naturalStoppingPayoffs P X T G) ≤ sSup (naturalStoppingPayoffs Q Z T G)
  refine csSup_le hne ?_
  rintro a ⟨τ, hτ, hτT, rfl⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨ρ, hρ, hρT, hρfin, hclose⟩ :=
    exists_finite_natural_stop_reward_close_of_rightContinuous P X hXm hXjoint hXc T τ hτ hτT G hGc M hG ε hε
  obtain ⟨σ, hσ, hσT, _, heq⟩ :=
    exists_finite_natural_reward_factor P Q Z hZm hZjoint f hf hQ T ρ hρ hρT hρfin G hGc.measurable
  have hval : (∫ ξ, G (σ ξ) (Z (σ ξ) ξ) ∂Q) ≤ sSup (naturalStoppingPayoffs Q Z T G) :=
    le_csSup hbd ⟨σ, hσ, hσT, rfl⟩
  have hnear := (abs_lt.mp hclose).1
  change |(∫ ω, G (ρ ω) (Z (ρ ω) (f ω)) ∂P) -
    (∫ ω, G (τ ω) (Z (τ ω) (f ω)) ∂P)| < ε at hclose
  have hnear' := (abs_lt.mp hclose).2
  linarith

end Sandpile.External.Stopping
