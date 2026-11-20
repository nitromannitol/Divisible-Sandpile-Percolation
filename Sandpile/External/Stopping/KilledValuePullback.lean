import Sandpile.External.Stopping.RightKilledValueTransfer

/-!
# Pullback of killed stopping values

A stopping rule and its killing constraint pull back along a measurable map.
For right-continuous processes this gives equality of killed values under
pushforward laws.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Pulling back stopping rules cannot decrease a killed stopping value. -/
theorem clockStoppingValue_ge_of_map
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (Z : ℝ≥0 → Ξ → Continuum.Space d) (hZm : ∀ t, Measurable (Z t))
    (hZjoint : Measurable (fun p : ℝ≥0 × Ξ => Z p.1 p.2))
    (f : Ω → Ξ) (hf : Measurable f) (hQ : P.map f = Q)
    (T : ℝ≥0) (κ : Ξ → ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGm : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    sSup (clockPayoffs Z Q T G κ (Continuum.brownianFiltration Z)) ≤
    sSup (clockPayoffs (fun t ω => Z t (f ω)) P T G (fun ω => κ (f ω))
      (Continuum.brownianFiltration (fun t ω => Z t (f ω)))) := by
  let X : ℝ≥0 → Ω → Continuum.Space d := fun t ω => Z t (f ω)
  have hne : (clockPayoffs Z Q T G κ (Continuum.brownianFiltration Z)).Nonempty :=
    ⟨_, fun _ => 0, Continuum.isBrownianStopping_const Z 0, (fun _ => bot_le),
      Filter.Eventually.of_forall (fun _ => bot_le), rfl⟩
  have hbd : BddAbove (clockPayoffs X P T G (fun ω => κ (f ω)) (Continuum.brownianFiltration X)) := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, _, rfl⟩
    have hb := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G ((T : ℝ) - τ ω) (X (τ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  change sSup (clockPayoffs Z Q T G κ (Continuum.brownianFiltration Z)) ≤
    sSup (clockPayoffs X P T G (fun ω => κ (f ω)) (Continuum.brownianFiltration X))
  refine csSup_le hne ?_
  rintro a ⟨τ, hτ, hτT, hτκ, rfl⟩
  have hτm : Measurable τ := measurable_of_isBrownianStopping Z hZm τ hτ
  have hpos : Measurable (fun ξ => Z (τ ξ) ξ) := hZjoint.comp (hτm.prodMk measurable_id)
  have hreward : Measurable (fun ξ => G ((T : ℝ) - τ ξ) (Z (τ ξ) ξ)) :=
    hGm.comp ((measurable_const.sub (measurable_coe_nnreal_real.comp hτm)).prodMk hpos)
  have hkill : ∀ᵐ ω ∂P, τ (f ω) ≤ κ (f ω) := by
    have hk : ∀ᵐ ξ ∂P.map f, τ ξ ≤ κ ξ := by
      rw [hQ]
      exact hτκ
    exact ae_of_ae_map hf.aemeasurable hk
  have heq : (∫ ξ, G ((T : ℝ) - τ ξ) (Z (τ ξ) ξ) ∂Q) =
      ∫ ω, G ((T : ℝ) - τ (f ω)) (Z (τ (f ω)) (f ω)) ∂P := by
    rw [← hQ, MeasureTheory.integral_map hf.aemeasurable hreward.aestronglyMeasurable]
  rw [heq]
  exact le_csSup hbd ⟨(fun ω => τ (f ω)), isBrownianStopping_comp Z f τ hτ,
    (fun ω => hτT (f ω)), hkill, rfl⟩

/-- Bounded continuous killed values are preserved under measurable maps for
right-continuous processes and natural stopping clocks. -/
theorem clockStoppingValue_eq_of_map
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ξ) [IsProbabilityMeasure Q]
    (Z : ℝ≥0 → Ξ → Continuum.Space d) (hZm : ∀ t, StronglyMeasurable (Z t))
    (hZjoint : Measurable (fun p : ℝ≥0 × Ξ => Z p.1 p.2))
    (hZc : ∀ ξ t, ContinuousWithinAt (fun s => Z s ξ) (Set.Ici t) t)
    (f : Ω → Ξ) (hf : Measurable f) (hQ : P.map f = Q)
    (T : ℝ≥0) (κ : Ξ → ℝ≥0) (hκ : Continuum.IsBrownianStopping Z κ)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    sSup (clockPayoffs (fun t ω => Z t (f ω)) P T G (fun ω => κ (f ω))
      (Continuum.brownianFiltration (fun t ω => Z t (f ω)))) =
    sSup (clockPayoffs Z Q T G κ (Continuum.brownianFiltration Z)) :=
  le_antisymm (clockStoppingValue_le_of_map P Q Z hZm hZjoint hZc f hf hQ T κ hκ G hGc M hG)
    (clockStoppingValue_ge_of_map P Q Z (fun t => (hZm t).measurable) hZjoint f hf hQ T κ G hGc.measurable M hG)

end Sandpile.External.Stopping
