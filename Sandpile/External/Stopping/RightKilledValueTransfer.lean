import Sandpile.External.Stopping.FiniteRightStoppingRewardDensity
import Sandpile.External.Stopping.NaturalStoppingComposition
import Sandpile.External.Stopping.FiniteNaturalStopTransfer

/-!
# Killed stopping values under pushforward laws

Finite-rule factorization and right-continuous approximation transfer bounded
killed stopping values from a realization to its pushforward law.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A right-continuous process has at least the killed stopping value of any
realization obtained by reading it along a measurable map, when the killing
clock is a natural stopping time. -/
theorem clockStoppingValue_le_of_map
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
      (Continuum.brownianFiltration (fun t ω => Z t (f ω)))) ≤
    sSup (clockPayoffs Z Q T G κ (Continuum.brownianFiltration Z)) := by
  let X : ℝ≥0 → Ω → Continuum.Space d := fun t ω => Z t (f ω)
  have hXm : ∀ t, Measurable (X t) := fun t => (hZm t).measurable.comp hf
  have hXjoint : Measurable (fun p : ℝ≥0 × Ω => X p.1 p.2) :=
    hZjoint.comp (measurable_fst.prodMk (hf.comp measurable_snd))
  have hne : (clockPayoffs X P T G (fun ω => κ (f ω)) (Continuum.brownianFiltration X)).Nonempty :=
    ⟨_, fun _ => 0, Continuum.isBrownianStopping_const X 0, (fun _ => bot_le),
      Filter.Eventually.of_forall (fun _ => bot_le), rfl⟩
  have hbd : BddAbove (clockPayoffs Z Q T G κ (Continuum.brownianFiltration Z)) := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, _, rfl⟩
    have hb := norm_integral_le_of_norm_le_const (μ := Q)
      (f := fun ξ => G ((T : ℝ) - τ ξ) (Z (τ ξ) ξ)) (C := M)
      (Filter.Eventually.of_forall fun ξ => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  change sSup (clockPayoffs X P T G (fun ω => κ (f ω)) (Continuum.brownianFiltration X)) ≤ _
  refine csSup_le hne ?_
  rintro a ⟨τ, hτ, hτT, hτκ, rfl⟩
  let σ : ℕ → Ω → ℝ≥0 := fun n ω => min (LatticeProb.dyUp n (τ ω)) T
  have hσT : ∀ n ω, σ n ω ≤ T := fun _ _ => min_le_right _ _
  have hσstop : ∀ n, Continuum.IsBrownianStopping X (σ n) := by
    intro n
    have hs := (LatticeProb.isStoppingTime_dyUp hτ n).min_const T
    have heq : (fun ω => (σ n ω : ℝ≥0∞)) =
        (fun ω => min (LatticeProb.dyUp n (τ ω) : ℝ≥0∞) T) := by
      funext ω
      exact ENNReal.coe_min _ _
    change IsStoppingTime (Continuum.brownianFiltration X) (fun ω => (σ n ω : ℝ≥0∞))
    rw [heq]
    exact hs
  have hσfin : ∀ n, (Set.range (σ n)).Finite := by
    intro n
    let K := Nat.ceil ((2 ^ n : ℝ≥0) * T)
    refine ((Set.finite_Iic K).image (fun j : ℕ => min ((j : ℝ≥0) / 2 ^ n) T)).subset ?_
    rintro _ ⟨ω, rfl⟩
    refine ⟨Nat.ceil ((2 ^ n : ℝ≥0) * τ ω), ?_, ?_⟩
    · exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (hτT ω) zero_le)
    · rfl
  have hσlim : ∀ ω, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω)) := by
    intro ω
    simpa only [σ, min_eq_left (hτT ω)] using
      (LatticeProb.tendsto_dyUp (τ ω)).min (tendsto_const_nhds (x := T))
  let ρ : ℕ → Ω → ℝ≥0 := fun n ω => min (σ n ω) (κ (f ω))
  have hκX : Continuum.IsBrownianStopping X (fun ω => κ (f ω)) :=
    isBrownianStopping_comp Z f κ hκ
  have hρstop : ∀ n, Continuum.IsBrownianStopping X (ρ n) := fun n =>
    Continuum.isBrownianStopping_min (hσstop n) hκX
  have hlim : Tendsto (fun n => ∫ ω, G ((T : ℝ) - ρ n ω) (X (ρ n ω) ω) ∂P) atTop
      (𝓝 (∫ ω, G ((T : ℝ) - τ ω) (X (τ ω) ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun n => ?_)
      (integrable_const M) (fun n => ?_) ?_
    · have hρm : AEMeasurable (ρ n) P :=
        (measurable_of_isBrownianStopping X hXm (ρ n) (hρstop n)).aemeasurable
      have hp : AEMeasurable (fun ω => X (ρ n ω) ω) P :=
        hXjoint.comp_aemeasurable (hρm.prodMk aemeasurable_id)
      exact (hGc.measurable.comp_aemeasurable
        ((aemeasurable_const.sub (measurable_coe_nnreal_real.comp_aemeasurable hρm)).prodMk hp)).aestronglyMeasurable
    · filter_upwards with ω
      simpa only [Real.norm_eq_abs] using hG _ _
    · filter_upwards [hτκ] with ω hω
      have hρlim : Tendsto (fun n => ρ n ω) atTop (𝓝 (τ ω)) := by
        simpa only [ρ, min_eq_left hω] using (hσlim ω).min (tendsto_const_nhds (x := κ (f ω)))
      have hwithin : Tendsto (fun n => ρ n ω) atTop (𝓝[Set.Ici (τ ω)] (τ ω)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hρlim, Filter.Eventually.of_forall fun n =>
          le_min (le_min (LatticeProb.le_dyUp n _) (hτT ω)) hω⟩
      have hr : Tendsto (fun t => Z t (f ω)) (𝓝[Set.Ici (τ ω)] (τ ω))
          (𝓝 (Z (τ ω) (f ω))) := hZc (f ω) (τ ω)
      have hright := hr.comp hwithin
      have htime : Tendsto (fun n => (T : ℝ) - (ρ n ω : ℝ)) atTop
          (𝓝 ((T : ℝ) - (τ ω : ℝ))) :=
        tendsto_const_nhds.sub ((NNReal.continuous_coe.tendsto _).comp hρlim)
      exact (hGc.tendsto _).comp (htime.prodMk_nhds hright)
  apply le_of_tendsto hlim
  filter_upwards with n
  obtain ⟨υ, hυ, hυT, _, hσυ⟩ :=
    exists_finite_natural_stopping_factor Z hZm f hf T (σ n) (hσstop n) (hσT n) (hσfin n)
  let η : Ξ → ℝ≥0 := fun ξ => min (υ ξ) (κ ξ)
  have hη : Continuum.IsBrownianStopping Z η := Continuum.isBrownianStopping_min hυ hκ
  have hηm : Measurable η := measurable_of_isBrownianStopping Z (fun t => (hZm t).measurable) η hη
  have hpos : Measurable (fun ξ => Z (η ξ) ξ) := hZjoint.comp (hηm.prodMk measurable_id)
  have hreward : Measurable (fun ξ => G ((T : ℝ) - η ξ) (Z (η ξ) ξ)) :=
    hGc.measurable.comp ((measurable_const.sub (measurable_coe_nnreal_real.comp hηm)).prodMk hpos)
  have heq : (fun ω => G ((T : ℝ) - ρ n ω) (X (ρ n ω) ω)) =
      (fun ω => G ((T : ℝ) - η (f ω)) (Z (η (f ω)) (f ω))) := by
    funext ω
    dsimp only [ρ, η, X]
    rw [hσυ ω]
  rw [heq, ← MeasureTheory.integral_map hf.aemeasurable hreward.aestronglyMeasurable, hQ]
  exact le_csSup hbd ⟨η, hη, (fun ξ => (min_le_left _ _).trans (hυT ξ)),
    Filter.Eventually.of_forall (fun ξ => min_le_right _ _), rfl⟩

end Sandpile.External.Stopping
