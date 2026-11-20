import Sandpile.External.Stopping.StoppingLawTransfer
import Sandpile.External.Stopping.ApproximatedClockValue

/-!
# Optimal stopping values and continuous path laws

Bounded continuous finite-horizon stopping values depend only on the law of a
continuous process. Finite-grid approximation reduces the comparison to the
transfer of finitely valued natural stopping rules.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Equal continuous path laws give ordered bounded continuous stopping values. -/
theorem brownianDiscount_le_of_path_law_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → Continuum.Space d) (C : ℝ≥0 → Ω' → Continuum.Space d)
    (hBm : ∀ t, StronglyMeasurable (B t)) (hCm : ∀ t, StronglyMeasurable (C t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (hCc : ∀ ω, Continuous fun t => C t ω)
    (hlaw : P.map (LatticeProb.pathMap B hBc) = Q.map (LatticeProb.pathMap C hCc))
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Continuum.brownianDiscount B P (fun s z => -G s z) T ≤
      Continuum.brownianDiscount C Q (fun s z => -G s z) T := by
  let S : Set ℝ := {a | ∃ τ : Ω → ℝ≥0, Continuum.IsBrownianStopping B τ ∧
    (∀ ω, τ ω ≤ T) ∧ a = ∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P}
  let U : Set ℝ := {a | ∃ τ : Ω' → ℝ≥0, Continuum.IsBrownianStopping C τ ∧
    (∀ ω, τ ω ≤ T) ∧ a = ∫ ω, G ((T : ℝ) - τ ω) (C (τ ω) ω) ∂Q}
  have hSne : S.Nonempty := ⟨_, fun _ => 0, Continuum.isBrownianStopping_const B 0,
    (fun _ => bot_le), rfl⟩
  have hUbd : BddAbove U := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, rfl⟩
    have hb := norm_integral_le_of_norm_le_const (μ := Q)
      (f := fun ω => G ((T : ℝ) - τ ω) (C (τ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  have heq₁ : Continuum.brownianDiscount B P (fun s z => -G s z) T = sSup S := by
    unfold Continuum.brownianDiscount
    apply congrArg sSup
    ext a
    simp only [S, Set.mem_ofPred_eq, neg_neg, NNReal.coe_le_coe]
  have heq₂ : Continuum.brownianDiscount C Q (fun s z => -G s z) T = sSup U := by
    unfold Continuum.brownianDiscount
    apply congrArg sSup
    ext a
    simp only [U, Set.mem_ofPred_eq, neg_neg, NNReal.coe_le_coe]
  rw [heq₁, heq₂]
  refine csSup_le hSne ?_
  rintro a ⟨τ, hτ, hτT, rfl⟩
  let σ : ℕ → Ω → ℝ≥0 := fun n ω => min (LatticeProb.dyUp n (τ ω)) T
  have hσT : ∀ n ω, σ n ω ≤ T := fun _ _ => min_le_right _ _
  have hσstop : ∀ n, Continuum.IsBrownianStopping B (σ n) := by
    intro n
    have hs := (LatticeProb.isStoppingTime_dyUp hτ n).min_const T
    have heq : (fun ω => (σ n ω : ℝ≥0∞)) =
        (fun ω => min (LatticeProb.dyUp n (τ ω) : ℝ≥0∞) T) := by
      funext ω
      exact ENNReal.coe_min _ _
    change IsStoppingTime (Continuum.brownianFiltration B) (fun ω => (σ n ω : ℝ≥0∞))
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
  have hσlim : ∀ᵐ ω ∂P, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω)) := by
    filter_upwards with ω
    simpa only [σ, min_eq_left (hτT ω)] using
      (LatticeProb.tendsto_dyUp (τ ω)).min (tendsto_const_nhds (x := T))
  have hlim := tendsto_integral_reward_of_ae_tendsto P B
    (fun t => (hBm t).measurable.aemeasurable)
    (Filter.Eventually.of_forall hBc) σ τ
    (fun n => Continuum.IsBrownianStopping.aemeasurable (hσstop n) P
      (fun t => (hBm t).measurable.aemeasurable)) hσlim T M G hGc hG
  apply le_of_tendsto hlim
  filter_upwards with n
  obtain ⟨υ, hυ, hυT, _, hrew⟩ :=
    exists_finite_stopping_reward_eq_of_path_law_eq P Q B C hBm hCm hBc hCc hlaw T
      (σ n) (hσstop n) (hσT n) (hσfin n) G hGc.measurable
  rw [hrew]
  exact le_csSup hUbd ⟨υ, hυ, hυT, rfl⟩

/-- Equal continuous path laws give the same bounded continuous stopping value. -/
theorem brownianDiscount_eq_of_path_law_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → Continuum.Space d) (C : ℝ≥0 → Ω' → Continuum.Space d)
    (hBm : ∀ t, StronglyMeasurable (B t)) (hCm : ∀ t, StronglyMeasurable (C t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (hCc : ∀ ω, Continuous fun t => C t ω)
    (hlaw : P.map (LatticeProb.pathMap B hBc) = Q.map (LatticeProb.pathMap C hCc))
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Continuum.brownianDiscount B P (fun s z => -G s z) T =
      Continuum.brownianDiscount C Q (fun s z => -G s z) T :=
  le_antisymm (brownianDiscount_le_of_path_law_eq P Q B C hBm hCm hBc hCc hlaw T G hGc M hG)
    (brownianDiscount_le_of_path_law_eq Q P C B hCm hBm hCc hBc hlaw.symm T G hGc M hG)

end Sandpile.External.Stopping
