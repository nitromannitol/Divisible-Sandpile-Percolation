import Sandpile.External.Stopping.CubeStoppingLawTransfer
import Sandpile.External.Stopping.BrownianValueIntrinsic

/-!
# Cube-killed Brownian stopping values and path laws

Dyadic approximation followed by clipping at the cube exit transfers
finite-horizon killed values between continuous Brownian realizations.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Equal continuous path laws order cube-killed bounded continuous stopping
values. -/
theorem brownianDiscountCube_le_of_path_law_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (C : ℝ≥0 → Ω' → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hC : Continuum.IsBrownian d x C Q)
    (hBm : ∀ t, Measurable (B t)) (hCm : ∀ t, Measurable (C t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (hCc : ∀ ω, Continuous fun t => C t ω)
    (hlaw : P.map (LatticeProb.pathMap B hBc) = Q.map (LatticeProb.pathMap C hCc))
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x ≤
      Continuum.brownianDiscountCube C Q (fun s z => -G s z) T 1 x := by
  let κ : Ω → ℝ≥0 := fun ω =>
    (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal
  let κC : Ω' → ℝ≥0 := fun ω =>
    (min (LatticeProb.openExitTime C (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal
  have hκ : Continuum.IsBrownianStopping B κ := isBrownianStopping_openUnitCubeExitTrunc B hBc x T
  let S := clockPayoffs B P T G κ (Continuum.brownianFiltration B)
  let U := clockPayoffs C Q T G κC (Continuum.brownianFiltration C)
  have hSne : S.Nonempty := ⟨_, fun _ => 0, Continuum.isBrownianStopping_const B 0,
    (fun _ => bot_le), Filter.Eventually.of_forall (fun _ => bot_le), rfl⟩
  have hUbd : BddAbove U := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, _, rfl⟩
    have hb := norm_integral_le_of_norm_le_const (μ := Q)
      (f := fun ω => G ((T : ℝ) - τ ω) (C (τ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  have heq₁ : Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x = sSup S := by
    unfold Continuum.brownianDiscountCube
    rw [cubeStoppingPayoffs_eq_clockPayoffs P x B hB hBm hBc T G]
    rfl
  have heq₂ : Continuum.brownianDiscountCube C Q (fun s z => -G s z) T 1 x = sSup U := by
    unfold Continuum.brownianDiscountCube
    rw [cubeStoppingPayoffs_eq_clockPayoffs Q x C hC hCm hCc T G]
    rfl
  rw [heq₁, heq₂]
  refine csSup_le hSne ?_
  rintro a ⟨τ, hτ, hτT, hτκ, rfl⟩
  let σ : ℕ → Ω → ℝ≥0 := fun n ω => min (LatticeProb.dyUp n (τ ω)) T
  let ν : ℕ → Ω → ℝ≥0 := fun n ω => min (σ n ω) (κ ω)
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
  have hνstop : ∀ n, Continuum.IsBrownianStopping B (ν n) := by
    intro n
    change IsStoppingTime (Continuum.brownianFiltration B) (fun ω => (ν n ω : ℝ≥0∞))
    have heq : (fun ω => (ν n ω : ℝ≥0∞)) =
        (fun ω => min (σ n ω : ℝ≥0∞) (κ ω : ℝ≥0∞)) := by
      funext ω
      exact ENNReal.coe_min _ _
    rw [heq]
    exact (hσstop n).min hκ
  have hνlim : ∀ᵐ ω ∂P, Tendsto (fun n => ν n ω) atTop (𝓝 (τ ω)) := by
    filter_upwards [hτκ] with ω hle
    have hs : Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω)) := by
      simpa only [σ, min_eq_left (hτT ω)] using
        (LatticeProb.tendsto_dyUp (τ ω)).min (tendsto_const_nhds (x := T))
    simpa only [ν, min_eq_left hle] using hs.min (tendsto_const_nhds (x := κ ω))
  have hlim := tendsto_integral_reward_of_ae_tendsto P B
    (fun t => (hBm t).aemeasurable) (Filter.Eventually.of_forall hBc) ν τ
    (fun n => Continuum.IsBrownianStopping.aemeasurable (hνstop n) P
      (fun t => (hBm t).aemeasurable)) hνlim T M G hGc hG
  apply le_of_tendsto hlim
  filter_upwards with n
  obtain ⟨υ, hυ, hυT, hυκC, hrew⟩ :=
    exists_cube_clipped_finite_stopping_reward_eq P Q B C
      (fun t => (hBm t).stronglyMeasurable) (fun t => (hCm t).stronglyMeasurable)
      hBc hCc hlaw x T (σ n) (hσstop n) (hσT n) (hσfin n) G hGc.measurable
  change (∫ ω, G ((T : ℝ) - min (σ n ω) (κ ω))
      (B (min (σ n ω) (κ ω)) ω) ∂P) = _ at hrew
  rw [hrew]
  exact le_csSup hUbd ⟨υ, hυ, hυT, Filter.Eventually.of_forall hυκC, rfl⟩

/-- Cube-killed bounded continuous stopping values agree for continuous
Brownian motions with equal path laws. -/
theorem brownianDiscountCube_eq_of_path_law_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (C : ℝ≥0 → Ω' → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hC : Continuum.IsBrownian d x C Q)
    (hBm : ∀ t, Measurable (B t)) (hCm : ∀ t, Measurable (C t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (hCc : ∀ ω, Continuous fun t => C t ω)
    (hlaw : P.map (LatticeProb.pathMap B hBc) = Q.map (LatticeProb.pathMap C hCc))
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x =
      Continuum.brownianDiscountCube C Q (fun s z => -G s z) T 1 x :=
  le_antisymm (brownianDiscountCube_le_of_path_law_eq P Q x B C hB hC hBm hCm hBc hCc hlaw T G hGc M hG)
    (brownianDiscountCube_le_of_path_law_eq Q P x C B hC hB hCm hBm hCc hBc hlaw.symm T G hGc M hG)

/-- The cube-killed bounded continuous value is independent of the continuous
Brownian realization. -/
theorem brownianDiscountCube_eq_of_continuous_isBrownian
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (C : ℝ≥0 → Ω' → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hC : Continuum.IsBrownian d x C Q)
    (hBm : ∀ t, Measurable (B t)) (hCm : ∀ t, Measurable (C t))
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (hCc : ∀ ω, Continuous fun t => C t ω)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x =
      Continuum.brownianDiscountCube C Q (fun s z => -G s z) T 1 x :=
  brownianDiscountCube_eq_of_path_law_eq P Q x B C hB hC hBm hCm hBc hCc
    (map_pathMap_eq_of_sandpile_brownian P Q x B C hB hC hBm hCm hBc hCc) T G hGc M hG

end Sandpile.External.Stopping
