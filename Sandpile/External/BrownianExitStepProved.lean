import Sandpile.External.BrownianExitStep
import Sandpile.Frozen.BrownianBallLocalization
import LatticeProb.Prob.BrownianRestartBoundLimit

/-!
# The strong Markov step at a ball's exit time, proved

This module discharges the external input `Sandpile.External.BrownianExitStep`, the strong
Markov property of Brownian motion at the exit time of a Euclidean ball in the set-integral
form of `lem:brownian-ball-localization`, instead of assuming it.

The shared library proves the restart bound `LatticeProb.BrownianRestartBound.restartBound_holds`:
if, started afresh at any point of a set `Z`, the payoff drops in expectation by at most `S`
along every stopping time bounded by the remaining horizon, then on an event `E` of the past at
a stopping time `σ` on which `σ ≤ τ` and `B_σ ∈ Z`, the payoff drops from `σ` to `τ` by at most
`P(E) S` in integral. It is applied with `σ` the exit time of the ball of radius `A` about `u`
stopped at the horizon, `E = {σ < τ}`, which lies in the σ-algebra of the past at `σ`, `Z` the
closed `A`-neighbourhood of `K` and `S` the supremum of the values over `Z` and all horizons
in `[0, T]`. On `E` the time `min τ σ` is `σ`, and `B_σ` lies within `A` of `u` by continuity
of the paths. The integrable envelope bounds every payoff of a stopping time by `M` and every
value by `2M`, so `S` is a genuine supremum and bounds each drop.

The `Prop` and its name are left untouched, so no frozen statement changes.
`Sandpile.brownian_ball_localization` is `lem:brownian-ball-localization` without the
hypothesis.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.External

open Sandpile.Continuum

/-- A motion started at `u` with continuous paths is within `A ≥ 0` of `u` at the exit time of
the closed ball of radius `A` about `u`, stopped at any horizon. -/
theorem norm_sub_le_of_ballExitTime {Ω : Type*} {d : ℕ} {B : ℝ≥0 → Ω → Space d}
    (hc : ∀ ω, Continuous fun s => B s ω) (u : Space d) {A : ℝ} (hA : 0 ≤ A) (T : ℝ)
    {ω : Ω} (h0 : B 0 ω = u) :
    ‖B (ballExitTime B u A T ω) ω - u‖ ≤ A := by
  set σ := ballExitTime B u A T ω with hσ
  have hlt : ∀ s : ℝ≥0, s < σ → ‖B s ω - u‖ ≤ A := by
    intro s hs
    have hle : ((σ : ℝ≥0) : ℝ≥0∞) ≤ LatticeProb.exitTime B u A ω := by
      rw [hσ, ballExitTime, LatticeProb.coe_exitTimeTrunc]
      exact inf_le_left
    have hnot : ¬ LatticeProb.exitTime B u A ω ≤ (s : ℝ≥0∞) :=
      not_le.2 (lt_of_lt_of_le (by exact_mod_cast hs) hle)
    rw [LatticeProb.exitTime_le_iff hc u A ω s] at hnot
    push Not at hnot
    exact (hnot s le_rfl).le
  have hclosed : IsClosed {s : ℝ≥0 | ‖B s ω - u‖ ≤ A} :=
    isClosed_le ((hc ω).sub continuous_const).norm continuous_const
  rcases eq_or_ne σ 0 with h | h
  · rw [h, h0, sub_self, norm_zero]
    exact hA
  · have hne : (Set.Iio σ).Nonempty := ⟨0, pos_iff_ne_zero.2 h⟩
    have hsub : closure (Set.Iio σ) ⊆ {s : ℝ≥0 | ‖B s ω - u‖ ≤ A} :=
      hclosed.closure_subset_iff.2 hlt
    rw [closure_Iio' hne] at hsub
    exact hsub (Set.mem_Iic.2 le_rfl)

end Sandpile.External

open Sandpile.Continuum

-- FROZEN-STATEMENT-BEGIN
/-- The strong Markov step at the exit time of the ball, in the set-integral form of
`lem:brownian-ball-localization`, proved rather than assumed. -/
theorem Sandpile.External.brownianExitStep_holds : Sandpile.External.BrownianExitStep
-- FROZEN-STATEMENT-END
:= by
  intro d ΩB _ PB _ B hB hc hm T hT h hh A hA K _hK hEnv u hu τ hτ hτT
  obtain ⟨M, hM⟩ := hEnv
  set Z : Set (Space d) := {z | ∃ y ∈ K, ‖z - y‖ ≤ A} with hZ
  set V : Set ℝ := {v : ℝ | ∃ z : Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) ∧
    ∃ s ∈ Set.Icc (0 : ℝ) T, v = brownianValue (B z) PB h s z} with hV
  have hpay : ∀ z ∈ Z, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ρ : ΩB → ℝ≥0, (∀ ω, (ρ ω : ℝ) ≤ s) →
      |∫ ω, -h (s - ρ ω) (B z (ρ ω) ω) ∂PB| ≤ M := by
    intro z hz s hs ρ hρ
    obtain ⟨D, hD, hDM, hdom⟩ := hM z hz
    have hbd : ∀ᵐ ω ∂PB, ‖-h (s - ρ ω) (B z (ρ ω) ω)‖ ≤ D ω := by
      filter_upwards [hdom] with ω hω
      rw [norm_neg]
      exact hω _ ⟨sub_nonneg.2 (hρ ω), (sub_le_self _ (NNReal.coe_nonneg _)).trans hs.2⟩ _
        ((hρ ω).trans hs.2)
    rw [← Real.norm_eq_abs]
    exact (norm_integral_le_of_norm_le hD hbd).trans hDM
  have hval : ∀ z ∈ Z, ∀ s ∈ Set.Icc (0 : ℝ) T, |h s z| ≤ M := by
    intro z hz s hs
    obtain ⟨D, hD, hDM, hdom⟩ := hM z hz
    have hbd : ∀ᵐ ω ∂PB, ‖h s z‖ ≤ D ω := by
      filter_upwards [hdom, (hB z).start] with ω hω h0
      have := hω s hs 0 (by simpa using hT.le)
      rwa [h0] at this
    have hle : ‖h s z‖ ≤ ∫ ω, D ω ∂PB := by
      simpa using integral_mono_ae (integrable_const ‖h s z‖) hD hbd
    rw [← Real.norm_eq_abs]
    exact hle.trans hDM
  have hdisc_bdd : ∀ z ∈ Z, ∀ s ∈ Set.Icc (0 : ℝ) T,
      BddAbove {a : ℝ | ∃ ρ : ΩB → ℝ≥0, IsBrownianStopping (B z) ρ ∧ (∀ ω, (ρ ω : ℝ) ≤ s) ∧
        a = ∫ ω, -h (s - ρ ω) (B z (ρ ω) ω) ∂PB} := by
    intro z hz s hs
    refine ⟨M, ?_⟩
    rintro a ⟨ρ, -, hρ, rfl⟩
    exact (le_abs_self _).trans (hpay z hz s hs ρ hρ)
  have hdisc : ∀ z ∈ Z, ∀ s ∈ Set.Icc (0 : ℝ) T, brownianDiscount (B z) PB h s ≤ M := by
    intro z hz s hs
    rw [brownianDiscount]
    refine Real.sSup_le ?_ ((abs_nonneg _).trans (hval z hz s hs))
    rintro a ⟨ρ, -, hρ, rfl⟩
    exact (le_abs_self _).trans (hpay z hz s hs ρ hρ)
  have hVbdd : BddAbove V := by
    refine ⟨M + M, ?_⟩
    rintro v ⟨z, hz, s, hs, rfl⟩
    exact add_le_add ((le_abs_self _).trans (hval z hz s hs)) (hdisc z hz s hs)
  have hS : ∀ z ∈ Z, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ρ : ΩB → ℝ≥0,
      IsStoppingTime (LatticeProb.natFiltration (B z) (hm z)) (fun ω => (ρ ω : ℝ≥0∞)) →
      (∀ ω, (ρ ω : ℝ) ≤ s) → Integrable (fun ω => h (s - ρ ω) (B z (ρ ω) ω)) PB →
      h s z - ∫ ω, h (s - ρ ω) (B z (ρ ω) ω) ∂PB ≤ sSup V := by
    intro z hz s hs ρ hρ hρs _
    have hmem : (∫ ω, -h (s - ρ ω) (B z (ρ ω) ω) ∂PB) ∈
        {a : ℝ | ∃ ρ : ΩB → ℝ≥0, IsBrownianStopping (B z) ρ ∧ (∀ ω, (ρ ω : ℝ) ≤ s) ∧
          a = ∫ ω, -h (s - ρ ω) (B z (ρ ω) ω) ∂PB} :=
      ⟨ρ, (isBrownianStopping_iff_natFiltration (B z) (hm z) ρ).2 hρ, hρs, rfl⟩
    have h1 : h s z - ∫ ω, h (s - ρ ω) (B z (ρ ω) ω) ∂PB ≤ brownianValue (B z) PB h s z := by
      rw [brownianValue, brownianDiscount, sub_eq_add_neg, ← integral_neg]
      exact add_le_add le_rfl (le_csSup (hdisc_bdd z hz s hs) hmem)
    exact h1.trans (le_csSup hVbdd ⟨z, hz, s, hs, rfl⟩)
  set σ : ΩB → ℝ≥0 := ballExitTime (B u) u A T with hσdef
  have hσ : IsStoppingTime (LatticeProb.natFiltration (B u) (hm u))
      (fun ω => (σ ω : ℝ≥0∞)) :=
    LatticeProb.isStoppingTime_exitTimeTrunc (hm u) (hc u) u A T.toNNReal
  have hτ' : IsStoppingTime (LatticeProb.natFiltration (B u) (hm u))
      (fun ω => (τ ω : ℝ≥0∞)) :=
    (isBrownianStopping_iff_natFiltration (B u) (hm u) τ).1 hτ
  set E : Set ΩB := {b : ΩB | σ b < τ b} with hEdef
  have hE : MeasurableSet[hσ.measurableSpace] E := by
    have hc' := (IsStoppingTime.measurableSet_stopping_time_le hτ' hσ).compl
    convert hc' using 1
    ext b
    change σ b < τ b ↔ ¬((τ b : ℝ≥0∞) ≤ (σ b : ℝ≥0∞))
    rw [ENNReal.coe_le_coe, not_le]
  have hEm : MeasurableSet E := hσ.measurableSpace_le _ hE
  obtain ⟨D, hD, -, hdom⟩ := hM u ⟨u, hu, by simpa using (zero_le_one.trans hA)⟩
  have hZσ : ∀ᵐ ω ∂PB, ω ∈ E → B u (σ ω) ω ∈ Z := by
    filter_upwards [(hB u).start] with ω h0 _
    exact ⟨u, hu,
      Sandpile.External.norm_sub_le_of_ballExitTime (hc u) u (zero_le_one.trans hA) T h0⟩
  have key := LatticeProb.BrownianRestartBound.restartBound_holds PB B
    (fun z => ⟨(hB z).start, (hB z).coord, (hB z).indep⟩) hm hc T hT.le h hh Z (sSup V) hS u
    D hD hdom σ τ hσ hτ' hτT E hE (fun ω hω => le_of_lt hω) hZσ
  refine (setIntegral_congr_fun hEm fun b hb => ?_).trans_le key
  simp only [min_eq_right (le_of_lt (show σ b < τ b from hb))]

/-- `lem:brownian-ball-localization` without the hypothesis `Sandpile.External.BrownianExitStep`,
which `Sandpile.External.brownianExitStep_holds` proves. -/
theorem Sandpile.brownian_ball_localization
    (d : ℕ) (hd : d < 4) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 0 < T →
      ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Sandpile.Continuum.Space d), IsCompact K →
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W PW →
      ∀ ν2 : ℝ, 0 ≤ ν2 →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
        (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB) →
        (∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun s => B y s ω) →
        (∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
      ∀ (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ),
        (∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
          Z t x =ᵐ[PW] fun ω => Sandpile.Continuum.gaussianPotential d ν2 W t x ω) →
        (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
          ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
            (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)))) →
      ∀ᵐ ω ∂PW, ∀ u ∈ K,
        Sandpile.Continuum.brownianValue (B u) PB
              (fun t z => Z t z ω) T u -
            Sandpile.Continuum.brownianValueBall (B u) PB
              (fun t z => Z t z ω) T A u ≤
          C * Real.exp (-(c * A ^ 2 / T)) *
            sSup {v : ℝ | ∃ z : Sandpile.Continuum.Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) ∧
              v = Sandpile.Continuum.brownianValue (B z) PB
                (fun t x => Z t x ω) T z} :=
  Sandpile.Frozen.brownian_ball_localization Sandpile.External.brownianExitStep_holds d hd
