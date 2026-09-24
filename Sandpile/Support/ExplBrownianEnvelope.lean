import Sandpile.Support.ExplBrownianSemigroup
import Sandpile.Support.ExplHorizon
import Sandpile.Support.StopMeasurable
import Sandpile.Support.ExplGreenFubini
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace Sandpile.Support
open Sandpile.Continuum

/-- Maximum displacement from the initial point on a compact time interval. -/
noncomputable def brownianPathRadius {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (x : Space d) (T : ℝ≥0) (ω : Ω) : ℝ :=
  sSup ((fun s : ℝ≥0 => ‖B s ω - x‖) '' Set.Icc 0 T)


theorem lt_pathRadius {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (hBc : ∀ ω, Continuous fun s => B s ω)
    (x : Space d) (T : ℝ≥0) (ω : Ω) (a : ℝ) :
    a < brownianPathRadius B x T ω ↔ ∃ s : ℝ≥0, s ≤ T ∧ a < ‖B s ω - x‖ := by
  have hc : Continuous (fun s : ℝ≥0 => ‖B s ω - x‖) := ((hBc ω).sub continuous_const).norm
  have hb : BddAbove ((fun s : ℝ≥0 => ‖B s ω - x‖) '' Set.Icc 0 T) :=
    (isCompact_Icc.image hc).bddAbove
  have hn : ((fun s : ℝ≥0 => ‖B s ω - x‖) '' Set.Icc 0 T).Nonempty :=
    ⟨_, ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩⟩
  rw [brownianPathRadius, lt_csSup_iff hb hn]
  constructor
  · rintro ⟨b, ⟨s, hs, rfl⟩, ha⟩
    exact ⟨s, hs.2, ha⟩
  · rintro ⟨s, hs, ha⟩
    exact ⟨_, ⟨s, ⟨zero_le, hs⟩, rfl⟩, ha⟩
theorem norm_le_pathRadius {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (hBc : ∀ ω, Continuous fun s => B s ω)
    (x : Space d) (T : ℝ≥0) (ω : Ω) {s : ℝ≥0} (hs : s ≤ T) :
    ‖B s ω - x‖ ≤ brownianPathRadius B x T ω := by
  have hc : Continuous (fun s : ℝ≥0 => ‖B s ω - x‖) := ((hBc ω).sub continuous_const).norm
  have hb : BddAbove ((fun s : ℝ≥0 => ‖B s ω - x‖) '' Set.Icc 0 T) :=
    (isCompact_Icc.image hc).bddAbove
  exact le_csSup hb ⟨s, ⟨zero_le, hs⟩, rfl⟩

theorem measurable_pathRadius {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (hm : ∀ s, Measurable (B s))
    (hBc : ∀ ω, Continuous fun s => B s ω) (x : Space d) (T : ℝ≥0) :
    Measurable (brownianPathRadius B x T) := by
  apply measurable_of_Ioi
  intro a
  have he : (brownianPathRadius B x T) ⁻¹' Set.Ioi a =
      {ω | ∃ s : ℝ≥0, s ≤ T ∧ a < ‖B s ω - x‖} := by
    ext ω
    exact lt_pathRadius B hBc x T ω a
  rw [he]
  exact LatticeProb.measurableSet_exists_le_lt_norm B hm hBc x a T

theorem brownian_pathRadius_tail (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
      ∀ (x : Space d) (B : ℝ≥0 → Ω → Space d), IsBrownian d x B P →
      (∀ ω, Continuous fun s => B s ω) → ∀ (T : ℝ≥0) (a : ℝ), 0 < a →
      P {ω | a < brownianPathRadius B x T ω} ≤
        ENNReal.ofReal (C * Real.exp (-(c * a ^ 2 / ((T : ℝ) + 1)))) := by
  obtain ⟨C, c, hC, hc, ht⟩ := LatticeProb.brownian_exit_tail_pos d
  refine ⟨C, c, hC, hc, ?_⟩
  intro Ω _ P hP x B hB hBc T a ha
  have hsub : {ω | a < brownianPathRadius B x T ω} ⊆
      {ω | ∃ s : ℝ≥0, (s : ℝ) < (T : ℝ) + 1 ∧ a < ‖B s ω - x‖} := by
    intro ω hω
    obtain ⟨s, hs, hn⟩ := (lt_pathRadius B hBc x T ω a).mp hω
    refine ⟨s, ?_, hn⟩
    have : (s : ℝ) ≤ (T : ℝ) := hs
    linarith
  exact (measure_mono hsub).trans
    (ht x Ω P hP B (isBrownianSpace_of_isBrownian hB) a ha ((T : ℝ) + 1) (by positivity))

theorem summable_polynomial_mul_gaussian (p : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => ((n : ℝ) + 2) ^ p * Real.exp (-(a * (n : ℝ) ^ 2))) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ p * Real.exp (-a * ((n : ℝ) + 2))) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 2).mpr (Real.summable_pow_mul_exp_neg_nat_mul p ha)
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (hbase.mul_left (Real.exp (2 * a)))
  intro n
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ n =>
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast
      nlinarith [sq_nonneg (n : ℝ)]
  have he : Real.exp (-(a * (n : ℝ) ^ 2)) ≤ Real.exp (-a * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc ((n : ℝ) + 2) ^ p * Real.exp (-(a * (n : ℝ) ^ 2))
      ≤ ((n : ℝ) + 2) ^ p * Real.exp (-a * (n : ℝ)) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = Real.exp (2 * a) * (((n : ℝ) + 2) ^ p * Real.exp (-a * ((n : ℝ) + 2))) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring

theorem integrable_polynomial_of_summable_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (R : Ω → ℝ) (hm : Measurable R)
    (hn : ∀ ω, 0 ≤ R ω) (p : ℕ)
    (hs : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ p * P.real {ω | (n : ℝ) ≤ R ω})) :
    Integrable (fun ω => (1 + R ω) ^ p) P := by
  let S : ℕ → Set Ω := fun n => {ω | (n : ℝ) ≤ R ω ∧ R ω ≤ (n : ℝ) + 1}
  have hS (n : ℕ) : MeasurableSet (S n) :=
    (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  have hb (n : ℕ) : ∀ᵐ ω ∂P.restrict (S n), ‖(1 + R ω) ^ p‖ ≤ ((n : ℝ) + 2) ^ p := by
    filter_upwards [ae_restrict_mem (hS n)] with ω hω
    have hR := hn ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by dsimp [S] at hω; linarith [hω.2]) p
  have hi (n : ℕ) : IntegrableOn (fun ω => (1 + R ω) ^ p) (S n) P := by
    exact (integrable_const (((n : ℝ) + 2) ^ p)).mono'
      ((measurable_const.add hm).pow_const p).aestronglyMeasurable (hb n)
  have hsum : Summable (fun n : ℕ => ∫ ω in S n, ‖(1 + R ω) ^ p‖ ∂P) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) _ hs
    intro n
    calc (∫ ω in S n, ‖(1 + R ω) ^ p‖ ∂P)
        ≤ ∫ _ in S n, ((n : ℝ) + 2) ^ p ∂P := integral_mono_ae (hi n).norm (integrable_const _) (hb n)
      _ = ((n : ℝ) + 2) ^ p * P.real (S n) := by simp [integral_const, Measure.real, mul_comm]
      _ ≤ ((n : ℝ) + 2) ^ p * P.real {ω | (n : ℝ) ≤ R ω} := by
          apply mul_le_mul_of_nonneg_left (measureReal_mono (fun ω hω => hω.1))
          positivity
  have hu : (⋃ n, S n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    exact Set.mem_iUnion.mpr ⟨⌊R ω⌋₊, Nat.floor_le (hn ω), (Nat.lt_floor_add_one (R ω)).le⟩
  have hh := integrableOn_iUnion_of_summable_integral_norm hi hsum
  simpa only [hu, integrableOn_univ] using hh

/-- Every polynomial moment of the compact-time Brownian maximum is finite. -/
theorem integrable_brownian_pathRadius_pow {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {x : Space d}
    {B : ℝ≥0 → Ω → Space d} (hB : IsBrownian d x B P)
    (hm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (T : ℝ≥0) (p : ℕ) : Integrable (fun ω => (1 + brownianPathRadius B x T ω) ^ p) P := by
  let R := brownianPathRadius B x T
  have hR (ω : Ω) : 0 ≤ R ω := (norm_nonneg (B 0 ω - x)).trans
    (norm_le_pathRadius B hBc x T ω (s := 0) zero_le)
  apply integrable_polynomial_of_summable_tail P R
    (measurable_pathRadius B hm hBc x T) hR p
  obtain ⟨C, c, hC, hc, htail⟩ := brownian_pathRadius_tail d
  let a : ℝ := c / (4 * ((T : ℝ) + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hs := (summable_polynomial_mul_gaussian p ha).mul_left C
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ ((summable_nat_add_iff 1).mpr hs)
  intro n
  let m : ℝ := (n + 1 : ℕ)
  have hmpos : 0 < m := by dsimp [m]; positivity
  have hsub : {ω | m ≤ R ω} ⊆ {ω | m / 2 < brownianPathRadius B x T ω} := by
    intro ω hω
    change m ≤ brownianPathRadius B x T ω at hω
    change m / 2 < brownianPathRadius B x T ω
    linarith
  have ht := (measure_mono hsub).trans
    (htail Ω P inferInstance x B hB hBc T (m / 2) (by positivity))
  have he : -(c * (m / 2) ^ 2 / ((T : ℝ) + 1)) = -(a * m ^ 2) := by
    dsimp [a]
    field_simp
    ring
  rw [he] at ht
  have ht' : P.real {ω | m ≤ R ω} ≤ C * Real.exp (-(a * m ^ 2)) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
    simpa only [Measure.real, ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.exp_nonneg _))] using hh
  calc (m + 2) ^ p * P.real {ω | m ≤ R ω}
      ≤ (m + 2) ^ p * (C * Real.exp (-(a * m ^ 2))) := mul_le_mul_of_nonneg_left ht' (by positivity)
    _ = C * ((m + 2) ^ p * Real.exp (-(a * m ^ 2))) := by ring
/-- Polynomial spatial growth gives one integrable bound for all bounded stopping rewards. -/
theorem exists_brownian_envelope_of_polynomial_growth {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {x : Space d}
    {B : ℝ≥0 → Ω → Space d} (hB : IsBrownian d x B P)
    (hm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (h : ℝ → Space d → ℝ) (T : ℝ≥0) (C : ℝ) (hC : 0 ≤ C) (p : ℕ)
    (hg : ∀ v : ℝ≥0, v ≤ T → ∀ y, ‖h v y‖ ≤ C * (1 + ‖y - x‖) ^ p) :
    ∃ D : Ω → ℝ, Integrable D P ∧ ∀ ω, ∀ v : ℝ≥0, v ≤ T →
      ∀ r : ℝ≥0, r ≤ T → ‖h v (B r ω)‖ ≤ D ω := by
  refine ⟨fun ω => C * (1 + brownianPathRadius B x T ω) ^ p,
    (integrable_brownian_pathRadius_pow hB hm hBc T p).const_mul C, ?_⟩
  intro ω v hv r hr
  apply (hg v hv (B r ω)).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact pow_le_pow_left₀ (by positivity)
    (by linarith [norm_le_pathRadius B hBc x T ω hr]) p
end Sandpile.Support

namespace Sandpile.Continuum
open Sandpile.Continuum

theorem bddAbove_stoppingPayoffs_of_integrable_envelope {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Space d}
    {x : Space d} (hB : IsBrownian d x B P)
    (h : ℝ → Space d → ℝ) (T : ℝ)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (D : Ω → ℝ) (hD : Integrable D P)
    (hdom : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : ℝ) ≤ T → ‖h (T - r) (B r ω)‖ ≤ D ω) :
    BddAbove (stoppingPayoffs B P h T) := by
  refine ⟨∫ ω, D ω ∂P, ?_⟩
  rintro a ⟨τ, hτ, hτT, rfl⟩
  have ht := hτ.aemeasurable P hB.aemeasurable
  have hy := aemeasurable_stopped_position P hB.aemeasurable
    (isBrownianSpace_of_isBrownian hB).cont ht
  have hm := aemeasurable_stopped_payoff_of_continuousOn P τ _ ht hy h T hc hτT
  have hb : ∀ᵐ ω ∂P, ‖-h (T - τ ω) (B (τ ω) ω)‖ ≤ D ω := by
    filter_upwards [hdom] with ω hω
    simpa only [norm_neg] using hω (τ ω) (hτT ω)
  exact integral_mono_ae (hD.mono' hm.aestronglyMeasurable hb) hD
    (hb.mono fun ω hω => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hω))
end Sandpile.Continuum
