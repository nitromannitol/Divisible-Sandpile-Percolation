/-
`prop:dgt4-contact-asymptotics` (`sandpile.tex:4823-4825`) from the pointwise
contact thresholds, and the uniform form of those thresholds that
`lem:dgt4-path-survival` consumes.

The paper's own proof of `prop:dgt4-linearization` (`sandpile.tex:5853-5864`)
reads: "The two case-specific parts of Proposition~\ref{prop:dgt4-contact-asymptotics}
give the threshold asymptotic and threshold comparison, hence
\eqref{eq:dgt4-uniform-contact-thresholds}."  Those two are exactly the two
limits of `PointwiseContactThresholds`, and this file performs the two
deductions the sentence names.

* `uniformContactThresholds_of_pointwise`: the maximum over
  `⌈ε n_R⌉ ≤ m ≤ n_R` of the two quantities tends to zero because each tends to
  zero in `m` and `⌈ε n_R⌉ → ∞`.
* `dgt4_contact_of_pointwise`: `P(u_n(0)=0)` and `P(J(0)>E u_{n-1}(0))` differ
  by at most the measure of the symmetric difference of the two events, which is
  `o(1/n)`; so the second limit transports the first from the threshold event to
  the contact event.  Neither event needs to be measurable: a measure is an outer
  measure, and `S ⊆ T ∪ (S Δ T)` is a set inclusion.  That matters, because the
  threshold event of the Gaussian branch is only null measurable
  (`Support/LinThresholdNull.lean`).
-/
import Sandpile.Support.Dgt4Thresholds

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The measures of two arbitrary sets differ by at most the measure of their
symmetric difference.  No measurability is needed. -/
theorem abs_toReal_sub_le_symmDiff {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsFiniteMeasure mu] (S T : Set alpha) :
    |(mu S).toReal - (mu T).toReal| ≤ (mu (symmDiff S T)).toReal := by
  have h1 : S ⊆ T ∪ symmDiff S T := by
    intro x hx
    by_cases h : x ∈ T
    · exact Or.inl h
    · exact Or.inr (Set.mem_symmDiff.mpr (Or.inl ⟨hx, h⟩))
  have h2 : T ⊆ S ∪ symmDiff S T := by
    intro x hx
    by_cases h : x ∈ S
    · exact Or.inl h
    · exact Or.inr (Set.mem_symmDiff.mpr (Or.inr ⟨hx, h⟩))
  have h3 : mu.real S ≤ mu.real T + mu.real (symmDiff S T) :=
    le_trans (measureReal_mono h1) (measureReal_union_le T (symmDiff S T))
  have h4 : mu.real T ≤ mu.real S + mu.real (symmDiff S T) :=
    le_trans (measureReal_mono h2) (measureReal_union_le S (symmDiff S T))
  rw [abs_le]
  constructor <;> simp only [Measure.real] at h3 h4 <;> linarith

/-- `⌈ε n_R⌉ → ∞` as `R → ∞`, for positive `ε` and `T`; this is why a limit in the
single index `m` gives the maximum over `⌈ε n_R⌉ ≤ m ≤ n_R`. -/
theorem tendsto_ceil_mul_floor_atTop {eps T : ℝ} (heps : 0 < eps) (hT : 0 < T) :
    Tendsto (fun R : ℝ => ⌈eps * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊) atTop atTop := by
  have h1 : Tendsto (fun R : ℝ => R ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h2 : Tendsto (fun R : ℝ => R ^ 2 * T) atTop atTop := Filter.Tendsto.atTop_mul_const hT h1
  have h3 : Tendsto (fun R : ℝ => (⌊R ^ 2 * T⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp h2)
  have h4 : Tendsto (fun R : ℝ => eps * (⌊R ^ 2 * T⌋₊ : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop heps h3
  exact tendsto_nat_ceil_atTop.comp h4

/-- The pointwise contact thresholds give the uniform form
`eq:dgt4-uniform-contact-thresholds` that `lem:dgt4-path-survival` assumes. -/
theorem uniformContactThresholds_of_pointwise {ν : Measure ℝ}
    {J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ} {κ T : ℝ} (hT : 0 < T)
    (h : PointwiseContactThresholds d ν J κ) :
    UniformContactThresholds d ν J κ T := by
  obtain ⟨h1, h2⟩ := h
  intro eps heps eta heta
  have hhalf : (0 : ℝ) < eta / 2 := by linarith
  obtain ⟨M1, hM1⟩ := Metric.tendsto_atTop.mp h1 (eta / 2) hhalf
  obtain ⟨M2, hM2⟩ := Metric.tendsto_atTop.mp h2 (eta / 2) hhalf
  have hc := (tendsto_ceil_mul_floor_atTop heps.1 hT).eventually_ge_atTop (max M1 M2)
  filter_upwards [hc] with R hR m hm1 hm2
  have hmax : max M1 M2 ≤ m := le_trans hR hm1
  have hA := hM1 m (le_trans (le_max_left M1 M2) hmax)
  have hB := hM2 m (le_trans (le_max_right M1 M2) hmax)
  rw [Real.dist_eq] at hA hB
  rw [sub_zero] at hB
  have hB' := le_of_lt (lt_of_le_of_lt (le_abs_self _) hB)
  have hA' := le_of_lt hA
  linarith

/-- `prop:dgt4-contact-asymptotics` from the pointwise contact thresholds. -/
theorem dgt4_contact_of_pointwise {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ} {κ : ℝ}
    (hG : 0 < Sandpile.green d 0 0 * κ)
    (h : PointwiseContactThresholds d ν J κ) :
    Tendsto (fun n : ℕ =>
        ((Sandpile.centeredMassLaw d ν) {σ | Sandpile.odometer σ n 0 = 0}).toReal /
          (Sandpile.green d 0 0 * κ / n)) atTop (𝓝 1) := by
  obtain ⟨h1, h2⟩ := h
  set mu := Sandpile.centeredMassLaw d ν with hmu
  set G := Sandpile.green d 0 0 * κ with hGdef
  set A : ℕ → ℝ := fun n => (mu {σ | Sandpile.odometer σ n 0 = 0}).toReal with hA
  set B : ℕ → ℝ := fun n =>
    (mu {σ | Sandpile.meanOdometer mu (n - 1) < J σ 0}).toReal with hB
  set S : ℕ → ℝ := fun n => (mu (symmDiff {σ | Sandpile.odometer σ n 0 = 0}
    {σ | Sandpile.meanOdometer mu (n - 1) < J σ 0})).toReal with hS
  have hdiv : Tendsto (fun n : ℕ => (n : ℝ) * S n / G) atTop (𝓝 0) := by
    simpa using h2.div_const G
  have hkey : Tendsto (fun n : ℕ => (n : ℝ) * A n / G - (n : ℝ) * B n / G) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hdiv
    have hab := abs_toReal_sub_le_symmDiff mu {σ | Sandpile.odometer σ n 0 = 0}
      {σ | Sandpile.meanOdometer mu (n - 1) < J σ 0}
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hstep : (n : ℝ) * A n / G - (n : ℝ) * B n / G = (n : ℝ) * (A n - B n) / G := by ring
    rw [Real.norm_eq_abs, hstep, abs_div, abs_mul, abs_of_nonneg hn, abs_of_pos hG]
    gcongr
  have hsum := h1.add hkey
  rw [add_zero] at hsum
  refine hsum.congr fun n => ?_
  rw [div_div_eq_mul_div]
  ring

end Sandpile
