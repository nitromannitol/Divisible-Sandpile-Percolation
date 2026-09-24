/-
The value is a measurable functional of the field's sample point, by clamping.

The value `𝒰_Z(T,x)` reads the field at every point the motion can reach before
`T`, which is an unbounded set, so the measurability of `ω ↦ 𝒰_Z(T,x)(ω)` is not
a pointwise statement.  The route here is the one the continuous
modification makes available: clamp the field radially to the ball of radius `n`.
The clamped field is bounded, and the value built from it reads the field only
through its restriction to the compact box `[0,T] × B(0,n)`, where the value is a
continuous functional of the field in the sup norm and the field is measurable as
a map into the continuous functions.  The clamped values converge to the value of
`Z` as `n → ∞`, because the clamped field differs from `Z` only outside the ball
and the motion leaves the ball with probability tending to zero.

This module carries the pointwise bound on the clamped field and the elementary
supremum comparison used by the convergence step.
-/
import Sandpile.Continuum.Kernel
import Sandpile.Support.ContValueLipschitz
import Sandpile.Support.ContValueMeasurable
import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal
open Sandpile.Continuum

namespace Sandpile.Support

/-- **Two nonempty bounded-above sets of reals whose elements are pairwise within
`ε` have suprema within `ε`.**  This is the comparison of the clamped value with
the value, once the two attainable sets are known to be within `ε` elementwise. -/
theorem abs_sSup_sub_le_of_close {S T : Set ℝ} (hS : S.Nonempty) (hT : T.Nonempty)
    (hbS : BddAbove S) (hbT : BddAbove T) {ε : ℝ} (_hε : 0 ≤ ε)
    (h1 : ∀ a ∈ S, ∃ b ∈ T, |a - b| ≤ ε) (h2 : ∀ b ∈ T, ∃ a ∈ S, |a - b| ≤ ε) :
    |sSup S - sSup T| ≤ ε := by
  rw [abs_sub_le_iff]
  constructor
  · refine sub_le_iff_le_add'.mpr ?_
    refine csSup_le hS ?_
    intro a ha
    obtain ⟨b, hb, hbε⟩ := h1 a ha
    have hbT' : b ≤ sSup T := le_csSup hbT hb
    have h1' : a - b ≤ ε := (abs_le.mp hbε).2
    linarith
  · refine sub_le_iff_le_add'.mpr ?_
    refine csSup_le hT ?_
    intro b hb
    obtain ⟨a, ha, haε⟩ := h2 b hb
    have haS' : a ≤ sSup S := le_csSup hbS ha
    have h2' : b - a ≤ ε := by linarith [(abs_le.mp haε).1]
    linarith

/-- The radial clamp of a field to the ball of radius `n`. -/
noncomputable def clampField (d : ℕ) (n : ℝ) (h : ℝ → Space d → ℝ) : ℝ → Space d → ℝ :=
  fun t y => h t (if ‖y‖ ≤ n then y else (n / ‖y‖) • y)

/-- **The clamped field is bounded by `C (1+n)^k`.**  The clamp maps every point into
the closed ball of radius `n`, so the polynomial growth bound of the field at the
clamped point is the bound at radius `n`. -/
theorem abs_clampField_le {d : ℕ} (h : ℝ → Space d → ℝ) (C k : ℝ)
    (hC : 0 ≤ C) (hk : 0 ≤ k) (hbound : ∀ t y, |h t y| ≤ C * (1 + ‖y‖) ^ k)
    {n : ℝ} (hn : 0 < n) (t : ℝ) (y : Space d) :
    |clampField d n h t y| ≤ C * (1 + n) ^ k := by
  by_cases hy : ‖y‖ ≤ n
  · simp only [clampField, if_pos hy]
    exact (hbound t y).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) hk) hC)
  · simp only [clampField, if_neg hy]
    have hnorm : ‖(n / ‖y‖) • y‖ = n := by
      have hpos : 0 < ‖y‖ := by
        have : n < ‖y‖ := not_le.mp hy
        linarith
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hn hpos)]
      field_simp
    have h := hbound t ((n / ‖y‖) • y)
    rw [hnorm] at h
    exact h

/-- **The clamped value is within `2E` of the value** when the clamped field is within
`E` of the field on `[0,T] × ℝ^d`.  This is the Lipschitz bound of
`abs_brownianValue_sub_le_of_field` at the two fields `clampField d n h` and `h`. -/
theorem abs_brownianValue_clamp_sub_le {ΩB : Type*} [MeasurableSpace ΩB]
    (d : ℕ) (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) [IsProbabilityMeasure P]
    (h : ℝ → Space d → ℝ) (T E : ℝ) (hT : 0 ≤ T) (x : Space d) {n : ℝ} (_hn : 0 < n)
    (hbdd : ∀ h : ℝ → Space d → ℝ, BddAbove (stoppingPayoffs B P h T))
    (hint : ∀ (h : ℝ → Space d → ℝ), (∀ s ∈ Set.Icc (0:ℝ) T, ∀ _y : Space d,
        ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
          Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P))
    (hgap : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : Space d, |clampField d n h s y - h s y| ≤ E) :
    |brownianValue B P (clampField d n h) T x - brownianValue B P h T x| ≤ 2 * E := by
  exact Sandpile.Support.abs_brownianValue_sub_le_of_field d B P (clampField d n h) h T E hT x
    (hbdd _) (hbdd _)
    (fun τ hτ hb => hint _ 0 ⟨le_refl 0, hT⟩ x τ hτ hb)
    (fun τ hτ hb => hint _ 0 ⟨le_refl 0, hT⟩ x τ hτ hb)
    hgap

/-- The radial clamp of a point to the closed ball of radius `n`. -/
noncomputable def clampPoint (d : ℕ) (n : ℝ) (y : Space d) : Space d :=
  if ‖y‖ ≤ n then y else (n / ‖y‖) • y

/-- The clamp lands in the closed ball of radius `n`. -/
theorem norm_clampPoint_le (d : ℕ) {n : ℝ} (hn : 0 < n) (y : Space d) :
    ‖clampPoint d n y‖ ≤ n := by
  by_cases hy : ‖y‖ ≤ n
  · simpa [clampPoint, if_pos hy] using hy
  · have hpos : 0 < ‖y‖ := lt_of_lt_of_le hn (le_of_lt (lt_of_not_ge hy))
    simp only [clampPoint, if_neg hy]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hn hpos)]
    exact le_of_eq (div_mul_cancel₀ n (ne_of_gt hpos))

/-- The clamp is the identity on the ball. -/
theorem clampPoint_eq_self (d : ℕ) {n : ℝ} {y : Space d} (hy : ‖y‖ ≤ n) :
    clampPoint d n y = y := by
  simp only [clampPoint, if_pos hy]

/-- The clamp of a time to `[0,T]`. -/
noncomputable def clampTime (T t : ℝ) : ℝ := max 0 (min t T)

/-- The clamped time lies in `[0,T]` when `0 ≤ T`. -/
theorem clampTime_mem_Icc {T t : ℝ} (hT : 0 ≤ T) : clampTime T t ∈ Set.Icc (0:ℝ) T :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- The clamped time is the identity on `[0,T]`. -/
theorem clampTime_eq_self {T t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) : clampTime T t = t := by
  simp only [clampTime, Set.mem_Icc] at ht ⊢
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- The field read through the clamp, as a functional of the field on the box. -/
noncomputable def clampFunctional (d : ℕ) (T n : ℝ) (hn : 0 < n) (hT : 0 ≤ T)
    (v : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) n, ℝ)) :
    ℝ → Space d → ℝ :=
  fun t z => v ⟨(clampTime T t, clampPoint d n z),
    ⟨clampTime_mem_Icc hT, by
      simpa [Metric.mem_closedBall, dist_zero_right] using norm_clampPoint_le d hn z⟩⟩

/-- A Lipschitz map between metric spaces with Borel structure is measurable. -/
theorem measurable_of_lipschitzWith {α β : Type*} [PseudoEMetricSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [PseudoEMetricSpace β] [MeasurableSpace β] [BorelSpace β]
    {K : ℝ≥0} {f : α → β} (hf : LipschitzWith K f) : Measurable f :=
  hf.continuous.measurable

/-- **The clamped value is Lipschitz in the field's restriction to the box.**  Two fields
agreeing on `[0,T] × closedBall 0 n` have the same clamp, hence values within `2 * dist`
by `abs_brownianValue_clamp_sub_le`. -/
theorem lipschitzWith_clamp_value {ΩB : Type*} [MeasurableSpace ΩB]
    (d : ℕ) (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (T n : ℝ) (hT : 0 < T) (hn : 0 < n) (x : Space d)
    (hbdd : ∀ h : ℝ → Space d → ℝ, BddAbove (stoppingPayoffs B PB h T))
    (hint : ∀ (h : ℝ → Space d → ℝ), (∀ s ∈ Set.Icc (0:ℝ) T, ∀ _y : Space d,
        ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
          Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) PB))
    [CompactSpace ↥(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) n)] :
    LipschitzWith 2 (fun v : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) n, ℝ) =>
      brownianValue B PB (clampFunctional d T n hn hT.le v) T x) := by
  refine LipschitzWith.of_dist_le_mul fun v v' => ?_
  rw [dist_eq_norm, Real.norm_eq_abs]
  have hgap : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ y : Space d,
      |clampFunctional d T n hn hT.le v s y - clampFunctional d T n hn hT.le v' s y|
        ≤ dist v v' := by
    intro s hs y
    have h1 : clampFunctional d T n hn hT.le v s y
        = v ⟨(s, clampPoint d n y), ⟨hs, by
            simpa [Metric.mem_closedBall, dist_zero_right] using norm_clampPoint_le d hn y⟩⟩ := by
      simp only [clampFunctional, clampTime_eq_self hs]
    have h2 : clampFunctional d T n hn hT.le v' s y
        = v' ⟨(s, clampPoint d n y), ⟨hs, by
            simpa [Metric.mem_closedBall, dist_zero_right] using norm_clampPoint_le d hn y⟩⟩ := by
      simp only [clampFunctional, clampTime_eq_self hs]
    rw [h1, h2, ← Real.dist_eq]
    exact ContinuousMap.dist_apply_le_dist _
  have h := abs_brownianValue_sub_le_of_field d B PB
    (clampFunctional d T n hn hT.le v) (clampFunctional d T n hn hT.le v')
    T (dist v v') hT.le x (hbdd _) (hbdd _)
    (fun τ hτ hb => hint _ 0 ⟨le_refl 0, hT.le⟩ x τ hτ hb)
    (fun τ hτ hb => hint _ 0 ⟨le_refl 0, hT.le⟩ x τ hτ hb)
    hgap
  simpa using h

/-- **The clamped value is almost everywhere measurable in the sample point.**  The
field's restriction to the box is almost everywhere measurable as a map into the
continuous functions on the box (`aemeasurable_field_box`), and the clamped value is a
Lipschitz, hence measurable, functional of that restriction
(`lipschitzWith_clamp_value`). -/
theorem aemeasurable_clamp_value {ΩW ΩB : Type*} [MeasurableSpace ΩW]
    [MeasurableSpace ΩB] (d : ℕ) (Z : ℝ → Space d → ΩW → ℝ) (PW : Measure ΩW)
    (b : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (T n : ℝ) (hT : 0 < T) (hn : 0 < n) (x : Space d)
    (hbdd : ∀ h : ℝ → Space d → ℝ, BddAbove (stoppingPayoffs b PB h T))
    (hint : ∀ (h : ℝ → Space d → ℝ), (∀ s ∈ Set.Icc (0:ℝ) T, ∀ _y : Space d,
        ∀ τ : ΩB → ℝ≥0, IsBrownianStopping b τ → (∀ ω, (τ ω : ℝ) ≤ T) →
          Integrable (fun ω => -h (T - τ ω) (b (τ ω) ω)) PB))
    [MeasurableSpace C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) n, ℝ)]
    [BorelSpace C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) n, ℝ)]
    (hZmeas : ∀ p : Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) n,
      AEMeasurable (fun ω => Z p.1.1 p.1.2 ω) PW)
    (hZcont : ∀ᵐ ω ∂PW, Continuous (fun p : Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) n =>
      Z p.1.1 p.1.2 ω)) :
    AEMeasurable (fun ω => brownianValue b PB
      (clampFunctional d T n hn hT.le
        (ContinuousMap.mkD (fun p : Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) n =>
          Z p.1.1 p.1.2 ω) 0)) T x) PW := by
  haveI : CompactSpace ↥(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) n) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod (isCompact_closedBall 0 n))
  exact (measurable_of_lipschitzWith
      (lipschitzWith_clamp_value d b PB T n hT hn x hbdd hint)).comp_aemeasurable
    (aemeasurable_field_box PW d T n Z hZmeas hZcont)

/-- **The value depends on the field only through its values on `[0,T] × ℝ^d`.**  If two
fields agree there, the values agree: the discount is `2`-Lipschitz in the field in the
supremum norm on that set, and the gap is `0`. -/
theorem brownianValue_congr_of_eq_on {ΩB : Type*} [MeasurableSpace ΩB]
    (d : ℕ) (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (h h' : ℝ → Space d → ℝ) (T : ℝ) (x : Space d)
    (hT : 0 ≤ T)
    (hbdd : BddAbove (stoppingPayoffs B PB h T))
    (hbdd' : BddAbove (stoppingPayoffs B PB h' T))
    (hint : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) PB)
    (hint' : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h' (T - τ ω) (B (τ ω) ω)) PB)
    (hagree : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ y : Space d, h s y = h' s y) :
    brownianValue B PB h T x = brownianValue B PB h' T x := by
  have h1 : |h T x - h' T x| ≤ 0 := by
    rw [hagree T ⟨hT, le_refl T⟩ x, sub_self, abs_zero]
  have h2 : |brownianDiscount B PB h T - brownianDiscount B PB h' T| ≤ 0 :=
    Sandpile.Continuum.abs_brownianDiscount_sub_le_of_reward B PB h h' T 0 hT hbdd hbdd' hint hint'
      (fun s hs y => by rw [hagree s hs y, sub_self, abs_zero])
  unfold brownianValue
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  linarith

/-- **The clamped field converges pointwise to the field** as the clamp radius
grows, at every `(t,y)`. -/
theorem clampField_tendsto {d : ℕ} (h : ℝ → Space d → ℝ)
    (hcont : Continuous (fun p : ℝ × Space d => h p.1 p.2))
    (t : ℝ) (y : Space d) :
    Tendsto (fun n : ℕ => clampField d (n : ℝ) h t y) atTop (𝓝 (h t y)) := by
  have hev : (fun n : ℕ => (if ‖y‖ ≤ (n:ℝ) then y else ((n:ℝ)/‖y‖) • y))
      =ᶠ[atTop] fun _ : ℕ => y := by
    filter_upwards [eventually_ge_atTop ⌈‖y‖⌉₊] with n hn
    rw [if_pos]
    have : (⌈‖y‖⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact (Nat.le_ceil ‖y‖).trans this
  have hproj : Tendsto (fun n : ℕ => (if ‖y‖ ≤ (n:ℝ) then y else ((n:ℝ)/‖y‖) • y))
      atTop (𝓝 y) := tendsto_const_nhds.congr' hev.symm
  have hpair : Tendsto (fun n : ℕ => (t, (if ‖y‖ ≤ (n:ℝ) then y else ((n:ℝ)/‖y‖) • y)))
      atTop (𝓝 (t, y)) := Filter.Tendsto.prodMk_nhds tendsto_const_nhds hproj
  have h2 : Tendsto (fun n : ℕ => h t ((if ‖y‖ ≤ (n:ℝ) then y else ((n:ℝ)/‖y‖) • y)))
      atTop (𝓝 (h t y)) := (hcont.continuousAt.tendsto).comp hpair
  simpa [clampField] using h2

/-- **The continuum value is almost everywhere measurable in the field's sample
point**, for a field continuous on `[0,T] x R^d` and with the clamped values
a.e. measurable.  The value is the a.e. pointwise limit of the clamped values,
and `AEMeasurable` is closed under such limits. -/
theorem aemeasurable_brownianValue_of_clamp {ΩW ΩB : Type*} [MeasurableSpace ΩW]
    [MeasurableSpace ΩB]
    (d : ℕ) (Z : ℝ → Space d → ΩW → ℝ) (PW : Measure ΩW)
    (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (T : ℝ) (_hT : 0 < T) (x : Space d)
    (_hZcont : ∀ᵐ ω ∂PW, ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
      (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (hmeas : ∀ n : ℕ, AEMeasurable (fun ω => brownianValue B PB (clampField d (n:ℝ) (fun t z => Z t z ω)) T x) PW)
    (hlim : ∀ᵐ ω ∂PW, Tendsto (fun n : ℕ => brownianValue B PB (clampField d (n:ℝ) (fun t z => Z t z ω)) T x) atTop (𝓝 (brownianValue B PB (fun t z => Z t z ω) T x))) :
    AEMeasurable (fun ω => brownianValue B PB (fun t z => Z t z ω) T x) PW := by
  exact aemeasurable_of_tendsto_metrizable_ae atTop hmeas hlim

end Sandpile.Support
