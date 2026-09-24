/-
Step 3 of `prop:fixed-scale-crossings` (`sandpile.tex:2300-2400`): the level
loss, from the relative entropy of the Cameron-Martin shift.

The paper compares the bottom-top crossing probabilities of `{𝒳_1 < 0}` and of
`{𝒳_1 < L/R}` by shifting the white noise on the cubes the exploration can
reveal.  Both crossing events are read off the same exploration trace `𝔗_M`, so
the comparison is a comparison of the two laws of that trace, and the tool is
Pinsker's inequality applied to one set.

This module is the part of Step 3 that does not mention the exploration: the
passage from a bound on the relative entropy of the two trace laws to a bound on
the difference of the probabilities of an event the trace determines, and the
arithmetic that turns the paper's entropy bound `L²𝔼𝒩/(2𝔪²R²)` together with the
subquadratic bound of `Sandpile/Support/CrossExplore.lean` into the paper's
`C L R^{-α₁/2}`.

An event the trace determines is a preimage `tr ⁻¹' E` under the trace map, and
the two laws are the pushforwards of the two measures along it; that is exactly
the paper's `P_ℓ^{tr}`.
-/
import Sandpile.Support.CrossExplore
import Sandpile.Support.CrossTrace
import Sandpile.Support.CrossEntropyPi
import Sandpile.External.Pinsker

open MeasureTheory Set
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

namespace Sandpile.Support

/-- The level loss from the relative entropy of the trace laws: if the two laws
of the trace are within relative entropy `δ`, then the probabilities of any
event the trace determines differ by at most `√(δ/2)`.  This is Pinsker's
inequality read through the trace map, which is the form
`sandpile.tex:2388-2396` uses. -/
theorem level_loss_of_entropy (hPin : Sandpile.External.Pinsker)
    {Ω : Type} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {T : Type} [MeasurableSpace T] (tr : Ω → T) (htr : Measurable tr)
    (E : Set T) (hE : MeasurableSet E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hent : InformationTheory.klDiv (P₀.map tr) (P₁.map tr) ≤ ENNReal.ofReal δ) :
    P₁.real (tr ⁻¹' E) - P₀.real (tr ⁻¹' E) ≤ Real.sqrt (δ / 2) := by
  haveI h0 : IsProbabilityMeasure (P₀.map tr) := Measure.isProbabilityMeasure_map htr.aemeasurable
  haveI h1 : IsProbabilityMeasure (P₁.map tr) := Measure.isProbabilityMeasure_map htr.aemeasurable
  have hP := hPin T (P₀.map tr) (P₁.map tr) E hE δ hδ hent
  have e0 : (P₀.map tr).real E = P₀.real (tr ⁻¹' E) := by
    simp [measureReal_def, Measure.map_apply htr hE]
  have e1 : (P₁.map tr).real E = P₁.real (tr ⁻¹' E) := by
    simp [measureReal_def, Measure.map_apply htr hE]
  rw [e0, e1] at hP
  calc P₁.real (tr ⁻¹' E) - P₀.real (tr ⁻¹' E)
      = -(P₀.real (tr ⁻¹' E) - P₁.real (tr ⁻¹' E)) := by ring
    _ ≤ |P₀.real (tr ⁻¹' E) - P₁.real (tr ⁻¹' E)| := neg_le_abs _
    _ ≤ Real.sqrt (δ / 2) := hP

/-- Half the relative entropy of the shift, under the square root: the paper's
`L²𝔼𝒩/(2𝔪²R²)` halved is `(L/(2𝔪R))²𝔼𝒩`, so its square root is
`(L/(2𝔪R))√(𝔼𝒩)`, which is the middle term of `sandpile.tex:2392-2398`. -/
theorem sqrt_half_entropy {m L R N : ℝ} (hm : 0 < m) (hL : 0 ≤ L) (hR : 0 < R) :
    Real.sqrt (L ^ 2 * N / (2 * m ^ 2 * R ^ 2) / 2) = L / (2 * m * R) * Real.sqrt N := by
  have key : L ^ 2 * N / (2 * m ^ 2 * R ^ 2) / 2 = (L / (2 * m * R)) ^ 2 * N := by
    rw [div_pow, div_mul_eq_mul_div, div_div]
    congr 1
    ring
  rw [key, Real.sqrt_mul (sq_nonneg (L / (2 * m * R))) N, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ L / (2 * m * R))]

/-- The square root of the subquadratic count of Step 2. -/
theorem sqrt_count_bound {R N Cn α₁ : ℝ} (hR : 1 ≤ R) (hCn : 0 ≤ Cn)
    (hNb : N ≤ Cn * R ^ (2 - α₁)) :
    Real.sqrt N ≤ Real.sqrt Cn * R ^ (1 - α₁ / 2) := by
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have h3 : Real.sqrt (R ^ (2 - α₁)) = R ^ (1 - α₁ / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hR0)]
    congr 1
    ring
  have h2 : Real.sqrt (Cn * R ^ (2 - α₁)) = Real.sqrt Cn * R ^ (1 - α₁ / 2) := by
    rw [Real.sqrt_mul hCn, h3]
  calc Real.sqrt N ≤ Real.sqrt (Cn * R ^ (2 - α₁)) := Real.sqrt_le_sqrt hNb
    _ = Real.sqrt Cn * R ^ (1 - α₁ / 2) := h2

/-- Step 3 of `prop:fixed-scale-crossings` (`sandpile.tex:2392-2398`), in full:
if the two laws of the exploration trace are within relative entropy
`L²𝒩/(2𝔪²R²)` and the expected count `𝒩` is at most `Cn R^{2-α₁}`, then the
probabilities of an event the trace determines differ by at most
`(√Cn/(2𝔪)) L R^{-α₁/2}`.  The constant in front of `L R^{-α₁/2}` is the paper's
`C`, written out.  The exploration enters only through the trace map and the
entropy bound; the count enters only through `Sandpile.Support.expected_processed_le`. -/
theorem level_loss_of_exploration (hPin : Sandpile.External.Pinsker)
    {Ω : Type} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {T : Type} [MeasurableSpace T] (tr : Ω → T) (htr : Measurable tr)
    (E : Set T) (hE : MeasurableSet E)
    (m L R N Cn α₁ : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (hR : 1 ≤ R)
    (hN : 0 ≤ N) (hCn : 0 ≤ Cn) (hNb : N ≤ Cn * R ^ (2 - α₁))
    (hent : InformationTheory.klDiv (P₀.map tr) (P₁.map tr)
      ≤ ENNReal.ofReal (L ^ 2 * N / (2 * m ^ 2 * R ^ 2))) :
    P₁.real (tr ⁻¹' E) - P₀.real (tr ⁻¹' E)
      ≤ Real.sqrt Cn / (2 * m) * L * R ^ (-(α₁ / 2)) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hRne : R ≠ 0 := ne_of_gt hR0
  have hδ : (0 : ℝ) ≤ L ^ 2 * N / (2 * m ^ 2 * R ^ 2) := by positivity
  have hstep := level_loss_of_entropy hPin P₀ P₁ tr htr E hE _ hδ hent
  have hval := sqrt_half_entropy (m := m) (L := L) (R := R) (N := N) hm hL hR0
  rw [hval] at hstep
  have hfac : (0 : ℝ) ≤ L / (2 * m * R) := by positivity
  have hcount : L / (2 * m * R) * Real.sqrt N
      ≤ L / (2 * m * R) * (Real.sqrt Cn * R ^ (1 - α₁ / 2)) :=
    mul_le_mul_of_nonneg_left (sqrt_count_bound hR hCn hNb) hfac
  have hRsplit : R ^ (1 - α₁ / 2) = R * R ^ (-(α₁ / 2)) := by
    calc R ^ (1 - α₁ / 2) = R ^ ((1 : ℝ) + -(α₁ / 2)) := by rw [sub_eq_add_neg]
      _ = R ^ (1 : ℝ) * R ^ (-(α₁ / 2)) := Real.rpow_add hR0 1 (-(α₁ / 2))
      _ = R * R ^ (-(α₁ / 2)) := by rw [Real.rpow_one]
  have hcancel : L / (2 * m * R) * (Real.sqrt Cn * (R * R ^ (-(α₁ / 2))))
      = Real.sqrt Cn / (2 * m) * L * R ^ (-(α₁ / 2)) := by
    rw [div_mul_eq_mul_div,
      show L * (Real.sqrt Cn * (R * R ^ (-(α₁ / 2))))
        = (Real.sqrt Cn * L * R ^ (-(α₁ / 2))) * R from by ring,
      mul_div_mul_right _ _ hRne]
    ring
  rw [hRsplit, hcancel] at hcount
  linarith


/-- The level loss in the form the fixed-scale assembly asks for: a real
comparison of two probabilities, read as a comparison of the two measures.  The
crossing events are not known to be measurable, and `P` applied to a set is its
outer measure, which is what this statement compares; both are finite, so the
real comparison transports. -/
theorem measure_le_add_ofReal {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (s t : Set Ω) (c : ℝ) (hc : 0 ≤ c)
    (h : P.real s - P.real t ≤ c) : P s ≤ P t + ENNReal.ofReal c := by
  have hs : P s ≠ ⊤ := measure_ne_top P s
  have ht : P t ≠ ⊤ := measure_ne_top P t
  have h1 : P.real s ≤ P.real t + c := by linarith
  have h2 : ENNReal.ofReal (P.real s) ≤ ENNReal.ofReal (P.real t + c) :=
    ENNReal.ofReal_le_ofReal h1
  rw [ENNReal.ofReal_add measureReal_nonneg hc] at h2
  rwa [measureReal_def, measureReal_def, ENNReal.ofReal_toReal hs, ENNReal.ofReal_toReal ht] at h2

/-- Step 3 of `prop:fixed-scale-crossings` with the entropy of the trace laws
supplied by the finite-dimensional Gaussian computation of
`Sandpile/Support/CrossEntropyPi.lean`: the two laws of the trace are the standard
Gaussian product and the shifted Gaussian product on the `n` revealed
coordinates, so the relative entropy is `n L²/(2𝔪²R²)` and the level loss is
`(√Cn/(2𝔪)) L R^{-α₁/2}`, the display `sandpile.tex:2392-2398`. -/
theorem level_loss_of_trace (hPin : Sandpile.External.Pinsker)
    {Ω : Type} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {T : Type} [MeasurableSpace T] (tr : Ω → T) (htr : Measurable tr)
    (E : Set T) (hE : MeasurableSet E)
    (n : ℕ) (m L R Cn α₁ : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (hR : 1 ≤ R)
    (hCn : 0 ≤ Cn) (hNb : (n : ℝ) ≤ Cn * R ^ (2 - α₁))
    (hent : InformationTheory.klDiv (P₀.map tr) (P₁.map tr)
      = ENNReal.ofReal ((n : ℝ) * (L ^ 2 / (2 * m ^ 2 * R ^ 2)))) :
    P₁.real (tr ⁻¹' E) - P₀.real (tr ⁻¹' E)
      ≤ Real.sqrt Cn / (2 * m) * L * R ^ (-(α₁ / 2)) := by
  have hN : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hkey : (n : ℝ) * (L ^ 2 / (2 * m ^ 2 * R ^ 2)) = L ^ 2 * (n : ℝ) / (2 * m ^ 2 * R ^ 2) := by
    ring
  rw [hkey] at hent
  exact level_loss_of_exploration hPin P₀ P₁ tr htr E hE m L R (n : ℝ) Cn α₁ hm hL hR hN hCn hNb hent.le

/-- The real comparison of two probabilities transports to the two measures, for
two different probability measures.  This is `measure_le_add_ofReal` with the
second measure allowed to differ from the first. -/
theorem measure_le_add_ofReal' {Ω : Type} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] (s t : Set Ω) (c : ℝ) (hc : 0 ≤ c)
    (h : P₀.real s - P₁.real t ≤ c) : P₀ s ≤ P₁ t + ENNReal.ofReal c := by
  have hs : P₀ s ≠ ⊤ := measure_ne_top P₀ s
  have ht : P₁ t ≠ ⊤ := measure_ne_top P₁ t
  have h1 : P₀.real s ≤ P₁.real t + c := by linarith
  have h2 : ENNReal.ofReal (P₀.real s) ≤ ENNReal.ofReal (P₁.real t + c) :=
    ENNReal.ofReal_le_ofReal h1
  rw [ENNReal.ofReal_add measureReal_nonneg hc] at h2
  rwa [measureReal_def, measureReal_def, ENNReal.ofReal_toReal hs, ENNReal.ofReal_toReal ht] at h2

/-- The level loss `hloss` of `fixed_scale_crossings_ball` from the two laws of
the exploration trace: the trace reads `n` coordinates, the two laws differ by
the Cameron--Martin shift of relative entropy `n L²/(2𝔪²R²)`, the count is at
most `Cn R^{2-α₁}`, and the two crossing events are the trace preimages of one
measurable event.  This is the display `sandpile.tex:2392-2398` in the form the
fixed-scale assembly consumes. -/
theorem hloss_of_trace (hPin : Sandpile.External.Pinsker)
    {Ω : Type} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {T : Type} [MeasurableSpace T] (tr : Ω → T) (htr : Measurable tr)
    (E : Set T) (hE : MeasurableSet E)
    (n : ℕ) (m L R Cn α₁ : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (hR : 1 ≤ R)
    (hCn : 0 ≤ Cn) (hNb : (n : ℝ) ≤ Cn * R ^ (2 - α₁))
    (hent : InformationTheory.klDiv (P₁.map tr) (P₀.map tr)
      = ENNReal.ofReal ((n : ℝ) * (L ^ 2 / (2 * m ^ 2 * R ^ 2)))) :
    P₀ (tr ⁻¹' E) ≤ P₁ (tr ⁻¹' E) + ENNReal.ofReal (Real.sqrt Cn / (2 * m) * L * R ^ (-(α₁ / 2))) := by
  have hstep := level_loss_of_trace hPin P₁ P₀ tr htr E hE n m L R Cn α₁ hm hL hR hCn hNb hent
  have hc : (0 : ℝ) ≤ Real.sqrt Cn / (2 * m) * L * R ^ (-(α₁ / 2)) := by positivity
  exact measure_le_add_ofReal' P₀ P₁ (tr ⁻¹' E) (tr ⁻¹' E) _ hc (by linarith)

/-- The level loss of `prop:fixed-scale-crossings` for a field read through the
trace map on the finitely many coordinates `q` the exploration evaluates: the
two crossing events are the trace preimages of one measurable event `E`, and the
two trace laws differ by the Cameron--Martin entropy `n L²/(2𝔪²R²)`.  This is
the display `sandpile.tex:2392-2398` with the trace map of Step 3 written out. -/
theorem hloss_ballField (hPin : Sandpile.External.Pinsker)
    {Ω : Type} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    {n : ℕ} (q : Fin n → Sandpile.Continuum.Space 2)
    (E : Set (Fin n → ℝ)) (hE : MeasurableSet E)
    (m L R Cn α₁ : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (hR : 1 ≤ R)
    (hCn : 0 ≤ Cn) (hNb : (n : ℝ) ≤ Cn * R ^ (2 - α₁))
    (hent : InformationTheory.klDiv
      (P₁.map fun ω => (fun i : Fin n => X (q i) ω))
      (P₀.map fun ω => (fun i : Fin n => X (q i) ω))
      = ENNReal.ofReal ((n : ℝ) * (L ^ 2 / (2 * m ^ 2 * R ^ 2)))) :
    P₀ ((fun ω => (fun i : Fin n => X (q i) ω)) ⁻¹' E) ≤
      P₁ ((fun ω => (fun i : Fin n => X (q i) ω)) ⁻¹' E) +
        ENNReal.ofReal (Real.sqrt Cn / (2 * m) * L * R ^ (-(α₁ / 2))) :=
  hloss_of_trace hPin P₀ P₁ (fun ω => (fun i : Fin n => X (q i) ω))
    (measurable_trace_fin hX q) E hE n m L R Cn α₁ hm hL hR hCn hNb hent

/-- The level loss of `prop:fixed-scale-crossings` in the shape the assembly
consumes, with the two trace laws identified as the two Gaussian products of
Step 3 (`sandpile.tex:2378-2382`): the entropy hypothesis of `hloss_ballField`
is then the chain-rule value `n L²/(2𝔪²R²)`. -/
theorem hloss_ballField_of_laws
    (hPin : Sandpile.External.Pinsker)
    {Ω : Type} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    {n : ℕ} (q : Fin n → Sandpile.Continuum.Space 2)
    (E : Set (Fin n → ℝ)) (hE : MeasurableSet E)
    (m L R Cn α₁ : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (hR : 1 ≤ R)
    (hCn : 0 ≤ Cn) (hNb : (n : ℝ) ≤ Cn * R ^ (2 - α₁))
    (h₀ : P₁.map (fun ω => (fun i : Fin n => X (q i) ω))
      = Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
    (h₁ : P₀.map (fun ω => (fun i : Fin n => X (q i) ω))
      = Measure.pi fun _ : Fin n =>
          ProbabilityTheory.gaussianReal (L / (m * R)) 1) :
    P₀ ((fun ω => (fun i : Fin n => X (q i) ω)) ⁻¹' E) ≤
      P₁ ((fun ω => (fun i : Fin n => X (q i) ω)) ⁻¹' E) +
        ENNReal.ofReal (Real.sqrt Cn / (2 * m) * L * R ^ (-(α₁ / 2))) := by
  refine hloss_ballField (n := n) hPin P₀ P₁ hX q E hE m L R Cn α₁ hm hL hR hCn hNb ?_
  rw [h₀, h₁]
  exact klDiv_trace_laws hm (lt_of_lt_of_le zero_lt_one hR) _ _ rfl rfl

/-- The level loss of Steps 2-3 for the ball field, from the exploration data:
the trace map on the finitely many coordinates the exploration reads, the
crossing event as its preimage, the two trace laws, and the subquadratic count.
This is the hypothesis `hloss` of `fixed_scale_crossings_ball` with the
exploration written out. -/
theorem hloss_of_exploration_data
    (hPin : Sandpile.External.Pinsker)
    {Ω : Type} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    {n : ℕ} (q : Fin n → Sandpile.Continuum.Space 2)
    (E : Set (Fin n → ℝ)) (hE : MeasurableSet E)
    (m L R Cn α₁ : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (hR : 1 ≤ R)
    (hCn : 0 ≤ Cn) (hNb : (n : ℝ) ≤ Cn * R ^ (2 - α₁))
    (h₀ : P₁.map (fun ω => (fun i : Fin n => X (q i) ω))
      = Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
    (h₁ : P₀.map (fun ω => (fun i : Fin n => X (q i) ω))
      = Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal (L / (m * R)) 1) :
    P₀ ((fun ω => (fun i : Fin n => X (q i) ω)) ⁻¹' E) ≤
      P₁ ((fun ω => (fun i : Fin n => X (q i) ω)) ⁻¹' E) +
        ENNReal.ofReal (Real.sqrt Cn / (2 * m) * L * R ^ (-(α₁ / 2))) :=
  hloss_ballField_of_laws hPin P₀ P₁ hX q E hE m L R Cn α₁ hm hL hR hCn hNb h₀ h₁

/-- The level loss of `prop:fixed-scale-crossings` for the ball field, from the
exploration data: the trace map on the finitely many coordinates the exploration
reads, the crossing event as its preimage, the two trace laws, and the
subquadratic count. -/
theorem hloss_ballField_of_exploration
    (hPin : Sandpile.External.Pinsker)
    {Ω : Type} [MeasurableSpace Ω] (P₀ P₁ : Measure Ω)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    {n : ℕ} (q : Fin n → Sandpile.Continuum.Space 2)
    (E : Set (Fin n → ℝ)) (hE : MeasurableSet E)
    (m θ L R Cn α₁ : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (hR : 1 ≤ R)
    (hCn : 0 ≤ Cn) (hNb : (n : ℝ) ≤ Cn * R ^ (2 - α₁))
    (h₀ : P₁.map (fun ω => (fun i : Fin n => X (q i) ω))
      = Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
    (h₁ : P₀.map (fun ω => (fun i : Fin n => X (q i) ω))
      = Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal (L / (m * R)) 1)
    (hcross : {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω}}
      = (fun ω => (fun i : Fin n => X (q i) ω)) ⁻¹' E) :
    P₀ {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω}} ≤
      P₁ {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω}} +
        ENNReal.ofReal (Real.sqrt Cn / (2 * m) * L * R ^ (-(α₁ / 2))) := by
  rw [hcross]
  exact Sandpile.Support.hloss_of_exploration_data hPin P₀ P₁ hX q E hE m L R Cn α₁ hm hL hR hCn hNb h₀ h₁

/-- The level loss of Steps 2-3 for the ball field, from the two shifted laws of
the exploration trace: `Q₀` is the law of the trace under the shift by `L/R` and
`Q₁` the law under the shift by `-ε`, the crossing probabilities at the two
levels are the probabilities of the one trace event under them, and the entropy
of the two trace laws is the chain-rule value `n (L/R + ε)²/(2𝔪²R²)`. -/
theorem hloss_ballField_of_shift_laws
    (hPin : Sandpile.External.Pinsker)
    {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    (P Q₀ Q₁ : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q₀]
    [IsProbabilityMeasure Q₁]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    {n : ℕ} (cubes : Fin n → Set (Space d)) (hmeas : ∀ i, MeasurableSet (cubes i))
    (hvol : ∀ i, volume (cubes i) = 1)
    (E : Set (Fin n → ℝ)) (hE : MeasurableSet E)
    (m θ L R Cn α₁ : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (hR : 1 ≤ R) (ε : ℝ) (hε : 0 < ε)
    (hCn : 0 ≤ Cn) (hNb : (n : ℝ) ≤ Cn * R ^ (2 - α₁))
    (hent : InformationTheory.klDiv
      (Q₀.map (fun ω => (fun i : Fin n =>
        W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω)))
      (Q₁.map (fun ω => (fun i : Fin n =>
        W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω)))
      = ENNReal.ofReal ((n : ℝ) * ((L / R + ε) ^ 2 / (2 * m ^ 2 * R ^ 2))))
    (h₀ : Q₀ ((fun ω => (fun i : Fin n =>
        W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω)) ⁻¹' E)
      = P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
          {u | L / R ≤ ballField d W 1 u ω}})
    (h₁ : Q₁ ((fun ω => (fun i : Fin n =>
        W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω)) ⁻¹' E)
      = P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
          {u | -ε ≤ ballField d W 1 u ω}}) :
    P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
        {u | -ε ≤ ballField d W 1 u ω}} ≤
      P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
          {u | L / R ≤ ballField d W 1 u ω}} +
        ENNReal.ofReal (Real.sqrt Cn / (2 * m) * (L / R + ε) * R ^ (-(α₁ / 2))) := by
  have htr : Measurable fun ω => (fun i : Fin n =>
      W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω) :=
    measurable_pi_iff.mpr fun i =>
      hW.meas _ (memLp_indicator_const 2 (hmeas i) (1 : ℝ) (Or.inr (by rw [hvol i]; exact ENNReal.one_ne_top)))
  have h := Sandpile.Support.hloss_of_trace hPin Q₁ Q₀ _ htr E hE n m (L / R + ε) R Cn α₁ hm
    (by positivity) hR hCn hNb hent
  rw [h₀, h₁] at h
  exact h

end Sandpile.Support
