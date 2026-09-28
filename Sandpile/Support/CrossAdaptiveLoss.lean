import Sandpile.Support.CrossStoppingSet
import Sandpile.External.Pinsker

/-!
# Pinsker bound for the adaptive Cameron-Martin tilt

Step 3 of `prop:fixed-scale-crossings` (`sandpile.tex:2334-2400`) with the exploration
abstracted away: Pinsker's inequality applied to the adaptive Cameron-Martin tilt of
`Sandpile/Support/CrossStoppingSet.lean`. The paper's display `sandpile.tex:2392-2398`,
`P_{L/R}(E_R(θ)) - P_0(E_R(θ)) ≤ (L/(2𝔪R))√(𝔼_0 𝒩)`, is exactly `tilted_cm_level_loss` below
with `a = L/(𝔪R)` and `N` a bound for the expected number `𝔼_0 𝒩` of revealed coordinates: the
left-hand side is the difference of the probabilities of the same event under the fully
shifted law and under the unshifted law, and the right-hand side is `|a|/2` times `√N`. What
the crossing proof still has to supply is the exploration itself: a stopping set for the
cubes, decided by the coordinates it reveals, whose expected size is `O(R^{2-α₁})`, and the
identification of the fully tilted measure with the law of the shifted white noise.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

variable {Ω ι : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The paper's Step 3, in the abstract: on an event the exploration decides, the fully
shifted law exceeds the unshifted law by at most `|a|/2` times the square root of a bound
for the expected number of revealed coordinates. -/
theorem tilted_cm_level_loss (hPin : Sandpile.External.Pinsker)
    [IsProbabilityMeasure P] [Fintype ι] [DecidableEq ι]
    {G : ι → MeasurableSpace Ω} (hGle : ∀ i, G i ≤ mΩ) (hGindep : iIndep G P)
    {S : Ω → Finset ι} (hS : IsIndepStoppingSet G S)
    (ξ : ι → Ω → ℝ) (hξm : ∀ i, Measurable[G i] (ξ i)) (hξi : ∀ i, Integrable (ξ i) P)
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0) (a : ℝ)
    (hfi : ∀ i, Integrable (cmFactor a ξ i) P)
    (hf1 : ∀ i, ∫ ω, cmFactor a ξ i ω ∂P = 1)
    (N : ℝ) (hN : ∫ ω, ((S ω).card : ℝ) ∂P ≤ N)
    {E : Set Ω} (hE : IndepBlockDecides G S E) :
    (P.tilted (cmLogDensity a ξ (fun _ : Ω => (Finset.univ : Finset ι)))).real E - P.real E
      ≤ |a| / 2 * Real.sqrt N := by
  classical
  have hN0 : (0 : ℝ) ≤ N := by
    refine le_trans ?_ hN
    exact integral_nonneg fun ω => by positivity
  have hexpint : Integrable (fun ω => Real.exp (cmLogDensity a ξ S ω)) P :=
    integrable_exp_cmLogDensity hGle hGindep hS ξ hξm a hfi hf1
  haveI : IsProbabilityMeasure (P.tilted (cmLogDensity a ξ S)) :=
    isProbabilityMeasure_tilted hexpint
  have hEmeas : MeasurableSet E := measurableSet_of_indepBlockDecides hGle hE
  have hkl := klDiv_tilted_cm_le hGle hGindep hS ξ hξm hξi hξ0 a hfi hf1 N hN
  have hδ : (0 : ℝ) ≤ a ^ 2 / 2 * N := by positivity
  have hP := hPin Ω P (P.tilted (cmLogDensity a ξ S)) E hEmeas (a ^ 2 / 2 * N) hδ hkl
  have hsq : Real.sqrt (a ^ 2 / 2 * N / 2) = |a| / 2 * Real.sqrt N := by
    have hrw : a ^ 2 / 2 * N / 2 = (|a| / 2) ^ 2 * N := by
      rw [div_pow, sq_abs]
      ring
    rw [hrw, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsq] at hP
  have hmeq : (P.tilted (cmLogDensity a ξ S)).real E
      = (P.tilted (cmLogDensity a ξ (fun _ : Ω => (Finset.univ : Finset ι)))).real E := by
    rw [measureReal_def, measureReal_def,
      tilted_cm_apply_eq_of_decided hGle hGindep hS ξ hξm a hfi hf1 hE]
  rw [← hmeq]
  calc (P.tilted (cmLogDensity a ξ S)).real E - P.real E
      = -(P.real E - (P.tilted (cmLogDensity a ξ S)).real E) := by ring
    _ ≤ |P.real E - (P.tilted (cmLogDensity a ξ S)).real E| := neg_le_abs _
    _ ≤ |a| / 2 * Real.sqrt N := hP

/-- The same bound between the two measures, for use where the crossing event's probability
is written as an outer measure. -/
theorem tilted_cm_measure_le (hPin : Sandpile.External.Pinsker)
    [IsProbabilityMeasure P] [Fintype ι] [DecidableEq ι]
    {G : ι → MeasurableSpace Ω} (hGle : ∀ i, G i ≤ mΩ) (hGindep : iIndep G P)
    {S : Ω → Finset ι} (hS : IsIndepStoppingSet G S)
    (ξ : ι → Ω → ℝ) (hξm : ∀ i, Measurable[G i] (ξ i)) (hξi : ∀ i, Integrable (ξ i) P)
    (hξ0 : ∀ i, ∫ ω, ξ i ω ∂P = 0) (a : ℝ)
    (hfi : ∀ i, Integrable (cmFactor a ξ i) P)
    (hf1 : ∀ i, ∫ ω, cmFactor a ξ i ω ∂P = 1)
    (N : ℝ) (hN : ∫ ω, ((S ω).card : ℝ) ∂P ≤ N)
    {E : Set Ω} (hE : IndepBlockDecides G S E) :
    (P.tilted (cmLogDensity a ξ (fun _ : Ω => (Finset.univ : Finset ι)))) E
      ≤ P E + ENNReal.ofReal (|a| / 2 * Real.sqrt N) := by
  classical
  have hexpint : Integrable (fun ω => Real.exp (cmLogDensity a ξ S ω)) P :=
    integrable_exp_cmLogDensity hGle hGindep hS ξ hξm a hfi hf1
  haveI : IsProbabilityMeasure (P.tilted (cmLogDensity a ξ S)) :=
    isProbabilityMeasure_tilted hexpint
  haveI : IsProbabilityMeasure
      (P.tilted (cmLogDensity a ξ (fun _ : Ω => (Finset.univ : Finset ι)))) :=
    isProbabilityMeasure_tilted
      (integrable_exp_cmLogDensity hGle hGindep (isIndepStoppingSet_univ G) ξ hξm a hfi hf1)
  set Q := P.tilted (cmLogDensity a ξ (fun _ : Ω => (Finset.univ : Finset ι))) with hQ
  have hreal := tilted_cm_level_loss hPin hGle hGindep hS ξ hξm hξi hξ0 a hfi hf1 N hN hE
  have hc : (0 : ℝ) ≤ |a| / 2 * Real.sqrt N := by positivity
  have h1 : Q.real E ≤ P.real E + |a| / 2 * Real.sqrt N := by linarith
  have h2 : ENNReal.ofReal (Q.real E)
      ≤ ENNReal.ofReal (P.real E + |a| / 2 * Real.sqrt N) := ENNReal.ofReal_le_ofReal h1
  rw [ENNReal.ofReal_add measureReal_nonneg hc] at h2
  rwa [measureReal_def, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top Q E),
    ENNReal.ofReal_toReal (measure_ne_top P E)] at h2

end Sandpile.Support
