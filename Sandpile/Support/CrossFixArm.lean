import Sandpile.Support.CrossArmDecay
import Sandpile.Support.CrossCircuit
import Sandpile.Support.CrossBallMemLp
import Sandpile.Support.CrossArmIndep
import Sandpile.Support.CrossBallMemLp

/-!
# The arm bound of Step 1 via independent blocking circuits

The arm bound of Step 1 of `prop:fixed-scale-crossings`
(`sandpile.tex:2229-2235`), in the form the blocking argument uses it.

  "This implies the arm bound by a routine argument: ... choosing a logarithmic
   number of such annuli separated by distance greater than the dependence range
   of `𝒳₁` makes these circuit events independent.  A `{𝒳₁ < 0}` arm from
   `B(x,r₁)` to `∂B(x,r₂)` must then avoid each selected circuit."

The quantitative content is `Sandpile.Support.arm_power_bound`
(`Sandpile/Support/CrossArmDecay.lean`), which turns "avoids `n` independent
events of probability at least `c`" into `(1-c)⁻¹ (r₁/r₂)^α`.  This module
states it in the shape the geometry of the annuli produces: the blocking events
are indexed by the scale, and the arm avoids the one at every scale whose
annulus fits inside the ball of radius `r₂`.
-/

open MeasureTheory Set

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- The arm bound of Step 1 of `prop:fixed-scale-crossings`
(`sandpile.tex:2229-2235`): an event that avoids a blocking event at every scale
that fits between `r₁` and `r₂` has probability at most
`(1 - c)⁻¹ (r₁ / r₂) ^ armExponent c κ`, the blocking events being independent
with probability at least `c`. -/
theorem arm_bound_of_blocking {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : ℕ → Set Ω) (hmeas : ∀ i, MeasurableSet (A i))
    (hind : ProbabilityTheory.iIndepSet A P) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hAc : ∀ i, ENNReal.ofReal c ≤ P (A i))
    (κ : ℝ) (hκ : 4 ≤ κ) (r₁ r₂ : ℝ) (hr₁ : 1 ≤ r₁) (hr : r₁ ≤ r₂)
    (S : Set Ω) (hS : ∀ i : ℕ, 4 * κ ^ i * r₁ ≤ r₂ → S ⊆ (A i)ᶜ) :
    P S ≤ ENNReal.ofReal ((1 - c)⁻¹ * (r₁ / r₂) ^ armExponent c κ) :=
  arm_power_bound P A hmeas hind c hc0 hc1 hAc κ hκ r₁ r₂ hr₁ hr S hS

/-- The circuit events of the annuli of separated scales are independent: the
regions are at distance more than the dependence range `2s`, and each circuit
event is read off the field over its own region. -/
theorem iIndepSet_circuit_of_separated {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : ℝ} (hs : 0 < s)
    (Reg : ℕ → Set (Sandpile.Continuum.Space 2))
    (hsep : ∀ i j, i ≠ j → ∀ u ∈ Reg i, ∀ v ∈ Reg j, 2 * s ≤ ‖u - v‖)
    (E : ℕ → Set Ω)
    (hE : ∀ i, MeasurableSet[MeasurableSpace.comap
      (fun ω (u : Reg i) => ballField d W s (u : Sandpile.Continuum.Space 2) ω) inferInstance]
      (E i)) :
    ProbabilityTheory.iIndepSet E P := by
  exact iIndepSet_ballField_of_separated hd hW hs Reg hsep E hE

/-- The exploration trace: the map that reads the field off the finitely many
coordinates the exploration evaluates.  It is measurable as soon as each
coordinate is. -/
theorem measurable_trace {Ω : Type} [MeasurableSpace Ω]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    (S : Finset (Sandpile.Continuum.Space 2)) :
    Measurable fun ω => (fun z : {z // z ∈ S} => X (z : Sandpile.Continuum.Space 2) ω) := by
  exact measurable_pi_iff.mpr fun z => hX z

/-- The arm bound of Step 1 of `prop:fixed-scale-crossings`
(`sandpile.tex:2229-2235`) for the ball field: the circuit events of the annuli
of the scales that fit between `r₁` and `r₂` are independent, each has
probability at least `c ^ 4` by FKG, and an arm that avoids them all has
probability at most `(1 - c ^ 4)⁻¹ (r₁ / r₂) ^ armExponent (c ^ 4) κ`. -/
theorem arm_bound_ballField {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (hPitt : Sandpile.External.PittGaussianFKG)
    {s : ℝ} (hs : 0 < s)
    (a b : ℕ → Fin 4 → Fin 2 → ℝ) (dir : ℕ → Fin 4 → Fin 2) (lev : ℕ → Fin 4 → ℝ)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hcA : ∀ i j, c ≤ P.real (crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j)))
    (hind : ProbabilityTheory.iIndepSet
      (fun i => ⋂ j, crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j)) P)
    (κ : ℝ) (hκ : 4 ≤ κ) (r₁ r₂ : ℝ) (hr₁ : 1 ≤ r₁) (hr : r₁ ≤ r₂)
    (S : Set Ω)
    (hS : ∀ i : ℕ, 4 * κ ^ i * r₁ ≤ r₂ →
      S ⊆ (⋂ j, crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j))ᶜ) :
    P S ≤ ENNReal.ofReal ((1 - c ^ 4)⁻¹ * (r₁ / r₂) ^ armExponent (c ^ 4) κ) := by
  have hmeas : ∀ i, MeasurableSet
      (⋂ j, crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j)) :=
    fun i => MeasurableSet.iInter fun j =>
      measurableSet_crossApprox (X := ballField d W s)
        (fun u => hW.meas _ (memLp_ballKernel hd hs u)) (a i j) (b i j) (dir i j) (lev i j)
  have hprob : ∀ i, ENNReal.ofReal (c ^ 4) ≤
      P (⋂ j, crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j)) := by
    intro i
    have h := circuit_probability (X := ballField d W s)
      (fun u => hW.meas _ (memLp_ballKernel hd hs u))
      (isAssociatedField_ballField_of_whiteNoise hPitt hd hW hs)
      (a i) (b i) (dir i) (lev i) hc.le (fun j => hcA i j)
    rw [measureReal_def] at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal h
  have hc4 : (0:ℝ) < c ^ 4 := by positivity
  have hc41 : c ^ 4 < 1 := pow_lt_one₀ hc.le hc1 (by norm_num)
  exact arm_bound_of_blocking P _ hmeas hind hc4 hc41 hprob κ hκ r₁ r₂ hr₁ hr S hS


/-- The arm bound `eq:fixed-scale-arm` in the `C (1+z₂)^{-α}` shape the
exploration's per-square estimate consumes, from `arm_bound_ballField` at
`r₁ = 1` and `r₂ = 1 + z₂`. -/
theorem arm_bound_pow {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (hPitt : Sandpile.External.PittGaussianFKG)
    {s : ℝ} (hs : 0 < s)
    (a b : ℕ → Fin 4 → Fin 2 → ℝ) (dir : ℕ → Fin 4 → Fin 2) (lev : ℕ → Fin 4 → ℝ)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hcA : ∀ i j, c ≤ P.real (crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j)))
    (hind : ProbabilityTheory.iIndepSet
      (fun i => ⋂ j, crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j)) P)
    (κ : ℝ) (hκ : 4 ≤ κ) (z₂ : ℝ) (hz : 0 ≤ z₂)
    (S : Set Ω)
    (hS : ∀ i : ℕ, 4 * κ ^ i * 1 ≤ 1 + z₂ →
      S ⊆ (⋂ j, crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j))ᶜ) :
    P S ≤ ENNReal.ofReal ((1 - c ^ 4)⁻¹ * (1 + z₂) ^ (-(armExponent (c ^ 4) κ))) := by
  have h := arm_bound_ballField hd hW hPitt hs a b dir lev hc hc1 hcA hind κ hκ 1 (1 + z₂)
    le_rfl (by linarith) S hS
  have hpos : (0:ℝ) < 1 + z₂ := by linarith
  have hconv : (1 / (1 + z₂)) ^ armExponent (c ^ 4) κ
      = (1 + z₂) ^ (-(armExponent (c ^ 4) κ)) := by
    rw [one_div, Real.inv_rpow (le_of_lt hpos), Real.rpow_neg (le_of_lt hpos)]
  rwa [hconv] at h

/-- The arm bound in the real-valued form the exploration's per-square estimate
uses: the probability of the arm event is at most `C (1+z₂)^{-α}`. -/
theorem arm_bound_real {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (hPitt : Sandpile.External.PittGaussianFKG)
    {s : ℝ} (hs : 0 < s)
    (a b : ℕ → Fin 4 → Fin 2 → ℝ) (dir : ℕ → Fin 4 → Fin 2) (lev : ℕ → Fin 4 → ℝ)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hcA : ∀ i j, c ≤ P.real (crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j)))
    (hind : ProbabilityTheory.iIndepSet
      (fun i => ⋂ j, crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j)) P)
    (κ : ℝ) (hκ : 4 ≤ κ) (z₂ : ℝ) (hz : 0 ≤ z₂)
    (S : Set Ω)
    (hS : ∀ i : ℕ, 4 * κ ^ i * 1 ≤ 1 + z₂ →
      S ⊆ (⋂ j, crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j))ᶜ) :
    P.real S ≤ (1 - c ^ 4)⁻¹ * (1 + z₂) ^ (-(armExponent (c ^ 4) κ)) := by
  have h := arm_bound_pow hd hW hPitt hs a b dir lev hc hc1 hcA hind κ hκ z₂ hz S hS
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal ?_ h
  have hc4 : c ^ 4 < 1 := pow_lt_one₀ (le_of_lt hc) hc1 (by norm_num)
  apply mul_nonneg
  · exact inv_nonneg.mpr (by linarith)
  · exact Real.rpow_nonneg (by linarith) _


/-- The circuit events of the annuli of separated scales are independent: the
regions are at distance more than the dependence range `2s`, and each circuit
event is read off the field over its own region. -/
theorem iIndepSet_circuit_annulus {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : ℝ} (hs : 0 < s)
    (Reg : ℕ → Set (Sandpile.Continuum.Space 2))
    (hsep : ∀ i j, i ≠ j → ∀ u ∈ Reg i, ∀ v ∈ Reg j, 2 * s ≤ ‖u - v‖)
    (E : ℕ → Set Ω)
    (hE : ∀ i, MeasurableSet[MeasurableSpace.comap
      (fun ω (u : Reg i) => ballField d W s (u : Sandpile.Continuum.Space 2) ω) inferInstance]
      (E i)) :
    ProbabilityTheory.iIndepSet E P := by
  exact Sandpile.Support.iIndepSet_circuit_of_separated hd hW hs Reg hsep E hE

/-- The arm bound of Step 1 for the ball field, from the circuit probability of
`circuit_probability` and the independence of the separated annuli. -/
theorem arm_bound_ballField_final2 {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (hPitt : Sandpile.External.PittGaussianFKG)
    {s : ℝ} (hs : 0 < s)
    (a b : ℕ → Fin 4 → Fin 2 → ℝ) (dir : ℕ → Fin 4 → Fin 2) (lev : ℕ → Fin 4 → ℝ)
    {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hcA : ∀ i j, c ≤ P.real (crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j)))
    (hind : ProbabilityTheory.iIndepSet
      (fun i => ⋂ j, crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j)) P)
    (κ : ℝ) (hκ : 4 ≤ κ) (r₁ r₂ : ℝ) (hr₁ : 1 ≤ r₁) (hr : r₁ ≤ r₂)
    (S : Set Ω)
    (hS : ∀ i : ℕ, 4 * κ ^ i * r₁ ≤ r₂ →
      S ⊆ (⋂ j, crossApprox (ballField d W s) (a i j) (b i j) (dir i j) (lev i j))ᶜ) :
    P S ≤ ENNReal.ofReal ((1 - c ^ 4)⁻¹ * (r₁ / r₂) ^ armExponent (c ^ 4) κ) := by
  exact Sandpile.Support.arm_bound_ballField hd hW hPitt hs a b dir lev hc hc1 hcA hind κ hκ r₁ r₂
    hr₁ hr S hS

end Sandpile.Support
