/-
The quantitative core of Step 1 of `prop:fixed-scale-crossings`
(`sandpile.tex:2213-2235`): geometric decay over separated scales is a power of
the ratio.

  "This implies the arm bound by a routine argument:
   `eq:fixed-scale-zero-crossing` and the FKG inequality give a uniformly
   positive probability of a `{𝒳₁ ≥ 0}` circuit in every annulus
   `B(x,4ρ) \ B(x,ρ)`; choosing a logarithmic number of such annuli separated by
   distance greater than the dependence range of `𝒳₁` makes these circuit events
   independent.  A `{𝒳₁ < 0}` arm from `B(x,r₁)` to `∂B(x,r₂)` must then avoid
   each selected circuit."

What the paper calls routine is the passage from "the arm avoids `n` independent
events of probability at least `c`" to the power bound `C (r₁/r₂)^α`, and that
passage is what this module proves, with nothing about the plane in it.  The
geometry -- which annuli are chosen, why a circuit blocks an arm, why the
circuit events of separated annuli are independent -- is not here; the
independence of the field over separated regions is
`Sandpile/Support/CrossArmIndep.lean`.

The exponent is `α = log(1-c)⁻¹ / log κ`, where `κ` is the ratio between
consecutive scales and `c` the uniform lower bound on the blocking probability,
and the constant is `(1-c)⁻¹`.  Both are explicit: the paper's `C` and `α` of
`eq:fixed-scale-arm` are these.  The scale split `exists_scale_split` is the
"logarithmic number of annuli": between `r₁` and `r₂` there are `N` scales
`4κ^i r₁ ≤ r₂`, and `r₂/r₁ ≤ κ^{N+1}`, which is what turns `(1-c)^N` into a
power of `r₁/r₂`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

/-- Geometric decay over `n` scales is a power of the ratio: if `q < 1` and the
number of scales is at least `log t / log κ - 1`, then `q^n` is at most
`q⁻¹ t^{-log q⁻¹ / log κ}`. -/
theorem geometric_to_power {q t : ℝ} (κ : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (ht : 1 ≤ t) (n : ℕ) (hn : Real.log t / Real.log κ - 1 ≤ (n : ℝ)) :
    q ^ n ≤ q⁻¹ * t ^ (-(Real.log q⁻¹ / Real.log κ)) := by
  have ht0 : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have h1 : q ^ ((n : ℕ) : ℝ) ≤ q ^ (Real.log t / Real.log κ - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hn
  rw [Real.rpow_natCast q n] at h1
  have h4 : q ^ (Real.log t / Real.log κ) = t ^ (-(Real.log q⁻¹ / Real.log κ)) := by
    rw [Real.rpow_def_of_pos hq0, Real.rpow_def_of_pos ht0, Real.log_inv]
    ring_nf
  have h3 : q ^ (Real.log t / Real.log κ - 1)
      = q ^ (Real.log t / Real.log κ) / q ^ (1:ℝ) := Real.rpow_sub hq0 _ _
  rw [Real.rpow_one, h4] at h3
  rw [h3, div_eq_inv_mul] at h1
  exact h1

/-- A power bound on the ratio bounds the logarithmic number of scales. -/
theorem log_le_of_pow {κ t : ℝ} (hκ : 1 < κ) (ht : 1 ≤ t) (n : ℕ) (htn : t ≤ κ ^ (n + 1)) :
    Real.log t / Real.log κ - 1 ≤ (n : ℝ) := by
  have hlogκ : 0 < Real.log κ := Real.log_pos hκ
  have ht0 : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have h1 : Real.log t ≤ Real.log (κ ^ (n + 1)) := Real.log_le_log ht0 htn
  rw [Real.log_pow] at h1
  rw [sub_le_iff_le_add, div_le_iff₀ hlogκ]
  push_cast at h1 ⊢
  linarith

/-- The scale split: between `1` and `t` there are `N` scales `4κ^i ≤ t`, and
`t ≤ κ^{N+1}`.  The factor `4` is the ratio between the inner and the outer
radius of one annulus, so that consecutive annuli are separated. -/
theorem exists_scale_split {κ t : ℝ} (hκ : 4 ≤ κ) (ht : 1 ≤ t) :
    ∃ N : ℕ, t ≤ κ ^ (N + 1) ∧ ∀ i, i < N → 4 * κ ^ i ≤ t := by
  have hκ1 : (1:ℝ) < κ := by linarith
  have hκ0 : (0:ℝ) < κ := by linarith
  by_cases h4 : (4:ℝ) ≤ t
  · obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := t / 4) (y := κ) (by linarith) hκ1
    have hpos : (0:ℝ) < κ ^ (n+1) := pow_pos hκ0 _
    refine ⟨n + 1, ?_, ?_⟩
    · have hlt : t < 4 * κ ^ (n + 1) := by
        have := (div_lt_iff₀ (by norm_num : (0:ℝ) < 4)).mp hn2
        linarith
      have hmul : (4:ℝ) * κ ^ (n+1) ≤ κ * κ ^ (n+1) := by nlinarith
      calc t ≤ κ * κ ^ (n + 1) := by linarith
        _ = κ ^ (n + 1 + 1) := by ring
    · intro i hi
      have hle : κ ^ i ≤ κ ^ n := pow_le_pow_right₀ (by linarith) (by omega)
      have h2 : (4:ℝ) * κ ^ n ≤ t := by
        have := (le_div_iff₀ (by norm_num : (0:ℝ) < 4)).mp hn1
        linarith
      nlinarith
  · refine ⟨0, ?_, ?_⟩
    · simp only [pow_one, zero_add]
      linarith
    · intro i hi
      omega

/-- Independent events, each of probability at least `c`, all fail with
probability at most `(1-c)^n`. -/
theorem measure_iInter_compl_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : ℕ → Set Ω) (hmeas : ∀ i, MeasurableSet (A i))
    (hA : ProbabilityTheory.iIndepSet A P) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hAc : ∀ i, ENNReal.ofReal c ≤ P (A i)) (n : ℕ) :
    P (⋂ i ∈ Finset.range n, (A i)ᶜ) ≤ ENNReal.ofReal ((1 - c) ^ n) := by
  have hprod : P (⋂ i ∈ Finset.range n, (A i)ᶜ) = ∏ i ∈ Finset.range n, P ((A i)ᶜ) := by
    refine (ProbabilityTheory.iIndepSet_iff A P).1 hA (Finset.range n)
      (f := fun i => (A i)ᶜ) ?_
    intro i _
    exact MeasurableSet.compl (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _))
  rw [hprod]
  have hstep : ∀ i ∈ Finset.range n, P ((A i)ᶜ) ≤ ENNReal.ofReal (1 - c) := by
    intro i _
    rw [MeasureTheory.prob_compl_eq_one_sub (hmeas i), ENNReal.ofReal_sub 1 hc0,
      ENNReal.ofReal_one]
    exact tsub_le_tsub_left (hAc i) 1
  calc ∏ i ∈ Finset.range n, P ((A i)ᶜ)
      ≤ ∏ _i ∈ Finset.range n, ENNReal.ofReal (1 - c) := Finset.prod_le_prod' hstep
    _ = ENNReal.ofReal (1 - c) ^ n := by simp
    _ = ENNReal.ofReal ((1 - c) ^ n) := (ENNReal.ofReal_pow (by linarith) n).symm

/-- The exponent of the arm bound `eq:fixed-scale-arm`, read off the blocking
probability `c` and the ratio `κ` between consecutive scales. -/
noncomputable def armExponent (c κ : ℝ) : ℝ := Real.log (1 - c)⁻¹ / Real.log κ

/-- The arm exponent is positive, which is what `eq:fixed-scale-arm` asserts. -/
theorem armExponent_pos {c κ : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hκ : 1 < κ) :
    0 < armExponent c κ := by
  have h1 : (1:ℝ) < (1 - c)⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) (by linarith)]
    linarith
  exact div_pos (Real.log_pos h1) (Real.log_pos hκ)

/-- The blocking bound: an event contained in the failure of `n` independent
events of probability at least `c` has probability at most
`(1-c)⁻¹ t^{-α}`, where `α` is the arm exponent and `t ≤ κ^{n+1}`. -/
theorem measure_le_of_blocking {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : ℕ → Set Ω) (hmeas : ∀ i, MeasurableSet (A i))
    (hA : ProbabilityTheory.iIndepSet A P) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hAc : ∀ i, ENNReal.ofReal c ≤ P (A i))
    (κ t : ℝ) (hκ : 1 < κ) (ht : 1 ≤ t) (n : ℕ) (htn : t ≤ κ ^ (n + 1))
    (S : Set Ω) (hS : S ⊆ ⋂ i ∈ Finset.range n, (A i)ᶜ) :
    P S ≤ ENNReal.ofReal ((1 - c)⁻¹ * t ^ (-(armExponent c κ))) := by
  have h2 := measure_iInter_compl_le P A hmeas hA c hc0.le hc1.le hAc n
  have h3 : (1 - c) ^ n ≤ (1 - c)⁻¹ * t ^ (-(armExponent c κ)) :=
    geometric_to_power κ (by linarith) (by linarith) ht n (log_le_of_pow hκ ht n htn)
  exact ((measure_mono hS).trans h2).trans (ENNReal.ofReal_le_ofReal h3)

/-- The arm bound `eq:fixed-scale-arm` in the form the paper states it: an event
that avoids a blocking event at every scale that fits between `r₁` and `r₂` has
probability at most `C (r₁/r₂)^α`, with `C = (1-c)⁻¹` and `α` the arm exponent.

The hypothesis `hS` is the geometry: at every scale `i` whose annulus fits
inside the ball of radius `r₂`, that is `4κ^i r₁ ≤ r₂`, the blocking event `A i`
excludes `S`.  Nothing else about the plane enters. -/
theorem arm_power_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : ℕ → Set Ω) (hmeas : ∀ i, MeasurableSet (A i))
    (hA : ProbabilityTheory.iIndepSet A P) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hAc : ∀ i, ENNReal.ofReal c ≤ P (A i))
    (κ : ℝ) (hκ : 4 ≤ κ) (r₁ r₂ : ℝ) (hr₁ : 1 ≤ r₁) (hr : r₁ ≤ r₂)
    (S : Set Ω) (hS : ∀ i : ℕ, 4 * κ ^ i * r₁ ≤ r₂ → S ⊆ (A i)ᶜ) :
    P S ≤ ENNReal.ofReal ((1 - c)⁻¹ * (r₁ / r₂) ^ armExponent c κ) := by
  have hr₁0 : (0:ℝ) < r₁ := lt_of_lt_of_le zero_lt_one hr₁
  have hr₂0 : (0:ℝ) < r₂ := lt_of_lt_of_le hr₁0 hr
  have ht1 : (1:ℝ) ≤ r₂ / r₁ := (one_le_div hr₁0).2 hr
  have ht0 : (0:ℝ) < r₂ / r₁ := lt_of_lt_of_le zero_lt_one ht1
  obtain ⟨n, htn, hfit⟩ := exists_scale_split hκ ht1
  have hsub : S ⊆ ⋂ i ∈ Finset.range n, (A i)ᶜ := by
    refine Set.subset_iInter₂ fun i hi => hS i ?_
    have hi' := hfit i (Finset.mem_range.1 hi)
    rw [le_div_iff₀ hr₁0] at hi'
    linarith
  have hmain := measure_le_of_blocking P A hmeas hA c hc0 hc1 hAc κ (r₂ / r₁)
    (by linarith) ht1 n htn S hsub
  have hconv : (r₂ / r₁) ^ (-(armExponent c κ)) = (r₁ / r₂) ^ armExponent c κ := by
    rw [Real.rpow_neg (le_of_lt ht0), ← Real.inv_rpow (le_of_lt ht0), inv_div]
  rwa [hconv] at hmain

end Sandpile.Support
