import Mathlib
import Sandpile.Law
import Sandpile.External.VarianceScale
import Sandpile.External.HeatKernelBounds
import Sandpile.Support.SceneryBridge
import Sandpile.Support.MeanLocalization
import Sandpile.Frozen.MeanLocalization

/-!
# Critical-Level Block Assembly

Assembly lemmas for the `d = 4` critical-level percolation theorem
(`sandpile.tex:3952-3968`). These are the deterministic arithmetic steps of the
block argument: the step-3 implication, the final scale conversion, the union
bound over the block set, and the LSS deficit arithmetic. The file culminates in
`uniform_localized_mean_lower`, which chains the mean, localization, and
exit-tail bounds into a uniform localized mean lower bound. All results here are
local support lemmas; none of the underlying probabilistic estimates are proved
from scratch.
-/

open MeasureTheory

namespace Sandpile

/-- Step-3 deterministic implication of the d4 critical-level proof: on the
intersection of the future-height and ball-replacement events, a low ball field
forces the block field above `b₀ log r / 2`. -/
theorem step3_implication
    (K : Set (Fin 2 → ℤ)) (B BN Y : (Fin 2 → ℤ) → ℝ) (b₀ r : ℝ)
    (_hb : 0 < b₀) (hr : 1 ≤ r)
    (hY : ∀ z ∈ K, b₀ * Real.log r ≤ Y z)
    (hBN : ∀ z ∈ K, |B z - BN z| ≤ b₀ * Real.log r / 4)
    (hB : ∀ z ∈ K, -(b₀ / 4) * Real.log r < B z) :
    ∀ z ∈ K, b₀ * Real.log r / 2 < BN z + Y z := by
  intro z hz
  have h1 := hY z hz
  have h2 := hBN z hz
  have h3 := hB z hz
  have h4 : B z - b₀ * Real.log r / 4 ≤ BN z := by
    have := (abs_le.mp h2).2
    linarith
  have h3' : -(b₀ * Real.log r) / 4 < B z := by ring_nf at h3 ⊢; exact h3
  have h5 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  linear_combination h3' + h1 + h4

/-- Final scale conversion of the d4 critical-level proof: if the odometer at
the block horizon exceeds `b₀ log r / 2` on a set, the odometer at time `t`
exceeds `c log t` there, given the horizon is at most `t`, `log t ≤ 4 log r`,
and `c ≤ b₀ / 8`. -/
theorem final_scale_conversion
    (K : Set (Fin 2 → ℤ)) (u : ℕ → (Fin 2 → ℤ) → ℝ)
    (b₀ c : ℝ) (hb : 0 < b₀) (_hc : 0 < c) (hcb : c ≤ b₀ / 8)
    (t s r : ℕ) (ht : 2 ≤ t) (hs : s ≤ t) (hr : 1 ≤ r)
    (hmono : ∀ n m : ℕ, n ≤ m → ∀ z, u n z ≤ u m z)
    (hlog : Real.log t ≤ 4 * Real.log r)
    (hK : ∀ z ∈ K, b₀ * Real.log r / 2 < u s z) :
    ∀ z ∈ K, c * Real.log t < u t z := by
  intro z hz
  have h1 := hK z hz
  have h2 := hmono s t hs z
  have h3 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  have h4 : 0 < Real.log t := Real.log_pos (by exact_mod_cast ht)
  have h5 : c * Real.log t ≤ b₀ * Real.log t / 8 := by
    have h7 : c * Real.log t ≤ (b₀ / 8) * Real.log t := by nlinarith
    have h8 : (b₀ / 8) * Real.log t = b₀ * Real.log t / 8 := by ring
    linarith [h7, h8]
  have h6 : b₀ * Real.log t / 8 ≤ b₀ * Real.log r / 2 := by
    have h9 : Real.log t ≤ 4 * Real.log r := hlog
    have h10 : 0 ≤ Real.log r := h3
    have h11 : b₀ * Real.log t / 8 ≤ b₀ * (4 * Real.log r) / 8 := by
      have h12 : b₀ * Real.log t ≤ b₀ * (4 * Real.log r) := by nlinarith
      have h13 : b₀ * (4 * Real.log r) / 8 = b₀ * Real.log r / 2 := by ring
      nlinarith [h12]
    have h14 : b₀ * (4 * Real.log r) / 8 = b₀ * Real.log r / 2 := by ring
    rw [h14] at h11
    exact h11
  have h15 : b₀ * Real.log r / 2 < u t z := by
    have h16 : b₀ * Real.log r / 2 < u s z := h1
    have h17 : u s z ≤ u t z := h2
    linarith
  have h18 : c * Real.log t ≤ b₀ * Real.log r / 2 := le_trans h5 h6
  linarith

/-- Union bound over the block set: the probability that the future-height
event fails somewhere in the finite block index set is at most the cardinality
times the uniform one-site failure bound. -/
theorem union_bound_blocks
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (K : Finset (Fin 2 → ℤ))
    (Y : (Fin 2 → ℤ) → Ω → ℝ) (b₀ r : ℝ) (δ : ENNReal)
    (hP : ∀ z ∈ K, μ {ω | Y z ω < b₀ * Real.log r} ≤ δ) :
    μ {ω | ∃ z ∈ K, Y z ω < b₀ * Real.log r} ≤ K.card * δ := by
  have hset : {ω | ∃ z ∈ K, Y z ω < b₀ * Real.log r} = ⋃ z ∈ K, {ω | Y z ω < b₀ * Real.log r} := by
    ext ω
    simp
  rw [hset]
  have h1 : μ (⋃ z ∈ K, {ω | Y z ω < b₀ * Real.log r}) ≤
      ∑ z ∈ K, μ {ω | Y z ω < b₀ * Real.log r} :=
    measure_biUnion_finset_le K _
  have h2 : ∑ z ∈ K, μ {ω | Y z ω < b₀ * Real.log r} ≤ ∑ z ∈ K, δ :=
    Finset.sum_le_sum (fun z hz => hP z hz)
  have h3 : ∑ z ∈ K, δ = K.card * δ := by simp [Finset.sum_const]
  refine le_trans h1 ?_
  rw [← h3]
  exact h2

/-- Deficit arithmetic for the LSS application: a per-block success
probability of at least `1 - C r⁻²` exceeds the LSS deficit `1 - δ` once
`r² ≥ C δ⁻¹`. -/
theorem deficit_arithmetic
    (C δ : ℝ) (r : ℕ) (_hC : 0 < C) (hδ : 0 < δ) (hr : 1 ≤ r)
    (hbig : C / δ ≤ (r : ℝ) ^ 2) :
    1 - δ ≤ 1 - C / (r : ℝ) ^ 2 := by
  have h1 : 0 < (r : ℝ) ^ 2 := by
    have h1a : 0 < (r : ℝ) := by exact_mod_cast hr
    positivity
  have h2 : C ≤ δ * (r : ℝ) ^ 2 := by linarith [(mul_inv_le_iff₀ hδ).mp hbig]
  have h3 : C / (r : ℝ) ^ 2 ≤ δ :=
    (mul_inv_le_iff₀ h1).mpr h2
  linarith

/-- Exponential arithmetic for the block estimates: if the concentration
exponent dominates `2 log r`, the bound `C exp(-c min(s², s r²))` is at most
`C r⁻²`. -/
theorem concentration_to_rsq
    (C c b₀ : ℝ) (r : ℕ) (hC : 0 < C) (hr : 2 ≤ r)
    (hexp : 2 * Real.log r ≤ c * min ((b₀ * Real.log r) ^ 2) (b₀ * Real.log r * (r : ℝ) ^ 2)) :
    C * Real.exp (-(c * min ((b₀ * Real.log r) ^ 2) (b₀ * Real.log r * (r : ℝ) ^ 2))) ≤
      C / (r : ℝ) ^ 2 := by
  have hL : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr)
  have h1 : Real.exp (-(c * min ((b₀ * Real.log r) ^ 2) (b₀ * Real.log r * (r : ℝ) ^ 2))) ≤
      Real.exp (-(2 * Real.log r)) :=
    Real.exp_le_exp.mpr (by nlinarith [hexp])
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hr)
  have h2 : Real.exp (-(2 * Real.log r)) = 1 / (r : ℝ) ^ 2 := by
    have h3 : Real.exp (-(2 * Real.log r)) = Real.exp (Real.log r * (-(2:ℝ))) := by congr 1; ring
    rw [h3, Real.exp_mul, Real.exp_log hr0]
    rw [Real.rpow_neg (le_of_lt hr0)]
    norm_num
  rw [h2] at h1
  have h5 : C * (1 / (r : ℝ) ^ 2) = C / (r : ℝ) ^ 2 := by ring
  calc C * Real.exp (-(c * min ((b₀ * Real.log r) ^ 2) (b₀ * Real.log r * (r : ℝ) ^ 2)))
      ≤ C * (1 / (r : ℝ) ^ 2) := by nlinarith [h1, hC]
    _ = C / (r : ℝ) ^ 2 := h5

/-- Step-1 arithmetic of the d4 critical-level proof: if the mean odometer at
time `r²` is at least `c₀ log r`, the localization deficit and the exit-tail
deficit are each at most a quarter of `c₀ log r`, then the exit value
expectation is at least `2 b₀ log r` with `b₀ = c₀ / 8`. -/
theorem exit_value_expectation_arith
    (c₀ b₀ r : ℝ) (EY : ℝ)
    (hr : 2 ≤ r) (hc₀ : 0 < c₀)
    (hb : b₀ = c₀ / 8)
    (hmean : c₀ * Real.log r ≤ EY + c₀ * Real.log r / 4 + c₀ * Real.log r / 4) :
    2 * b₀ * Real.log r ≤ EY := by
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  have hA : 0 ≤ c₀ * Real.log r := mul_nonneg (le_of_lt hc₀) hlog
  subst hb
  linarith


/-- Localization-deficit arithmetic: a nonnegative deficit bounded by
`C e^{-c A²} M` with `M ≤ K log r` and `C K e^{-c A²} ≤ c₀/4` is at most
`c₀ log r / 4`. -/
theorem localization_deficit_arith
    (C c A M K c₀ r D : ℝ)
    (hC : 0 ≤ C) (_hD0 : 0 ≤ D) (hD : D ≤ C * Real.exp (-(c * A ^ 2)) * M)
    (hM : M ≤ K * Real.log r) (hr : 2 ≤ r)
    (hK : C * K * Real.exp (-(c * A ^ 2)) ≤ c₀ / 4) :
    D ≤ c₀ * Real.log r / 4 := by
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  have h1 : C * Real.exp (-(c * A ^ 2)) * M ≤ C * Real.exp (-(c * A ^ 2)) * (K * Real.log r) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have h2 : C * Real.exp (-(c * A ^ 2)) * (K * Real.log r)
      = (C * K * Real.exp (-(c * A ^ 2))) * Real.log r := by ring
  have h3 : (C * K * Real.exp (-(c * A ^ 2))) * Real.log r ≤ (c₀ / 4) * Real.log r :=
    mul_le_mul_of_nonneg_right hK hlog
  have h4 : (c₀ / 4) * Real.log r = c₀ * Real.log r / 4 := by ring
  linarith


/-- Localization lower-bound arithmetic of Step 1a: if the mean odometer is at
least `c₀ log t` and the localization deficit is at most half of it, the
localized mean is at least `c₀ log t / 2`. -/
theorem localized_mean_lower_arith
    (c₀ t Mloc D : ℝ) (_ht : 2 ≤ t) (_hc₀ : 0 < c₀)
    (hmean : c₀ * Real.log t ≤ Mloc + D) (hD : D ≤ c₀ * Real.log t / 2) :
    c₀ * Real.log t / 2 ≤ Mloc := by
  linarith


/-- Exit-tail deficit arithmetic of Step 1a: a deficit bounded by the exit
probability `p ≤ C / Aex^2` times a payoff bound `M` is at most `c₀ log r / 4`
once `C * M / Aex^2 ≤ c₀ log r / 4`. -/
theorem exit_deficit_arith
    (C M Aex c₀ r D : ℝ) (_hAex : 0 < Aex)
    (hD : D ≤ (C / Aex ^ 2) * M) (hK : C * M / Aex ^ 2 ≤ c₀ * Real.log r / 4) :
    D ≤ c₀ * Real.log r / 4 := by
  have h1 : (C / Aex ^ 2) * M = C * M / Aex ^ 2 := by ring
  linarith

/-- Full Step-1a assembly: given matching log-scale bounds on the mean odometer and a
uniform localization estimate with sufficiently large exponent `Aloc`, the localized
mean odometer over the box `supBox w (Aloc * r)` at time `r²` is at least
`c₀ log(r²) / 2`. This chains `meanOdometer_centeredMassLaw_eq`,
`localization_deficit_arith`, and `localized_mean_lower_arith`. -/
theorem uniform_localized_mean_lower
    (_hVS : Sandpile.External.VarianceScale)
    (_hHK : Sandpile.External.HeatKernelBounds)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (_hmean : ∫ z, z ∂ν = 0)
    (_hpos : Integrable (fun z => max z 0) ν)
    (c₀ C₀ c₁ C₁ Aloc : ℝ) (r : ℕ) (hc₀ : 0 < c₀) (_hC₀ : 0 < C₀) (_hc₁ : 0 < c₁) (hC₁ : 0 < C₁)
    (hAloc : 1 ≤ Aloc) (hr : 2 ≤ r)
    (hlow : ∀ t : ℕ, 2 ≤ t → c₀ * Real.log t ≤
        Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t)
    (hup : ∀ t : ℕ, 2 ≤ t →
        Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t ≤ C₀ * Real.log t)
    (hloc : ∀ A : ℝ, 1 ≤ A → ∀ R : ℝ, 1 ≤ R → ∀ t : ℕ, (t : ℝ) ≤ 1 * R ^ 2 →
        ∀ x : Sandpile.Site 4,
          0 ≤ (∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν)) -
                ∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox x (A * R)) ζ t x
                  ∂(LatticeProb.iidLaw 4 ν) ∧
            (∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν)) -
                (∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox x (A * R)) ζ t x
                  ∂(LatticeProb.iidLaw 4 ν)) ≤
              C₁ * Real.exp (-(c₁ * A ^ 2 / 1)) *
                ∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν))
    (hsmall : C₀ * C₁ * Real.exp (-(c₁ * Aloc ^ 2)) ≤ c₀ / 4) :
    ∀ w : Sandpile.Site 4,
      c₀ * Real.log ((r : ℕ) ^ 2) / 2 ≤
        ∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox w (Aloc * (r : ℝ))) ζ (r ^ 2) w
          ∂(LatticeProb.iidLaw 4 ν) := by
  intro w
  have h4 : (1 : ℕ) ≤ 4 := by omega
  have htrans : Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) (r ^ 2)
      = ∫ ζ, Sandpile.odometerOf ζ (r ^ 2) 0 ∂(LatticeProb.iidLaw 4 ν) :=
    meanOdometer_centeredMassLaw_eq 4 ν h4 (r ^ 2)
  have hr2 : 2 ≤ r ^ 2 := by nlinarith
  have hlow' := hlow (r ^ 2) hr2
  rw [htrans] at hlow'
  have hup' := hup (r ^ 2) hr2
  rw [htrans] at hup'
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have htR : ((r ^ 2 : ℕ) : ℝ) ≤ 1 * (r : ℝ) ^ 2 := by
    have : ((r ^ 2 : ℕ) : ℝ) = (r : ℝ) * (r : ℝ) := by push_cast; ring
    rw [this]
    nlinarith [hr]
  have hD := hloc Aloc hAloc (r : ℝ) hrR (r ^ 2) htR w
  set Mloc := ∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox w (Aloc * (r : ℝ))) ζ (r ^ 2) w
    ∂(LatticeProb.iidLaw 4 ν) with hMloc
  set Mu := ∫ ζ, Sandpile.odometerOf ζ (r ^ 2) 0 ∂(LatticeProb.iidLaw 4 ν) with hMu
  have hdef : Mu - Mloc ≤ C₁ * Real.exp (-(c₁ * Aloc ^ 2)) * Mu := by
    have := hD.2
    simp only [div_one] at this
    exact this
  have hdef' : Mu - Mloc ≤ C₁ * Real.exp (-(c₁ * Aloc ^ 2 / 1)) * Mu := by
    simpa using hdef
  have hsmall' : C₁ * C₀ * Real.exp (-(c₁ * Aloc ^ 2)) ≤ c₀ / 4 := by
    nlinarith [hsmall]
  have hK := localization_deficit_arith C₁ c₁ Aloc Mu C₀ c₀ ((r ^ 2 : ℕ) : ℝ)
    (Mu - Mloc) (le_of_lt hC₁) hD.1 hdef hup' (by exact_mod_cast hr2) hsmall'
  have hlog : 0 ≤ Real.log ((r ^ 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r ^ 2))
  have hmean2 : c₀ * Real.log ((r ^ 2 : ℕ) : ℝ) ≤ Mloc + (Mu - Mloc) := by
    have : Mloc + (Mu - Mloc) = Mu := by ring
    linarith
  have := localized_mean_lower_arith c₀ ((r ^ 2 : ℕ) : ℝ) Mloc (Mu - Mloc)
    (by exact_mod_cast hr2) hc₀ hmean2 (hK.trans (by linarith))
  have hcast : ((r ^ 2 : ℕ) : ℝ) = (r : ℝ) ^ 2 := by push_cast; ring
  calc c₀ * Real.log ((r : ℕ) ^ 2) / 2 ≤ Mloc := by
        have h2 : c₀ * Real.log ((r ^ 2 : ℕ) : ℝ) / 2 ≤ Mloc := this
        rw [hcast] at h2
        exact h2
    _ = ∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox w (Aloc * (r : ℝ))) ζ (r ^ 2) w
          ∂(LatticeProb.iidLaw 4 ν) := rfl

/-- Final Step-1a arithmetic: with `b₀ = c₀/16`, the half-localized mean
`c₀ log t / 4` at `t = r²` dominates `2 b₀ log r` since `log r² = 2 log r`. -/
theorem exit_value_final_arith (c₀ b₀ EY : ℝ) (r t : ℕ) (hr : 2 ≤ r) (hc₀ : 0 < c₀)
    (hb : b₀ = c₀ / 16) (ht : t = r ^ 2)
    (hEY : c₀ * Real.log t / 4 ≤ EY) : 2 * b₀ * Real.log r ≤ EY := by
  have hlog : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have h2 : Real.log (t : ℝ) = 2 * Real.log (r : ℝ) := by
    rw [ht]
    push_cast
    rw [Real.log_pow]
    norm_num
  subst hb
  rw [h2] at hEY
  nlinarith [mul_nonneg (le_of_lt hc₀) hlog]

/-- Exit-tail smallness: the d=4 exit tail `C / A_ex^2` is at most `1/2` once
`A_ex ≥ 2` and `C ≤ 2`. -/
theorem exit_tail_small (C Aex : ℝ) (_hC : 0 ≤ C) (hC2 : C ≤ 2) (hAex : 2 ≤ Aex) :
    C / Aex ^ 2 ≤ 1 / 2 := by
  have h4 : (4:ℝ) ≤ Aex ^ 2 := by nlinarith
  have e1 : C / Aex ^ 2 ≤ 2 / Aex ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have e2 : (2:ℝ) / Aex ^ 2 ≤ 2 / 4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h4
  have e3 : (2:ℝ) / 4 = 1 / 2 := by norm_num
  rw [e3] at e2
  linarith


/-- Good-event mean lower bound: if the exit value `EY` is bounded below by
`(1 - p) · m` with tail `p ≤ 1/2`, then `m / 2 ≤ EY`. -/
theorem good_event_mean_lower (p m EY : ℝ) (hp : p ≤ 1 / 2) (hm : 0 ≤ m)
    (hEY : (1 - p) * m ≤ EY) : m / 2 ≤ EY :=
  calc m / 2 = (1 - 1/2) * m := by ring
    _ ≤ (1 - p) * m := mul_le_mul_of_nonneg_right (by linarith) hm
    _ ≤ EY := hEY

/-- Step-1a final assembly arithmetic: an exit value bounded below by
`(1 - p) · c₀ log r² / 2` with tail `p ≤ 1/2` dominates `2 b₀ log r`
when `b₀ = c₀ / 16`, since `log r² = 2 log r`. -/
theorem exit_value_tail_arith (c₀ b₀ p EY : ℝ) (r : ℕ) (hr : 2 ≤ r) (hc₀ : 0 < c₀)
    (hb : b₀ = c₀ / 16) (hp : p ≤ 1 / 2)
    (hEY : (1 - p) * (c₀ * Real.log ((r : ℕ) ^ 2) / 2) ≤ EY) :
    2 * b₀ * Real.log r ≤ EY := by
  have hlog : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have h2 : Real.log (((r : ℕ) ^ 2 : ℝ)) = 2 * Real.log (r : ℝ) := by
    rw [Real.log_pow]
    norm_num
  subst hb
  rw [h2] at hEY
  have hkey : 2 * (c₀ / 16) * Real.log r ≤ (1 - p) * (c₀ * (2 * Real.log r) / 2) := by
    have hhalf : (1 - 1/2) * (c₀ * (2 * Real.log r) / 2) ≤
        (1 - p) * (c₀ * (2 * Real.log r) / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hsimp : (1 - 1/2) * (c₀ * (2 * Real.log r) / 2) = c₀ * Real.log r / 2 := by
      field_simp
      ring
    rw [hsimp] at hhalf
    have hlhs : 2 * (c₀ / 16) * Real.log r = c₀ * Real.log r / 8 := by
      field_simp
      ring
    rw [hlhs]
    linarith [mul_nonneg (le_of_lt hc₀) hlog]
  exact hkey.trans hEY

end Sandpile
