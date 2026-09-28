import Sandpile.Support.D4SMarkov
import Sandpile.Support.D4SNegSobolev
import Sandpile.Support.D4STight

/-!
# Tightness on the small-scale range

The small-scale half of the tightness clause of `prop:d4-superdiffusive-limit`
(`sandpile.tex:3324-3327`).

Steps 2 and 3 of the paper's proof make the two error terms small only as `R\to\infty`, while
the tightness clause quantifies over every `R\geq1`. Below any fixed threshold the whole
centred odometer field is bounded crudely: the time `\lfloor R^\alpha\rfloor` is at most
`\lfloor R_0^\alpha\rfloor`, the mesh meets at most the box of radius `\lceil R_0L\rceil+1`,
and `R^{-4}\leq1`, so the uniform second moment of the centred odometer over that range of
times bounds the expectation of the mesh sum, and Markov's inequality
(`measure_gt_le_of_sqrt_bound`) turns that into a single level `M` above which the `H^{-s}(D)`
norm is unlikely (`exists_tight_bound_small`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- A Markov-type tail bound: if `N ω ≤ K * √(Y ω)` pointwise for a nonnegative integrable
`Y` with `K ^ 2 * ∫ Y ≤ B`, then `P {N > M} ≤ B / M ^ 2`. Squares the pointwise domination to
reduce to `mul_meas_ge_le_integral_of_nonneg` (Markov's inequality) applied to `K ^ 2 * Y`. -/
theorem measure_gt_le_of_sqrt_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (N : Ω → ℝ≥0∞) (Y : Ω → ℝ) (K B M : ℝ)
    (hK : 0 ≤ K) (hM : 0 < M)
    (hnn : ∀ ω : Ω, 0 ≤ Y ω) (hint : Integrable Y P)
    (hdom : ∀ ω : Ω, N ω ≤ ENNReal.ofReal (K * Real.sqrt (Y ω)))
    (hB : K ^ 2 * ∫ ω, Y ω ∂P ≤ B) :
    P {ω | ENNReal.ofReal M < N ω} ≤ ENNReal.ofReal (B / M ^ 2) := by
  have hM2 : (0:ℝ) < M ^ 2 := by positivity
  have hsub : {ω : Ω | ENNReal.ofReal M < N ω} ⊆ {ω : Ω | M ^ 2 ≤ K ^ 2 * Y ω} := by
    intro ω hω
    have h1 : ENNReal.ofReal M < ENNReal.ofReal (K * Real.sqrt (Y ω)) :=
      lt_of_lt_of_le hω (hdom ω)
    have h2 : M < K * Real.sqrt (Y ω) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hM.le).mp h1
    have h3 : Real.sqrt (Y ω) ^ 2 = Y ω := Real.sq_sqrt (hnn ω)
    have h4 : 0 ≤ K * Real.sqrt (Y ω) := mul_nonneg hK (Real.sqrt_nonneg _)
    have h5 : M ^ 2 < (K * Real.sqrt (Y ω)) ^ 2 := by nlinarith
    have h6 : (K * Real.sqrt (Y ω)) ^ 2 = K ^ 2 * Y ω := by rw [mul_pow, h3]
    have h7 : M ^ 2 < K ^ 2 * Y ω := by rw [← h6]; exact h5
    exact h7.le
  have hTnn : 0 ≤ᵐ[P] fun ω => K ^ 2 * Y ω :=
    Filter.Eventually.of_forall fun ω => by
      show (0:ℝ) ≤ K ^ 2 * Y ω
      exact mul_nonneg (sq_nonneg _) (hnn ω)
  have hTint : Integrable (fun ω => K ^ 2 * Y ω) P := hint.const_mul _
  have hmk := mul_meas_ge_le_integral_of_nonneg hTnn hTint (M ^ 2)
  rw [measureReal_def, integral_const_mul] at hmk
  have hreal : (P {ω : Ω | M ^ 2 ≤ K ^ 2 * Y ω}).toReal ≤ B / M ^ 2 := by
    rw [le_div_iff₀ hM2]
    nlinarith [hmk]
  have hfin : P {ω : Ω | M ^ 2 ≤ K ^ 2 * Y ω} ≠ ⊤ := measure_ne_top P _
  calc P {ω : Ω | ENNReal.ofReal M < N ω}
      ≤ P {ω : Ω | M ^ 2 ≤ K ^ 2 * Y ω} := measure_mono hsub
    _ = ENNReal.ofReal ((P {ω : Ω | M ^ 2 ≤ K ^ 2 * Y ω}).toReal) :=
        (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal (B / M ^ 2) := ENNReal.ofReal_le_ofReal hreal

/-- **Tightness on the small-scale range `1 ≤ R ≤ R₀`.** Produces a single level `M` above
which the `H^{-s}(D)` norm of the `ω`-representative of the centred, rescaled odometer field
has probability at most `ε`, uniformly over that whole range: the time `⌊R^α⌋₊` is bounded by
`⌊R₀^α⌋₊`, the mesh sum is bounded by `Sandpile.Support.exists_uniform_second_moment_le` at
that fixed time and a fixed box radius depending on `R₀`, and `measure_gt_le_of_sqrt_bound`
turns the resulting second-moment bound into the tail bound via
`exists_negSobolevNorm_omegaRep_le`. -/
theorem exists_tight_bound_small (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    {s : ℝ} (hs : 0 ≤ s) {D : Set (Space 4)} (hD : IsDomain D) {w : Space 4 → ℝ}
    (hw : IsAveragingDensity D w) {α : ℝ} (hα : 0 ≤ α) (R₀ : ℝ) (_hR₀ : 1 ≤ R₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ R : ℝ, 1 ≤ R → R ≤ R₀ →
      LatticeProb.iidLaw 4 ν {ζ | ENNReal.ofReal M < negSobolevNorm 4 s D
        (omegaRep D w (latticePairing R (fun x => odometerOf ζ ⌊R ^ α⌋₊ x -
          ∫ η, odometerOf η ⌊R ^ α⌋₊ 0 ∂(LatticeProb.iidLaw 4 ν))))} ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨K, L, hK0, hL0, hKb⟩ := exists_negSobolevNorm_omegaRep_le (d := 4) hs hD hw
  set t₀ : ℕ := ⌊R₀ ^ α⌋₊ with ht₀
  set Nb : ℕ := ⌈R₀ * L⌉₊ + 1 with hNb
  obtain ⟨V, hV0, hVb⟩ := exists_uniform_second_moment_le (d := 4) ν hsq t₀
  set B : ℝ := K ^ 2 * ((2 * (Nb : ℝ) + 1) ^ 4 * V) with hB
  have hB0 : 0 ≤ B := by
    have : (0:ℝ) ≤ (2 * (Nb : ℝ) + 1) ^ 4 := by positivity
    exact mul_nonneg (sq_nonneg _) (mul_nonneg this hV0)
  set M : ℝ := Real.sqrt (B / ε + 1) with hMdef
  have hMpos : 0 < M := Real.sqrt_pos.mpr (by positivity)
  have hMsq : M ^ 2 = B / ε + 1 := Real.sq_sqrt (by positivity)
  refine ⟨M, hMpos, ?_⟩
  intro R hR1 hRR₀
  have hR0 : (0:ℝ) < R := by linarith
  set t : ℕ := ⌊R ^ α⌋₊ with ht
  have htt₀ : t ≤ t₀ := by
    have hrp : R ^ α ≤ R₀ ^ α := Real.rpow_le_rpow (by linarith) hRR₀ hα
    exact Nat.floor_le_floor hrp
  set m : ℝ := ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν) with hm
  set g : (Site 4 → ℝ) → Site 4 → ℝ := fun ζ x => odometerOf ζ t x - m with hg
  set n : ℕ := ⌈|R| * L⌉₊ + 1 with hn
  have hnNb : n ≤ Nb := by
    have habs : |R| = R := abs_of_pos hR0
    have h1 : |R| * L ≤ R₀ * L := by rw [habs]; exact mul_le_mul_of_nonneg_right hRR₀ hL0
    have := Nat.ceil_le_ceil h1
    omega
  set Y : (Site 4 → ℝ) → ℝ := fun ζ => R⁻¹ ^ 4 * ∑ x ∈ boxFinset (0 : Site 4) n, g ζ x ^ 2
    with hY
  have hYnn : ∀ ζ, 0 ≤ Y ζ := by
    intro ζ
    have : (0:ℝ) ≤ ∑ x ∈ boxFinset (0 : Site 4) n, g ζ x ^ 2 :=
      Finset.sum_nonneg fun x _ => sq_nonneg _
    exact mul_nonneg (by positivity) this
  have hYint : Integrable Y (LatticeProb.iidLaw 4 ν) :=
    (integrable_finsetSum _ fun x _ => (hVb t htt₀ x).1).const_mul _
  have hdom : ∀ ζ, negSobolevNorm 4 s D (omegaRep D w (latticePairing R (g ζ)))
      ≤ ENNReal.ofReal (K * Real.sqrt (Y ζ)) := fun ζ => hKb R hR0 (g ζ)
  have hEY : ∫ ζ, Y ζ ∂(LatticeProb.iidLaw 4 ν) ≤ (2 * (Nb:ℝ) + 1) ^ 4 * V := by
    have hsum : ∫ ζ, (∑ x ∈ boxFinset (0 : Site 4) n, g ζ x ^ 2) ∂(LatticeProb.iidLaw 4 ν)
        = ∑ x ∈ boxFinset (0 : Site 4) n,
          ∫ ζ, g ζ x ^ 2 ∂(LatticeProb.iidLaw 4 ν) :=
      integral_finsetSum _ fun x _ => (hVb t htt₀ x).1
    have hle : ∑ x ∈ boxFinset (0 : Site 4) n, ∫ ζ, g ζ x ^ 2 ∂(LatticeProb.iidLaw 4 ν)
        ≤ ∑ _x ∈ boxFinset (0 : Site 4) n, V :=
      Finset.sum_le_sum fun x _ => (hVb t htt₀ x).2
    have hcard : (boxFinset (0 : Site 4) n).card = (2 * n + 1) ^ 4 := card_boxFinset _ _
    have hcardle : ((2 * n + 1 : ℕ) : ℝ) ^ 4 ≤ (2 * (Nb:ℝ) + 1) ^ 4 := by
      have h1 : ((2 * n + 1 : ℕ) : ℝ) ≤ 2 * (Nb:ℝ) + 1 := by
        push_cast
        have : (n:ℝ) ≤ (Nb:ℝ) := by exact_mod_cast hnNb
        linarith
      exact pow_le_pow_left₀ (by positivity) h1 4
    have hstep : ∑ _x ∈ boxFinset (0 : Site 4) n, V = ((2 * n + 1 : ℕ) : ℝ) ^ 4 * V := by
      rw [Finset.sum_const, hcard]
      push_cast
      ring
    have hfin : ∫ ζ, (∑ x ∈ boxFinset (0 : Site 4) n, g ζ x ^ 2) ∂(LatticeProb.iidLaw 4 ν)
        ≤ (2 * (Nb:ℝ) + 1) ^ 4 * V := by
      rw [hsum]
      refine le_trans hle ?_
      rw [hstep]
      exact mul_le_mul_of_nonneg_right hcardle hV0
    have hRinv : R⁻¹ ^ 4 ≤ 1 := by
      have : R⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]; right; exact hR1
      have h0 : (0:ℝ) ≤ R⁻¹ := by positivity
      calc R⁻¹ ^ 4 ≤ 1 ^ 4 := pow_le_pow_left₀ h0 this 4
        _ = 1 := one_pow 4
    have hnn0 : (0:ℝ) ≤ ∫ ζ, (∑ x ∈ boxFinset (0 : Site 4) n, g ζ x ^ 2)
        ∂(LatticeProb.iidLaw 4 ν) :=
      integral_nonneg fun ζ => Finset.sum_nonneg fun x _ => sq_nonneg _
    rw [hY, integral_const_mul]
    nlinarith
  have hBb : K ^ 2 * ∫ ζ, Y ζ ∂(LatticeProb.iidLaw 4 ν) ≤ B := by
    rw [hB]
    exact mul_le_mul_of_nonneg_left hEY (sq_nonneg _)
  have hmain := measure_gt_le_of_sqrt_bound (LatticeProb.iidLaw 4 ν)
    (fun ζ => negSobolevNorm 4 s D (omegaRep D w (latticePairing R (g ζ)))) Y K B M
    hK0 hMpos hYnn hYint hdom hBb
  refine le_trans hmain (ENNReal.ofReal_le_ofReal ?_)
  rw [hMsq, div_le_iff₀ (by positivity)]
  have hkey : ε * (B / ε + 1) = B + ε := by
    rw [mul_add, mul_one, mul_div_cancel₀ B (ne_of_gt hε)]
  linarith [hkey]

end Sandpile.Support
