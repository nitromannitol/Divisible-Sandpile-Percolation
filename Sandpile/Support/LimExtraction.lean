/-
`lem:finite-scale-extraction` (`sandpile.tex:2415-2425`) assembled from its two
steps.

  "[Finite-scale extraction]  Fix `N≥1` axis-parallel rectangles `𝓡_1,…,𝓡_N` in
   the plane and a coordinate crossing direction for each rectangle.  For every
   `ε>0`, there are `c>0` and rational scales `s_1,…,s_k∈(0,1)` such that
   `P(⋂_{j=1}^N H_{𝓡_j}(4c; max_{1≤i≤k} 𝒳_{s_i}))≥1-ε`."

Step 1 (`Sandpile/Support/LimStepOne.lean`) gives, almost surely, a rational
scale for each rectangle at which the level set at height `b(s)` crosses it.
Step 2 (`Sandpile/Support/CrossExtract.lean`) replaces the random finite set of
scales by a prefix of one enumeration of the rationals in `(0,1)` and takes a
stage of the increasing sequence of events by continuity from below.

That stage is chosen on one space carrying white noise, while the statement
fixes `c` and the scales before any space is named.  The two are reconciled by
the transfer of `Sandpile/Support/LimTransfer.lean`, which carries a crossing
bound for all the rectangles from one space to another at the cost of halving
the level: the level `4c₀` of the stage becomes `2c₀ = 4(c₀/2)` everywhere, and
`c = c₀/2` is the constant the lemma returns.
-/
import Sandpile.Support.LimLaw
import Sandpile.Support.LimStepOne
import Sandpile.Support.LimTransfer
import Sandpile.Support.LimSymmetry
import Sandpile.Support.CrossBallSym
import Sandpile.Frozen.FixedScaleCrossings

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A space carrying a white noise whose ball fields are almost surely
continuous.  The statement of the lemma is vacuous when there is none. -/
def CarriesWhiteNoise (d : ℕ) (Ω : Type) [MeasurableSpace Ω] : Prop :=
  ∃ (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
    Sandpile.Continuum.IsWhiteNoise d W P ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ᵐ ω ∂P, Continuous fun u => ballField d W t u ω

/-- The lower bound of Step 1 from `prop:fixed-scale-crossings`: the proposition
gives the liminf bound for the unit field on the rectangles `[-θR,θR]×[0,2R]`, and
the rescaled crossing estimate turns it into the bound at every small rational
scale. -/
theorem scaleCrossingLower_of_fixed_scale
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {d : ℕ} (hd : d = 2 ∨ d = 3) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P)
    (hcont : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ᵐ ω ∂P, Continuous fun u => ballField d W t u ω) :
    ScaleCrossingLower d P W := by
  intro al h hal hh
  obtain ⟨p, hp, hmain⟩ :=
    Sandpile.Frozen.fixed_scale_crossings hRSWc hPitt d hd (al / h) (div_pos hal hh)
  refine ⟨p / 2, by positivity, fun L hL => ?_⟩
  obtain ⟨s₀, hs₀, hbnd⟩ := rescaled_crossing_estimate hGauss hd hW hcont al h hal hh p hp
    (hmain Ω P W hW hcont) L hL
  refine ⟨s₀, hs₀, fun s hs hss => ?_⟩
  have hb := hbnd s hs hss
  rwa [show (if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * (s : ℝ) = crossScale d (s : ℝ) from
    (crossScale_eq_fieldScale_mul hd hs).symm] at hb

/-- And the same bound at an arbitrary rectangle and direction, by the symmetry
in law of the ball field.  This is the second of the two facts Step 1 rests on;
the remaining one is the zero-one law. -/
theorem scaleCrossingLowerAt_of_lower
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {d : ℕ} (hd : d = 2 ∨ d = 3) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P)
    (hcont : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ᵐ ω ∂P, Continuous fun u => ballField d W t u ω)
    (hlow : ScaleCrossingLower d P W) (a b : Fin 2 → ℝ) (hab : ∀ k : Fin 2, a k < b k)
    (i : Fin 2) : ScaleCrossingLowerAt d P W a b i := by
  obtain ⟨p, hp, hmain⟩ := hlow ((b i - a i) / 2) ((b (swapIdx i) - a (swapIdx i)) / 2)
    (by linarith [hab i]) (by linarith [hab (swapIdx i)])
  refine ⟨p, hp, fun L hL => ?_⟩
  obtain ⟨s₀, hs₀, hbnd⟩ := hmain (L + 1) (by linarith)
  refine ⟨min s₀ 1, lt_min hs₀ one_pos, fun s hs hss => ?_⟩
  have hss₀ : (s : ℝ) < s₀ := lt_of_lt_of_le hss (min_le_left _ _)
  have hs1 : (s : ℝ) ≤ 1 := (lt_of_lt_of_le hss (min_le_right _ _)).le
  have hgen := measure_crossing_general_of_symmetric P
    (fun u => measurable_ballField hd hW hs u) (hcont (s : ℝ) hs hs1)
    (isSymmetricField_ballField hGauss hd hW hs) hab i
    (ε := crossScale d (s : ℝ)) (crossScale_pos hs) (hbnd s hs hss₀)
  have hlev : (L + 1) * crossScale d (s : ℝ) - crossScale d (s : ℝ)
      = L * crossScale d (s : ℝ) := by ring
  rwa [hlev] at hgen

/-- `lem:finite-scale-extraction` from `prop:fixed-scale-crossings`, Step 1 and
the law of the finite-scale maximum. -/
theorem finite_scale_extraction_of_inputs
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {d : ℕ} (hd : d = 2 ∨ d = 3)
    (hZ : ScaleCrossingAS d) (hLaw : MaxBallFieldLaw d)
    {N : ℕ} (a b : Fin N → Fin 2 → ℝ) (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i)
    (dir : Fin N → Fin 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℝ) (k : ℕ) (s : Fin k → ℚ), 0 < c ∧ 0 < k ∧
      (∀ i : Fin k, 0 < s i ∧ s i < 1) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W P →
        (∀ t : ℝ, 0 < t → t ≤ 1 → ∀ᵐ ω ∂P, Continuous fun u => ballField d W t u ω) →
      ENNReal.ofReal (1 - ε) ≤ P {ω | ∀ j : Fin N,
        Crosses (a j) (b j) (dir j)
          {u | 4 * c ≤ ⨆ i : Fin k, ballField d W (s i : ℝ) u ω}} := by
  by_cases hex : ∃ (Ω : Type) (m : MeasurableSpace Ω), @CarriesWhiteNoise d Ω m
  · obtain ⟨Ω₀, m₀, hcar⟩ := hex
    letI := m₀
    obtain ⟨P₀, hP₀, W₀, hW₀, hc₀⟩ := hcar
    letI := hP₀
    obtain ⟨q, hq, hsurj⟩ := exists_scale_enum
    have hlow₀ := scaleCrossingLower_of_fixed_scale hRSWc hPitt hGauss hd hW₀ hc₀
    have hAS := ae_exists_scale_crossing_all hZ Ω₀ P₀ W₀ hW₀ hc₀ a b hab dir
      (fun j => scaleCrossingLowerAt_of_lower hGauss hd hW₀ hc₀ hlow₀ (a j) (b j) (hab j) (dir j))
    have hfull := prefixEvent_union_eq_one P₀ a b dir
      (fun r u ω => ballField d W₀ (r : ℝ) u ω) q hsurj (fun r => crossScale d (r : ℝ))
      (fun r hr0 _ => crossScale_pos (by exact_mod_cast hr0)) hAS
    obtain ⟨c₀, k, s, hc₀pos, hk, hs, hbound⟩ :=
      exists_finite_scales P₀ a b dir (fun r u ω => ballField d W₀ (r : ℝ) u ω) q hq hfull ε hε
    have hs' : ∀ i : Fin k, 0 < ((s i : ℚ) : ℝ) ∧ ((s i : ℚ) : ℝ) ≤ 1 := fun i => by
      exact ⟨by exact_mod_cast (hs i).1, by exact_mod_cast (hs i).2.le⟩
    refine ⟨c₀ / 2, k, s, by positivity, hk, hs, ?_⟩
    intro Ω _ P _ W hW hcont
    have htrans := measure_crossing_all_transfer P₀ P
      (maxBallField d k W₀ s) (maxBallField d k W s)
      (fun u => measurable_maxBallField hd hW₀ (fun i => (hs' i).1) u)
      (fun u => measurable_maxBallField hd hW (fun i => (hs' i).1) u)
      (ae_continuous_maxBallField P₀ hk W₀ hs' hc₀)
      (ae_continuous_maxBallField P hk W hs' hcont)
      (hLaw Ω₀ Ω P₀ P W₀ W hW₀ hW k s hs) a b hab dir (4 * c₀) (2 * c₀) (by linarith)
    have hlev : 4 * c₀ - 2 * c₀ = 4 * (c₀ / 2) := by ring
    rw [hlev] at htrans
    exact le_trans hbound htrans
  · refine ⟨1, 1, fun _ => 1 / 2, one_pos, one_pos, fun _ => by norm_num, ?_⟩
    intro Ω _ P _ W hW hcont
    exact absurd ⟨Ω, ‹MeasurableSpace Ω›, P, ‹IsProbabilityMeasure P›, W, hW, hcont⟩ hex

end Sandpile.Support
