import Sandpile.Support.Dgt4ABandLawParameters
import Sandpile.Support.Dgt4ABandParameters
import Sandpile.Support.Dgt4ABandLawDensity
import Sandpile.Support.Dgt4ABandLawLower
import Sandpile.Support.Dgt4ABandLawIntegrated
import Sandpile.Support.Dgt4ABandOneStep
import Sandpile.Support.Dgt4ABandReplacement
import Sandpile.Support.Dgt4ABandLawTail
import Sandpile.Support.Dgt4ABandLawMean
import Sandpile.Support.MeanOvershootJensen
import Sandpile.Support.Dgt4ABandStep2Refuted
import Sandpile.Support.Dgt4ABandLawNormalized
import Sandpile.Support.Dgt4ABandIndependence
import Sandpile.Support.Dgt4ABandHitting
import Sandpile.Support.Dgt4ABandTau
import Sandpile.Support.Dgt4ABandScaled
import Sandpile.Support.Dgt4ABandInvert
import Sandpile.Support.Dgt4ABandIndex

/-!
# Vacuity checks for the band construction

Each clause of the Step-1 band predicates, and each estimate of the Step-2 assembly, is
instantiated here at a concrete object, so that none of them is satisfied by a junk value: the
bump has positive mass, the profile really rises from zero to one, the band sits strictly on the
negative axis and carries no mass on the positive one, the band range of the density clause is
nonempty, the exponential trades are strict information at a positive argument, and the
hypotheses of the hitting-time lemmas are simultaneously satisfiable at a sequence whose hitting
time is positive.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace Sandpile.Support

/-- The smooth bump really has positive mass, so `bandBump` is a genuine
probability density and `bandStep` is not the junk constant. -/
example : 0 < bandBumpMass := bandBumpMass_pos

example : bandStep 1 = 1 := bandStep_eq_one_of_one_le le_rfl

example : bandStep 0 = 0 := bandStep_eq_zero_of_nonpos le_rfl

/-- The profile is not constant: it rises from `0` to `1`. -/
example : bandShape (3 / 2) 4 0 = 0 := bandShape_eq_zero_of_nonpos le_rfl

example : bandShape (3 / 2) 4 1 = 1 :=
  bandShape_eq_one_of_one_le (by norm_num) (by norm_num) le_rfl

/-- The band component's distribution function really reaches one inside the
band, so the component is not the zero measure. -/
example : bandComponentCDF (1 / 2) 1 (3 / 2) 4 (-(1 / 2 : ℝ)) = 1 := by
  refine bandComponentCDF_eq_one_of_ge (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  norm_num

/-- **The side of the origin the density bound reads.**  A band component carries
its whole mass on the REFLECTED band interval `[-a, -ℓ_1 a]`, which is the
interval `BandDensity` now bounds, ... -/
example : ∫ x in (-1 : ℝ)..(-(1 / 2 : ℝ)), bandComponent (1 / 2) 1 (3 / 2) 4 x = 1 :=
  integral_bandComponent (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- ... and carries no mass at all on the positive interval `[ℓ_1 a, a]` that the
old transcription bounded, so the two statements were about different things. -/
example : ∫ x in (1 / 2 : ℝ)..(1 : ℝ), bandComponent (1 / 2) 1 (3 / 2) 4 x = 0 := by
  have hz : EqOn (fun x : ℝ => bandComponent (1 / 2) 1 (3 / 2) 4 x) (fun _ => (0 : ℝ))
      (uIcc (1 / 2 : ℝ) 1) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hx
    have h1 : (1 : ℝ) / 2 ≤ x := hx.1
    refine bandComponent_eq_zero_of_ge (by norm_num) (by norm_num) (by norm_num) ?_
    norm_num
    linarith
  rw [intervalIntegral.integral_congr hz]
  simp

/-- The hypotheses of the profile theorem are simultaneously satisfiable, and
at such a choice the constructed law is a probability measure whose density is
smooth and strictly positive, which satisfies the Step-1 band profile, the
corrected Step-1 density bound, the whole Step-1 output, and the Step-2
integrated profile. -/
example : ∃ (P : BandParameters) (m : ℕ → ℕ) (mu : ℝ) (v : ℝ≥0),
    IsProbabilityMeasure (P.law m mu v) ∧
    BandProfile P (P.law m mu v) ∧
    (∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
      P.law m mu v = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z)) ∧
    Tendsto (fun k : ℕ =>
      ((P.law m mu v) {z : ℝ | -(z) > P.level k}).toReal / P.weight k) atTop (𝓝 0) ∧
    BandDensity P (P.law m mu v) ∧
    BandLawProfile P (P.law m mu v) ∧
    BandIntegratedProfile P (P.law m mu v) ∧
    (∀ t : ℝ, Integrable (fun z : ℝ => max (-z - t) 0) (P.law m mu v)) := by
  obtain ⟨P, -, hlam, -, hband, hparam, -, hlt, -, -⟩ :=
    BandParameters.exists_admissible (1 / 2) (by norm_num) (by norm_num)
  have hA : P.A⁻¹ ≤ P.l1 := by
    rw [inv_eq_one_div]
    exact hband.le
  have hlam1 : 1 < P.lam0 * P.l1 := by
    have hl0 : 0 < P.l1 := P.hl1.1
    have := (div_lt_iff₀ hl0).mp hlam
    linarith
  have hmtop : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hwtot : (1 - ∑' k, P.weight k) + ∑' k, P.weight k = 1 := by ring
  have hwa : Summable fun k => P.weight k * P.level k := by
    simpa only [mul_comm] using P.summable_level_weight
  refine ⟨P, fun k => k + 1, 0, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isProbabilityMeasure_bandLaw (by linarith) (fun k => (P.weight_pos k).le)
      (fun k => lt_of_lt_of_le one_pos (P.htheta k).1) P.hl1.1 P.hl1.2 P.level_pos
      (fun k => Nat.succ_pos k) P.level_tendsto (by norm_num) P.summable_weight hwtot
  · exact bandProfile_law P hA _ (fun k => Nat.succ_pos k) hmtop 0 1 (by norm_num) hlt.le
  · exact exists_density_bandLaw (by linarith) (by norm_num)
      (fun k => le_trans zero_le_one (P.htheta k).1) (fun k => (P.weight_pos k).le)
      P.hl1.1 P.hl1.2 P.level_pos (fun k => Nat.succ_pos k) P.level_tendsto
  · exact bandUpperIsolation_tail_law P hA _ (fun k => Nat.succ_pos k) hmtop 0 1
      (by norm_num) hlt.le
  · exact bandDensity_law P hA _ (fun k => Nat.succ_pos k) 0 1 (by norm_num) hlt.le
  · exact bandLawProfile_law P hA hlam1 hparam _ (fun k => Nat.succ_pos k) hmtop 0 1
      (by norm_num) hlt.le
  · exact bandIntegratedProfile_law P hA _ (fun k => Nat.succ_pos k) hmtop 0 1
      (by norm_num) hlt.le
  · intro t
    exact integrable_posPart_bandLaw (by linarith) (fun k => (P.weight_pos k).le)
      (fun k => lt_of_lt_of_le one_pos (P.htheta k).1) P.hl1.1 P.hl1.2 P.level_pos
      (fun k => Nat.succ_pos k) P.level_tendsto (by norm_num) P.summable_weight hwtot hwa t

/-- **The whole Step-1 output is satisfiable**, at `ℓ_0 = 1/2`: a single law that
is a probability measure, has mean zero, variance one, a smooth strictly positive
density, an exponential moment, a two-sided linear log tail, all four band
estimates, the integrated profile, and band exponents whose `κ_k` fill `[3/2,2]`.
This is the strongest non-vacuity check available for Step 1: variance one alone
rules out every degenerate law. -/
example : ∃ (P : BandParameters) (m : ℕ → ℕ) (mu : ℝ) (v : ℝ≥0),
    (1 : ℝ) / 2 < P.l1 ∧ (∀ k, 0 < m k) ∧ v ≠ 0 ∧
    IsProbabilityMeasure (P.law m mu v) ∧
    ∫ z : ℝ, z ∂(P.law m mu v) = 0 ∧
    variance (id : ℝ → ℝ) (P.law m mu v) = 1 ∧
    BandLawProfile P (P.law m mu v) ∧
    BandIntegratedProfile P (P.law m mu v) := by
  obtain ⟨P, m, mu, v, h1, hm, -, hv, hprob, hmean, hvar, -, -, hprof, hint, -⟩ :=
    exists_step1_law (1 / 2) (by norm_num) (by norm_num)
  exact ⟨P, m, mu, v, h1, hm, hv, hprob, hmean, hvar, hprof, hint⟩

/-- **The Step-1 analytic clauses of the frozen statement that are now proved**,
at parameters produced by `BandParameters.exists_admissible`: the exponential
moment and the two-sided linear log tail in the exact shape the frozen `htail`
asks for, and a shift making the mean zero. -/
example : ∃ (P : BandParameters) (m : ℕ → ℕ) (mu : ℝ) (v : ℝ≥0),
    (∃ c C θ0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ0 ∧
      Integrable (fun z : ℝ => Real.exp (θ0 * |z|)) (P.law m mu v) ∧
      ∀ᶠ r : ℝ in atTop,
        c * r ≤ -Real.log ((P.law m mu v) (Iic (-r))).toReal ∧
          -Real.log ((P.law m mu v) (Iic (-r))).toReal ≤ C * r) ∧
    ∫ z : ℝ, z ∂(P.law m mu v) = 0 := by
  obtain ⟨P, -, -, -, -, -, -, hlt, -, -⟩ :=
    BandParameters.exists_admissible (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨mu, hmu⟩ := exists_mean_zero_law P (fun k => k + 1) (fun k => Nat.succ_pos k) 1
    (by norm_num) hlt
  exact ⟨P, fun k => k + 1, mu, 1,
    exists_log_tail_law P (fun k => k + 1) (fun k => Nat.succ_pos k) mu 1 (by norm_num) hlt.le,
    hmu⟩

/-- The generic Jensen step is not vacuous: its convexity and monotonicity
ingredients hold for a measure whose mean overshoot above every level is
finite. -/
example :
    ConvexOn ℝ (Set.univ : Set ℝ) (meanOvershoot (volume.restrict (Set.Icc (0 : ℝ) 1))) ∧
      Antitone (meanOvershoot (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hint : ∀ w : ℝ,
      Integrable (fun x : ℝ => max (x - w) 0) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    intro w
    exact ((continuous_id.sub continuous_const).max continuous_const).integrableOn_Icc
  exact ⟨convexOn_meanOvershoot _ hint, antitone_meanOvershoot _ hint⟩

/-- The Step-2 band material is not about empty sets: the band between two
levels is genuinely nonempty, and the exponentially weighted indicator is
positive on its carrier, so `measure_band_le`, `measure_lt_le_expWeight` and the
independence identity are not vacuous. -/
example : ((-3 / 2 : ℝ), (1 : ℝ)) ∈ bandGap 2 := by
  rw [bandGap]
  norm_num

example : (-3 / 2 : ℝ) ∈ symmDiff {z : ℝ | -(z) > 1} {z : ℝ | -(z) > 2} := by
  rw [← slice_bandGap]
  rw [bandGap]
  norm_num

example : expWeightBelow 1 0 0 = 1 := by
  rw [expWeightBelow, Set.indicator_of_mem (by norm_num : (0 : ℝ) ∈ {z : ℝ | -z ≤ 0})]
  norm_num

example : (0 : ℝ) < expWeightBelow 1 0 1 := by
  rw [expWeightBelow, Set.indicator_of_mem (by norm_num : (1 : ℝ) ∈ {z : ℝ | -z ≤ 0})]
  positivity

/-- The half-open band the density bound is read on has positive length whenever
the two levels differ, so `measure_band_le` is not a statement about the empty
set. -/
example (P : BandParameters) (k : ℕ) :
    (Set.Ico (-P.level k) (-(P.l1 * P.level k))).Nonempty := by
  have h := P.level_pos k
  have hl1 := P.hl1.2
  refine ⟨-P.level k, le_rfl, ?_⟩
  have hkey : P.l1 * P.level k < P.level k := by nlinarith
  linarith

/-- The exponential trade for a positive part is not vacuous: at a positive
argument both sides are positive and the inequality is strict information. -/
example : max (1 : ℝ) 0 ≤ Real.exp (1 * 1) / (1 * Real.exp 1) := posPart_le_exp one_pos 1

/-- The integrand of the mean-increment identity is genuinely nonzero. -/
example : max (-(-1 : ℝ) - 0) 0 = 1 := by norm_num

/-- **The hitting-time lemmas are not vacuous**: their hypotheses are
simultaneously satisfiable at a sequence whose hitting time is positive, and the
two conclusions are then genuine bounds on it. -/
example : ∃ hex : ∃ n : ℕ, (3 : ℝ) ≤ (n : ℝ),
    0 < Nat.find hex ∧ ((Nat.find hex : ℕ) : ℝ) ≤ 3 / 1 + 1 ∧
      ((Nat.find hex : ℕ) : ℝ) ≤ 3 + 1 := by
  have hex : ∃ n : ℕ, (3 : ℝ) ≤ (n : ℝ) := ⟨3, by norm_num⟩
  refine ⟨hex, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso
      have hs := Nat.find_spec hex
      rw [h] at hs
      norm_num at hs
    · exact h
  · exact hitting_le (fun n : ℕ => (n : ℝ)) 1 3 one_pos (by norm_num) (by norm_num)
      (fun i j hij => by dsimp only; exact_mod_cast hij)
      (fun n _ => by push_cast; linarith) hex
  · exact hitting_value_le (fun n : ℕ => (n : ℝ)) 3 1 (by norm_num) (by norm_num)
      (by norm_num) (fun n => by push_cast; linarith) hex

/-- The band range of the density clause is never empty, so that clause is not
satisfied vacuously. -/
example (P : BandParameters) (k : ℕ) : P.l1 * P.level k < P.level k := by
  have h := P.level_pos k
  nlinarith [P.hl1.1, P.hl1.2]

/-- The reflected interval that `BandDensity` bounds has positive length, so the
difference quotient is not `0/0`. -/
example (t ε : ℝ) (hε : 0 < ε) : volume.real (Icc (-(t + ε)) (-t)) = ε := by
  rw [Real.volume_real_Icc_of_le (by linarith)]
  ring

/-- The hypotheses of the Taylor step are simultaneously satisfiable at a
concrete choice, so `abs_oneStep_increment_le` is not vacuous. -/
example : |((1 : ℝ) - 1 / 100) ^ (-(1 : ℝ)) - (1 : ℝ) ^ (-(1 : ℝ)) - 1 * (1 / 100)|
    ≤ 1 * (1 / 100) * 0 + 8 * (1 + 0) ^ 2 * (1 / 100) ^ 2 * (1 : ℝ) ^ (1 : ℝ) := by
  refine abs_oneStep_increment_le (θ := 1) (c := 1 / 100) (z := 1) (δ := 1 / 100) (ε := 0)
    le_rfl (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) ?_ (by norm_num)
  norm_num

/-- The two threshold events are genuinely different sets, so the symmetric
difference the contact error bounds is not always empty. -/
example : symmDiff {z : ℝ | -(z) > 1} {z : ℝ | -(z) > 2} = {z : ℝ | 1 < -z ∧ -z ≤ 2} := by
  have h := symmDiff_thresholdSet (1 : ℝ) 2
  rwa [min_eq_left (by norm_num : (1 : ℝ) ≤ 2), max_eq_right (by norm_num : (1 : ℝ) ≤ 2)] at h

example : (-(3 / 2 : ℝ)) ∈ symmDiff {z : ℝ | -(z) > 1} {z : ℝ | -(z) > 2} := by
  rw [symmDiff_thresholdSet]
  norm_num

/-- The scale `R_k` is not the junk zero, and it satisfies the relation the
summation of the one-step profile is stated against. -/
example : bandScale 1 (fun _ => 2) (fun _ => 1 / 2) 0 = 2 := by
  rw [bandScale, bandScaleSq]
  norm_num

example : bandScale 1 (fun _ => 2) (fun _ => 1 / 2) 0 ^ 2 * (1 / 2 : ℝ) = 1 * 2 :=
  bandScale_sq_mul (by norm_num) (by norm_num) (by norm_num)

/-- **The hitting time is not the junk zero.**  At a sequence rising by one at
each step and a band level four, it is two, the profile coordinate there is
exactly `1/2`, and the two bounds on it are genuine. -/
example : ∃ hex : ∃ n : ℕ, (4 : ℝ) - (1 - 0) * 4 / 2 ≤ (n : ℝ),
    Nat.find hex = 2 ∧
    bandLevelCoord 0 (fun _ => (4 : ℝ)) (fun n => (n : ℝ)) 0 (Nat.find hex) = 1 / 2 := by
  have hex : ∃ n : ℕ, (4 : ℝ) - (1 - 0) * 4 / 2 ≤ (n : ℝ) := ⟨2, by norm_num⟩
  have hfind : Nat.find hex = 2 := by
    refine (Nat.find_eq_iff hex).mpr ⟨by norm_num, ?_⟩
    intro n hn
    interval_cases n <;> norm_num
  refine ⟨hex, hfind, ?_⟩
  rw [bandLevelCoord_eq, hfind]
  norm_num

/-- The hitting-time bound `τ_k ≤ (1/c + 1)/ω_k` is a genuine bound at that
sequence. -/
example : ∃ hex : ∃ n : ℕ, (4 : ℝ) - (1 - 0) * 4 / 2 ≤ (n : ℝ),
    ((Nat.find hex : ℕ) : ℝ) ≤ (1 / 1 + 1) / (1 / 4) := by
  have hex : ∃ n : ℕ, (4 : ℝ) - (1 - 0) * 4 / 2 ≤ (n : ℝ) := ⟨2, by norm_num⟩
  refine ⟨hex, ?_⟩
  refine bandHittingTime_le (l1 := 0) (c := 1) le_rfl (by norm_num) (by norm_num)
    (fun _ => (4 : ℝ)) (fun _ => (1 : ℝ) / 4) (fun n => (n : ℝ)) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun i j hij => by dsimp only; exact_mod_cast hij) (fun n _ => by push_cast; norm_num) hex

/-- The overshoot bound at the hitting time, and the bounded negative power that
`y_{k,τ_k} = O(1)` reads, are genuine at the same sequence. -/
example : ∃ hex : ∃ n : ℕ, (4 : ℝ) - (1 - 0) * 4 / 2 ≤ (n : ℝ),
    1 / 2 - 1 / ((1 - 0) * (4 : ℝ)) ≤
        bandLevelCoord 0 (fun _ => (4 : ℝ)) (fun n => (n : ℝ)) 0 (Nat.find hex) ∧
      bandLevelCoord 0 (fun _ => (4 : ℝ)) (fun n => (n : ℝ)) 0 (Nat.find hex) ^ (-(1 : ℝ))
        ≤ (4 : ℝ) ^ (2 : ℝ) := by
  have hex : ∃ n : ℕ, (4 : ℝ) - (1 - 0) * 4 / 2 ≤ (n : ℝ) := ⟨2, by norm_num⟩
  refine ⟨hex, ?_, ?_⟩
  · exact half_sub_le_bandLevelCoord_hitting (l1 := 0) (M := 1) (fun _ => (4 : ℝ))
      (fun n => (n : ℝ)) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun n => by push_cast; norm_num) hex
  · exact bandProfile_hitting_le (l1 := 0) (M := 1) (Θ := 2) (fun _ => (4 : ℝ))
      (fun n => (n : ℝ)) (fun _ => (1 : ℝ)) 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (fun n => by push_cast; norm_num) (by norm_num) (by norm_num)
      (by norm_num) hex

/-- The increment lower bound carries information: at a point mass inside the
band the left-hand side is positive. -/
example :
    (1 : ℝ) * ((1 - 0) * (4 : ℝ) / 8) ≤ ∫ z, max (-z - 0) 0 ∂(Measure.dirac (-4 : ℝ)) := by
  have hint : Integrable (fun z : ℝ => max (-z - 0) 0) (Measure.dirac (-4 : ℝ)) :=
    integrable_dirac (by simp)
  have hmem : (-4 : ℝ) ∈ {z : ℝ | (4 : ℝ) - (1 - 0) * 4 / 4 < -z} := by
    simp only [Set.mem_setOf_eq]
    norm_num
  have hmass : (1 : ℝ) ≤
      ((Measure.dirac (-4 : ℝ)) {z : ℝ | (4 : ℝ) - (1 - 0) * 4 / 4 < -z}).toReal := by
    rw [MeasureTheory.Measure.dirac_apply_of_mem hmem]
    norm_num
  exact integral_posPart_neg_ge_band (l1 := 0) (Measure.dirac (-4 : ℝ)) (fun _ => (4 : ℝ)) 0
    0 1 (by norm_num) (by norm_num) hmass hint

/-- **The summed profile is satisfiable once the profile is a family.**  The
single-sequence reading is refuted by `no_single_sequence_summed_profile` in
exactly this regime, the band weights tending to zero at a bounded exponent; the
family reading carries it, with the exact profile `y_{k,n} = nω_k/(G(0,0)κ_k)`,
and the conclusion it yields is the genuine limit `t/κ`. -/
example : ∀ δ T : ℝ, 0 < δ → δ < T →
    Filter.Tendsto (fun k : ℕ => ⨆ t ∈ Set.Icc δ T,
      |(fun (k n : ℕ) => (n : ℝ) * (1 / ((k : ℝ) + 1) / (1 * (3 / 2)))) k
          (⌊t * ((k : ℝ) + 1) ^ 2⌋₊) / ((k : ℝ) + 1) - t / (3 / 2)|)
      Filter.atTop (nhds 0) := by
  refine scaledProfile_of_increments_family
    (fun (k n : ℕ) => (n : ℝ) * (1 / ((k : ℝ) + 1) / (1 * (3 / 2))))
    (fun k => (k : ℝ) + 1) (fun k => (k : ℝ) + 1)
    (fun k => 1 / ((k : ℝ) + 1)) (fun _ => (0 : ℝ)) (fun _ => (3 : ℝ) / 2) (fun _ => 0)
    (3 / 2) (by norm_num) (fun _ => le_rfl) 1 one_pos (fun k => ?_) ?_ ?_ ?_ ?_ ?_ ?_
  · have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  · exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  · exact tendsto_const_nhds
  · simp
  · exact ⟨0, by simp⟩
  · intro T hT
    filter_upwards with k n _ i _ _
    push_cast
    ring_nf
    simp

/-- The inversion step is not vacuous: its hypotheses hold at a genuinely
moving family, and the conclusion is then a statement about the reciprocals. -/
example : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ k : ℕ in Filter.atTop, ∀ t ∈ Set.Icc (1 : ℝ) 2,
    |(t + 1 / ((k : ℝ) + 1))⁻¹ - t⁻¹| ≤ ζ := by
  refine eventually_abs_inv_sub_le (fun k t => t + 1 / ((k : ℝ) + 1)) (fun _ t => t)
    (Set.Icc (1 : ℝ) 2) 1 one_pos ?_ ?_
  · filter_upwards with k t ht
    exact ht.1
  · intro ζ hζ
    obtain ⟨N, hN⟩ :=
      Metric.tendsto_atTop.mp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ζ hζ
    filter_upwards [Filter.eventually_ge_atTop N] with k hk t _
    have hd := hN k hk
    rw [Real.dist_eq, sub_zero] at hd
    have hpos : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    rw [show t + 1 / ((k : ℝ) + 1) - t = 1 / ((k : ℝ) + 1) by ring, abs_of_nonneg hpos]
    exact le_of_lt (lt_of_abs_lt hd)

/-- The index shift is not vacuous: its hypotheses hold at a family whose
consecutive values genuinely differ, and the conclusion is the ratio limit. -/
example : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ k : ℕ in Filter.atTop, ∀ n : ℕ, True →
    |((n : ℝ) + ((k : ℝ) + 1)) / (((n - 1 : ℕ) : ℝ) + ((k : ℝ) + 1)) - 1| ≤ ζ := by
  refine eventually_abs_ratio_sub_one_le (fun k n => (n : ℝ) + ((k : ℝ) + 1))
    (fun k => (k : ℝ) + 1) (fun _ => 1) (fun _ _ => True) 1 one_pos ?_ ?_ ?_ ?_
  · filter_upwards with k
    positivity
  · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · filter_upwards with k n _
    have : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  · filter_upwards with k n _
    rcases n with _ | m
    · norm_num
    · rw [Nat.succ_sub_one]
      push_cast
      rw [show (m : ℝ) + 1 + ((k : ℝ) + 1) - ((m : ℝ) + ((k : ℝ) + 1)) = 1 by ring]
      norm_num

/-- The first-failure argument does real work: from a start at zero and a step
that uses the bound already established, it gives the bound throughout. -/
example (u : ℕ → ℝ) (h0 : u 0 = 0) (hstep : ∀ n : ℕ, u (n + 1) ≤ u n + 1) (N : ℕ) :
    ∀ n : ℕ, n ≤ N → u n ≤ (n : ℝ) := by
  refine forall_le_of_step u (fun n => (n : ℝ)) N (by rw [h0]; norm_num) ?_
  intro n _ hn
  have h1 := hn n le_rfl
  have h2 := hstep n
  push_cast
  linarith

/-- The persistence of the upper end of the index range is a genuine inequality
between two positive numbers. -/
example : ((1 : ℝ) / 4) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (-(1 : ℝ)) :=
  rpow_le_two_rpow_neg (by norm_num) (by norm_num) zero_le_one

example : ((1 : ℝ) / 4) ^ (1 : ℝ) = 1 / 4 := Real.rpow_one _

/-- The two glue identities of the bookkeeping read the way the paper uses them:
the band level at the profile coordinate IS the frozen mean level, and the
decrement of the coordinate IS the increment of the level over the band width. -/
example : (4 : ℝ) - (1 - 0) * 4 * bandLevelCoord 0 (fun _ => (4 : ℝ)) (fun n => (n : ℝ)) 0 2
    = 2 := by
  have h := level_eq_of_bandLevelCoord (l1 := 0) (fun _ => (4 : ℝ)) (fun n => (n : ℝ)) 0 2
    (by norm_num)
  simpa using h

example : bandLevelCoord 0 (fun _ => (4 : ℝ)) (fun n => (n : ℝ)) 0 2
    - bandLevelCoord 0 (fun _ => (4 : ℝ)) (fun n => (n : ℝ)) 0 3 = 1 / 4 := by
  rw [bandLevelCoord_sub_succ]
  push_cast
  norm_num

end Sandpile.Support
