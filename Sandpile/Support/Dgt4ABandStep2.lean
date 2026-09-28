import Sandpile.Support.Dgt4ABandOneStepLaw
import Sandpile.Support.Dgt4ABandIndex
import Sandpile.Support.Dgt4ABandSlowWeights
import Sandpile.Support.Dgt4ABandInvert
import Sandpile.Support.Dgt4AStep2Output
import Sandpile.Support.GreenRatioStrict

/-!
# Step 2 of the many-limits theorem, stated end to end

Step 1 builds the one-site law and its band estimates; Step 3 turns Step 2's output into the
field limits. Both are proved. This file is Step 2: from the band estimates to
`Dgt4AStep2Output`, together with the scale the theorem needs.

This is the second statement of Step 2. The first was audited before any proof was written and
six defects were found; the corrections are recorded where they bite. In particular the scale
is CONSTRUCTED here rather than taken as given: the paper's auxiliary sequence grows slowly
enough that the band errors times its square still vanish, and a vacuity check showed that for
a fast sequence the one-step hypotheses are outright false, so the choice is what keeps Step 2
meaningful rather than merely convenient.

  (a) the band errors as one sequence            `bandErrorSeq`
  (b) the slow scale, constructed                `exists_bandScale`
  (c) the one-step increment, at a single index  `bandProfile_increment`  [OneStepLaw]
  (d) the two-sided index range                  `bandProfile_range`
  (e) the scaled profile                         `bandScaledProfile`
  (f) the contact rate                           `bandContactRate_of_scaled`
  (g) the contact comparison                     `bandContactComparison_of_band`
  (h) Step 2's output, with its scale            `exists_dgt4AStep2Output`
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- **The band estimates at a common rate.**  The remaining nodes need not only
the increment at rate `e` but the other band estimates at the same rate: the band
tail, the lower isolation, the origin concentration and the mass above the band.
Each is available qualitatively, and one sequence dominating all of them at once
is what the slow-scale choice consumes.  The paper says exactly this, choosing the
auxiliary sequence against four named errors at once.

Carrying only the increment at a rate, as the first version did, is not enough:
after every reduction the contact estimates leave a term that is the auxiliary
sequence times the tolerance of ANOTHER estimate, and a qualitative statement has
no tolerance to bound. -/
def BandModuli (P : BandParameters) (d : ℕ) (ν : Measure ℝ) (e : ℕ → ℝ) : Prop :=
  (∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
        |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
            - P.weight k / (green d 0 0 * (P.theta k + 1))
              * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
          ≤ e k * P.weight k) ∧
  (∀ᶠ k : ℕ in atTop, ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
      |(ν {z : ℝ | -(z) > P.level k - (1 - P.l1) * P.level k * r}).toReal / P.weight k
        - r ^ P.theta k| ≤ e k) ∧
  (∀ᶠ k : ℕ in atTop,
      (ν {z : ℝ | -(z) > P.level k}).toReal ≤ e k * P.weight k) ∧
  (∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      meanOdometer (centeredMassLaw d ν) n / green d 0 0 ≤ P.level k →
        (∫ σ, |avg (originOdometer (scenery d σ) n) 0
            - meanOdometer (centeredMassLaw d ν) n / green d 0 0| ∂centeredMassLaw d ν)
          ≤ e k * P.level k) ∧
  (∀ᶠ k : ℕ in atTop, Real.exp (-(P.lam0 * P.l1 * P.level k)) *
      (∫ z, Real.exp (-(P.lam0 * z)) *
        Set.indicator {z : ℝ | -(z) ≤ P.l1 * P.level k} (fun _ => (1 : ℝ)) z ∂ν) /
      P.weight k ≤ e k)


/-- **The diagonal argument.**  A family of properties, each holding eventually in `k`
for every fixed positive tolerance, holds eventually at the tolerance `e k` of ONE
positive null sequence.  For each `j` take an index beyond which the property holds at
tolerance `1/(j+1)`, and let `e k = 1/(j+1)` for the largest `j ≤ k` whose index is
already reached. -/
private theorem bandStep2_diagonal (Q : ℝ → ℕ → Prop)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, Q η k) :
    ∃ e : ℕ → ℝ, (∀ k, 0 < e k) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, Q (e k) k := by
  classical
  have hN : ∀ j : ℕ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → Q (1 / ((j : ℝ) + 1)) k := fun j =>
    eventually_atTop.mp (h _ (by positivity))
  choose N hN using hN
  set j : ℕ → ℕ := fun k => Nat.findGreatest (fun i => N i ≤ k) k with hj
  refine ⟨fun k => 1 / ((j k : ℝ) + 1), fun k => by positivity, ?_, ?_⟩
  · have hjtop : Tendsto j atTop atTop := by
      refine tendsto_atTop.mpr fun J => ?_
      filter_upwards [eventually_ge_atTop (max J (N J))] with k hk
      exact Nat.le_findGreatest (le_trans (le_max_left _ _) hk) (le_trans (le_max_right _ _) hk)
    have hjR : Tendsto (fun k => ((j k : ℕ) : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hjtop)
    exact tendsto_const_nhds.div_atTop hjR
  · filter_upwards [eventually_ge_atTop (N 0)] with k hk
    exact hN (j k) k (Nat.findGreatest_spec (P := fun i => N i ≤ k) (Nat.zero_le k) hk)

/-- **A divergent positive sequence has a monotone positive minorant that still
diverges.**  `L' k` is the least value of `L` from `k` on; it exists because `L → ∞`. -/
private theorem bandStep2_monotone_minorant (L₀ : ℕ → ℝ) (hpos : ∀ k, 0 < L₀ k)
    (htop : Tendsto L₀ atTop atTop) :
    ∃ L : ℕ → ℝ, (∀ k, 0 < L k) ∧ (∀ k, L k ≤ L₀ k) ∧ Monotone L ∧ Tendsto L atTop atTop := by
  have hmin : ∀ k : ℕ, ∃ i₀ : ℕ, ∀ i : ℕ, L₀ (i₀ + k) ≤ L₀ (i + k) := by
    intro k
    have h : Tendsto (fun i : ℕ => L₀ (i + k)) Filter.cofinite atTop := by
      rw [Nat.cofinite_eq_atTop]
      exact htop.comp (tendsto_add_atTop_nat k)
    exact h.exists_forall_le
  choose i₀ hi₀ using hmin
  refine ⟨fun k => L₀ (i₀ k + k), fun k => hpos _, fun k => ?_, ?_, ?_⟩
  · simpa using hi₀ k 0
  · refine monotone_nat_of_le_succ fun k => ?_
    have h := hi₀ k (i₀ (k + 1) + 1)
    have hk : i₀ (k + 1) + 1 + k = i₀ (k + 1) + (k + 1) := by omega
    rw [hk] at h
    exact h
  · refine tendsto_atTop.mpr fun B => ?_
    obtain ⟨K, hK⟩ := eventually_atTop.mp (htop.eventually_ge_atTop B)
    filter_upwards [eventually_ge_atTop K] with k hk
    exact hK _ (le_trans hk (Nat.le_add_left k (i₀ k)))

/-- The band weights tend to zero. -/
private theorem bandStep2_weight_tendsto (P : BandParameters) :
    Tendsto (fun k => P.weight k) atTop (𝓝 0) := by
  have h := (Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp P.level_tendsto)).const_mul P.c0
  simpa [Function.comp_def, BandParameters.weight] using h

/-- `max z 0` is integrable when `z` is. -/
private theorem bandStep2_integrable_pos (ν : Measure ℝ) (hint : Integrable id ν) :
    Integrable (fun z : ℝ => max z 0) ν :=
  hint.abs.mono' (by fun_prop) (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
    exact max_le (le_abs_self z) (abs_nonneg z))

/-- **The increments of the frozen mean level are nonincreasing**: the mean odometer is
concave in time. -/
private theorem bandStep2_incr_anti (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0) :
    Antitone (fun n : ℕ => meanOdometer (centeredMassLaw d ν) (n + 1) / green d 0 0
      - meanOdometer (centeredMassLaw d ν) n / green d 0 0) := by
  have hd1 : 1 ≤ d := by omega
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hpos := bandStep2_integrable_pos ν hint
  refine antitone_nat_of_succ_le fun n => ?_
  have h := meanOdometer_concave hd1 ν hint hmean hpos n
  have h' : meanOdometer (centeredMassLaw d ν) (n + 1 + 1)
      - meanOdometer (centeredMassLaw d ν) (n + 1)
      ≤ meanOdometer (centeredMassLaw d ν) (n + 1) - meanOdometer (centeredMassLaw d ν) n := h
  show meanOdometer (centeredMassLaw d ν) (n + 1 + 1) / green d 0 0
      - meanOdometer (centeredMassLaw d ν) (n + 1) / green d 0 0
      ≤ meanOdometer (centeredMassLaw d ν) (n + 1) / green d 0 0
      - meanOdometer (centeredMassLaw d ν) n / green d 0 0
  rw [← sub_div, ← sub_div]
  exact div_le_div_of_nonneg_right h' hG.le

/-- **The crude one-step bound** on the frozen mean level: every increment is at most the
first one, by concavity. -/
private theorem bandStep2_crude (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, meanOdometer (centeredMassLaw d ν) (n + 1) / green d 0 0
      - meanOdometer (centeredMassLaw d ν) n / green d 0 0 ≤ M := by
  have hd1 : 1 ≤ d := by omega
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hpos := bandStep2_integrable_pos ν hint
  have hanti := bandStep2_incr_anti hd ν hint hmean
  refine ⟨meanOdometer (centeredMassLaw d ν) (0 + 1) / green d 0 0
      - meanOdometer (centeredMassLaw d ν) 0 / green d 0 0, ?_, fun n => hanti (Nat.zero_le n)⟩
  rw [← sub_div]
  exact div_nonneg (sub_nonneg.mpr (meanOdometer_mono hd1 ν hpos (Nat.zero_le _))) hG.le

/-- **The coordinate at the hitting index.**  For large `k`, `z_{k,τ_k}` lies in
`[1/4, 1/2]`, so the profile `z_{k,τ_k}^{-ϑ_k}` is at most `4²`. -/
private theorem bandStep2_hitting_coord (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z) :
    ∀ᶠ k : ℕ in atTop,
      1 / 4 ≤ bandCoordSeq P d ν k (bandTau P hd ν hint hmean hnondeg k) ∧
      bandCoordSeq P d ν k (bandTau P hd ν hint hmean hnondeg k) ≤ 1 / 2 ∧
      bandCoordSeq P d ν k (bandTau P hd ν hint hmean hnondeg k) ^ (-(P.theta k)) ≤ 16 := by
  have hd1 : 1 ≤ d := by omega
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  obtain ⟨M, hM0, hstepM⟩ := bandStep2_crude hd ν hint hmean
  have hb0 : meanOdometer (centeredMassLaw d ν) 0 / green d 0 0 = 0 := by
    rw [meanOdometer_zero d ν, zero_div]
  have h1l' : 0 < 1 - P.l1 := by linarith [P.hl1.2]
  filter_upwards [P.level_tendsto.eventually_ge_atTop (4 * M / (1 - P.l1))] with k hlev
  have ha : 0 < P.level k := P.level_pos k
  have hW : 0 < (1 - P.l1) * P.level k := mul_pos h1l' ha
  have hh : 0 ≤ P.level k - (1 - P.l1) * P.level k / 2 := by
    nlinarith [P.hl1.1, P.hl1.2]
  have hsmall : M / ((1 - P.l1) * P.level k) ≤ 1 / 4 := by
    rw [div_le_iff₀ hW]
    rw [div_le_iff₀ h1l'] at hlev
    nlinarith
  have hex := bandHitting_exists_sandpile P hd ν hint hmean hnondeg k
  have hhi := bandLevelCoord_hitting_le_half (l1 := P.l1) P.level
    (fun n => meanOdometer (centeredMassLaw d ν) n / green d 0 0) k hW hex
  have hlo := half_sub_le_bandLevelCoord_hitting P.level
    (fun n => meanOdometer (centeredMassLaw d ν) n / green d 0 0) k hW hM0 hb0 hh hstepM hex
  have hθ0 : 0 ≤ P.theta k := by linarith [(P.htheta k).1]
  have hbd := bandProfile_hitting_le P.level
    (fun n => meanOdometer (centeredMassLaw d ν) n / green d 0 0) P.theta k hW hM0 hb0 hh
    hstepM hθ0 (P.htheta k).2 hsmall hex
  refine ⟨?_, hhi, ?_⟩
  · have : (1 : ℝ) / 4 ≤ 1 / 2 - M / ((1 - P.l1) * P.level k) := by linarith
    exact this.trans hlo
  · refine hbd.trans (le_of_eq ?_)
    rw [Real.rpow_two]
    norm_num

/-- **(a) The band estimates with an explicit modulus.**  The band estimates are
stated qualitatively, as "for every `η > 0`, eventually in `k`".  The slow-scale
choice needs a single sequence `e k → 0` such that the estimates hold AT LEVEL
`e k` for large `k`.

This is a genuine strengthening and not a repackaging.  The first version of this
statement merely asserted that some nonnegative sequence tends to zero, which is
true of the zero sequence and says nothing about the band at all; it was caught by
the substantiveness check.

Proof.  Diagonalise: for each `j` take an index beyond which the estimate holds
with `η = 1/(j+1)`, make those indices strictly increasing, and let `e k` be
`1/(j+1)` on the `j`-th block. -/
theorem bandErrorSeq (P : BandParameters) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hprof : BandIntegratedProfile P ν) :
    ∃ e : ℕ → ℝ, (∀ k, 0 ≤ e k) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, ∀ z : ℝ, z ∈ Icc (0 : ℝ) 1 →
        |(∫ x, max (-x - (P.level k - (1 - P.l1) * P.level k * z)) 0 ∂ν) /
            (P.weight k * (1 - P.l1) * P.level k)
          - z ^ (P.theta k + 1) / (P.theta k + 1)| ≤ e k := by
  obtain ⟨e, hepos, he, hev⟩ := bandStep2_diagonal
    (fun η k => ∀ z : ℝ, z ∈ Icc (0 : ℝ) 1 →
      |(∫ x, max (-x - (P.level k - (1 - P.l1) * P.level k * z)) 0 ∂ν) /
          (P.weight k * (1 - P.l1) * P.level k)
        - z ^ (P.theta k + 1) / (P.theta k + 1)| ≤ η) hprof
  exact ⟨e, fun k => (hepos k).le, he, hev⟩

/-- **(b) The slow scale.**  The auxiliary sequence grows slowly enough that the
band errors times its square still vanish, and the scale is then fixed by the
paper's normalisation `R_k² ω_k = G(0,0) L_k`.

The slow property is stated in the form `exists_slow_weights` actually provides:
domination by the EXPLICIT error sequence `e`, pointwise in `k`.  The first version
asked instead that `L_k²f_k → 0` for every `f` tending to zero, which is false for
`f = 1/L`, and an agent derived `False` from it.  A conclusion that implies `False`
is worse than an unprovable one, because everything downstream inherits it. -/
theorem exists_bandScale (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (e : ℕ → ℝ) (he0 : ∀ k, 0 ≤ e k) (he : Tendsto e atTop (𝓝 0)) :
    ∃ (L R : ℕ → ℝ),
      (∀ k, 0 < L k) ∧ Tendsto L atTop atTop ∧
      StrictMono R ∧ Tendsto R atTop atTop ∧
      (∀ k : ℕ, R k ^ 2 * P.weight k = green d 0 0 * L k) ∧
      ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) → (∀ k, f k ≤ e k) →
        Tendsto (fun k => L k ^ 2 * f k) atTop (𝓝 0) := by
  obtain ⟨L₀, hL₀pos, hL₀top, hL₀slow⟩ := exists_slow_weights e he0 he
  obtain ⟨L, hLpos, hLle, hLmono, hLtop⟩ := bandStep2_monotone_minorant L₀ hL₀pos hL₀top
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hωpos := P.weight_pos
  have hωlt : ∀ k, P.weight (k + 1) < P.weight k := by
    intro k
    unfold BandParameters.weight
    refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ?_) P.hc0
    have h1 : P.level k < P.level (k + 1) := by
      have h0 : 0 < P.A ^ k := P.level_pos k
      unfold BandParameters.level
      rw [pow_succ]
      nlinarith [P.hA]
    linarith
  have hω0 : Tendsto (fun k => P.weight k) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp P.level_tendsto)).const_mul P.c0
    simpa [Function.comp_def, BandParameters.weight] using h
  refine ⟨L, fun k => Real.sqrt (green d 0 0 * L k / P.weight k), hLpos, hLtop, ?_, ?_, ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ fun k => ?_
    refine Real.sqrt_lt_sqrt (by have := hLpos k; have := hωpos k; positivity) ?_
    rw [div_lt_div_iff₀ (hωpos k) (hωpos (k + 1))]
    have h1 : green d 0 0 * L k * P.weight (k + 1) < green d 0 0 * L k * P.weight k :=
      mul_lt_mul_of_pos_left (hωlt k) (mul_pos hG (hLpos k))
    have h2 : green d 0 0 * L k * P.weight k ≤ green d 0 0 * L (k + 1) * P.weight k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hLmono (Nat.le_succ k)) hG.le)
        (hωpos k).le
    linarith
  · refine Real.tendsto_sqrt_atTop.comp ?_
    refine tendsto_atTop_mono' _ ?_ (hLtop.const_mul_atTop hG)
    filter_upwards [hω0.eventually_lt_const one_pos] with k hk
    have h := hωpos k
    rw [le_div_iff₀ h]
    nlinarith [mul_pos hG (hLpos k)]
  · intro k
    have h := hωpos k
    rw [Real.sq_sqrt (by have := hLpos k; positivity), div_mul_cancel₀ _ h.ne']
  · intro f hf hfe
    refine squeeze_zero (fun k => mul_nonneg (sq_nonneg _) (hf k)) (fun k => ?_)
      (hL₀slow f hf hfe)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hLpos k).le (hLle k) 2) (hf k)

/-- **The summed increments stay below `T L`.**  From `τ` to `n + 1 ≤ T R²` steps, each of size
at most `ω/(G(1+1/θ)) + ηω ≤ ω/G`, and `R² ω = G L`. -/
private theorem bandStep2_sum_arith {N R L ω η θ G T : ℝ} (hG : 0 < G) (hT : 0 < T)
    (hω : 0 < ω) (hθ1 : 1 ≤ θ) (hθ2 : θ ≤ 2) (hη0 : 0 ≤ η) (hη : η < 1 / (3 * G))
    (hN : N ≤ T * R ^ 2) (hRL : R ^ 2 * ω = G * L) :
    N * (ω / (G * (1 + 1 / θ)) + η * ω) ≤ T * L := by
  have hθp : 0 < θ := by linarith
  have h1 : (1 : ℝ) / 2 ≤ 1 / θ := one_div_le_one_div_of_le hθp hθ2
  have h2 : 3 / 2 * G ≤ G * (1 + 1 / θ) := by nlinarith
  have hc' : ω / (G * (1 + 1 / θ)) ≤ 2 / (3 * G) * ω := by
    calc ω / (G * (1 + 1 / θ)) ≤ ω / (3 / 2 * G) :=
          div_le_div_of_nonneg_left hω.le (by positivity) h2
      _ = 2 / (3 * G) * ω := by field_simp
  have h3 : ω / (G * (1 + 1 / θ)) + η * ω ≤ (1 / G) * ω := by
    have h5 : 2 / (3 * G) * ω + η * ω ≤ 2 / (3 * G) * ω + 1 / (3 * G) * ω :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hη.le hω.le)
    have h6 : 2 / (3 * G) * ω + 1 / (3 * G) * ω = 1 / G * ω := by field_simp; ring
    linarith
  calc N * (ω / (G * (1 + 1 / θ)) + η * ω) ≤ (T * R ^ 2) * ((1 / G) * ω) :=
        mul_le_mul hN h3 (add_nonneg (by positivity) (mul_nonneg hη0 hω.le)) (by positivity)
    _ = T * L := by
        have : T * R ^ 2 * (1 / G * ω) = T / G * (R ^ 2 * ω) := by ring
        rw [this, hRL]
        field_simp

/-- **The coordinate stays positive.**  The step `z - z'` is `c z^{ϑ+1}` to within `eω`, and
`c z^{ϑ+1} ≤ z/2` while `eω < z/2` because `z ≥ z^ϑ ≥ 1/(2TL)` and `L² e < 1/(4T)`. -/
private theorem bandStep2_next_pos {z z' ω e G T L θ : ℝ} (hG : 0 < G) (hT : 0 < T)
    (hL1 : 1 ≤ L) (hz0 : 0 < z) (hz1 : z ≤ 1 / 2) (hθ1 : 1 ≤ θ)
    (hzθ : 1 / (2 * T * L) ≤ z ^ θ) (hω : 0 < ω) (hωG : ω < G) (hω1 : ω < 1)
    (he0 : 0 ≤ e) (hLe : L ^ 2 * e < 1 / (4 * T))
    (hmm : z - z' - ω / (G * (θ + 1)) * z ^ (θ + 1) ≤ e * ω) : 0 < z' := by
  have hLpos : 0 < L := by linarith
  have hz1' : z ≤ 1 := hz1.trans (by norm_num)
  have hzθle : z ^ θ ≤ z := by
    have h := Real.rpow_le_rpow_of_exponent_ge hz0 hz1' hθ1
    simpa using h
  have hzθ1 : z ^ θ ≤ 1 := hzθle.trans hz1'
  have hZ : z ^ (θ + 1) = z ^ θ * z := Real.rpow_add_one hz0.ne' _
  have hcz : ω / (G * (θ + 1)) * z ^ (θ + 1) ≤ z / 2 := by
    have h1 : ω / (G * (θ + 1)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h2 : z ^ (θ + 1) ≤ z := by
      rw [hZ]
      nlinarith
    have h3 : 0 ≤ ω / (G * (θ + 1)) := by positivity
    nlinarith
  have hez : e * ω < z / 2 := by
    have h1 : 4 * T * L * e < 1 := by
      have h2 : L * e ≤ L ^ 2 * e := by
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hL1) hLpos.le) he0]
      have h3 := hLe
      rw [lt_div_iff₀ (by positivity)] at h3
      nlinarith [mul_pos hT hLpos]
    have h2 : e < 1 / (4 * T * L) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    have h3 : 1 / (2 * T * L) ≤ z := hzθ.trans hzθle
    have h4 : 1 / (4 * T * L) = 1 / (2 * T * L) / 2 := by
      field_simp
      ring
    have h5 : e * ω ≤ e := by nlinarith
    linarith
  linarith

/-- **The index range with the coordinate strictly positive.**  This is the form the
consumers need: the profile `z^{-ϑ}` of a coordinate at `0` is `0`, so the barrier alone
does not keep the coordinate off `0`, and the one-step increment wants `z^ϑ ≥ 1/(2TL)`.
The induction runs on `u i = z_i^{-ϑ}` when `z_i > 0` and on a value above the barrier
otherwise, so that `u i ≤ 2TL` carries positivity along. -/
private theorem bandStep2_range_pos (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z)
    (e L R : ℕ → ℝ) (he0 : ∀ k, 0 ≤ e k)
    (hLpos : ∀ k, 0 < L k) (hL : Tendsto L atTop atTop)
    (hslow : ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) → (∀ k, f k ≤ e k) →
      Tendsto (fun k => L k ^ 2 * f k) atTop (𝓝 0))
    (hmod : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
        |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
            - P.weight k / (green d 0 0 * (P.theta k + 1))
              * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
          ≤ e k * P.weight k)
    (hRL : ∀ k : ℕ, R k ^ 2 * P.weight k = green d 0 0 * L k)
    (T : ℝ) (hT : 0 < T) :
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * R k ^ 2 → ∀ i : ℕ,
      bandTau P hd ν hint hmean hnondeg k ≤ i → i ≤ n →
        0 < bandCoordSeq P d ν k i ∧ bandCoordSeq P d ν k i ≤ 1 / 2 ∧
          bandCoordSeq P d ν k i ^ (-(P.theta k)) ≤ 2 * T * L k := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hpos := bandStep2_integrable_pos ν hint
  have hθ1 : ∀ k, 1 ≤ P.theta k := fun k => (P.htheta k).1
  have hθ2 : ∀ k, P.theta k ≤ 2 := fun k => (P.htheta k).2
  have hmono : Monotone (fun n : ℕ => meanOdometer (centeredMassLaw d ν) n / green d 0 0) :=
    fun m n h => div_le_div_of_nonneg_right (meanOdometer_mono hd1 ν hpos h) hG.le
  obtain ⟨η, hη, hinc⟩ := bandProfile_increment P hd ν hθ1 hθ2 L hLpos T hT e he0
    (hslow e he0 (fun _ => le_rfl)) hmod
  have hω0 := bandStep2_weight_tendsto P
  filter_upwards [hinc, hmod, bandStep2_hitting_coord P hd ν hint hmean hnondeg,
    hL.eventually_ge_atTop (max 1 (16 / T)),
    hη.eventually_lt_const (show (0 : ℝ) < 1 / (3 * green d 0 0) by positivity),
    hω0.eventually_lt_const (show (0 : ℝ) < min 1 (green d 0 0) by positivity),
    (hslow e he0 (fun _ => le_rfl)).eventually_lt_const (show (0 : ℝ) < 1 / (4 * T) by positivity)]
    with k hk hmk hcoord hLk hηk hωk hLe n hn i hτi hin
  obtain ⟨hτ1, hτ2, hτy⟩ := hcoord
  have h1l : 0 < 1 - P.l1 := by linarith [P.hl1.2]
  have ha : 0 < P.level k := P.level_pos k
  have hW : 0 < (1 - P.l1) * P.level k := mul_pos h1l ha
  have hω : 0 < P.weight k := P.weight_pos k
  have hωG : P.weight k < green d 0 0 := lt_of_lt_of_le hωk (min_le_right _ _)
  have hω1 : P.weight k < 1 := lt_of_lt_of_le hωk (min_le_left _ _)
  have hLpk := hLpos k
  have hL1 : 1 ≤ L k := le_trans (le_max_left _ _) hLk
  have hTL : 16 ≤ T * L k := by
    have h := le_trans (le_max_right _ _) hLk
    rw [div_le_iff₀ hT] at h
    linarith
  have hanti : Antitone (fun j => bandCoordSeq P d ν k j) :=
    bandLevelCoord_antitone P.l1 P.level
      (fun n => meanOdometer (centeredMassLaw d ν) n / green d 0 0) k hW hmono
  set τ := bandTau P hd ν hint hmean hnondeg k with hτdef
  have hhalf : ∀ j, τ ≤ j → bandCoordSeq P d ν k j ≤ 1 / 2 := fun j hj => (hanti hj).trans hτ2
  have hTLpos : 0 < 2 * T * L k := by positivity
  -- the barrier is kept from `τ` to `n`
  have key := forall_le_of_step_offset
    (fun j => if 0 < bandCoordSeq P d ν k j then bandCoordSeq P d ν k j ^ (-(P.theta k))
      else 2 * T * L k + 1)
    (fun _ => 2 * T * L k) τ n ?h0 ?hstep i hτi hin
  · -- the conclusion at `i`
    have h : (if 0 < bandCoordSeq P d ν k i then bandCoordSeq P d ν k i ^ (-(P.theta k))
        else 2 * T * L k + 1) ≤ 2 * T * L k := key
    by_cases hp : 0 < bandCoordSeq P d ν k i
    · rw [if_pos hp] at h
      exact ⟨hp, hhalf i hτi, h⟩
    · rw [if_neg hp] at h
      linarith
  case h0 =>
    show (if 0 < bandCoordSeq P d ν k τ then bandCoordSeq P d ν k τ ^ (-(P.theta k))
        else 2 * T * L k + 1) ≤ 2 * T * L k
    rw [if_pos (by linarith : 0 < bandCoordSeq P d ν k τ)]
    calc _ ≤ 16 := hτy
      _ ≤ 2 * T * L k := by nlinarith [mul_pos hT hLpk]
  case hstep =>
    intro m hτm hmn hIH
    have hIH' : ∀ j, τ ≤ j → j ≤ m → 0 < bandCoordSeq P d ν k j ∧
        bandCoordSeq P d ν k j ^ (-(P.theta k)) ≤ 2 * T * L k := by
      intro j hj hjm
      have h : (if 0 < bandCoordSeq P d ν k j then bandCoordSeq P d ν k j ^ (-(P.theta k))
          else 2 * T * L k + 1) ≤ 2 * T * L k := hIH j hj hjm
      by_cases hp : 0 < bandCoordSeq P d ν k j
      · rw [if_pos hp] at h
        exact ⟨hp, h⟩
      · rw [if_neg hp] at h
        linarith
    -- on `[τ, m]` the coordinate is in the range of the increment
    have hzj : ∀ j, τ ≤ j → j ≤ m → bandCoordSeq P d ν k j ∈ Icc (0 : ℝ) (1 / 2) ∧
        1 / (2 * T * L k) ≤ bandCoordSeq P d ν k j ^ P.theta k := by
      intro j hj hjm
      obtain ⟨hp, hy⟩ := hIH' j hj hjm
      refine ⟨⟨hp.le, hhalf j hj⟩, ?_⟩
      have hzθ : 0 < bandCoordSeq P d ν k j ^ P.theta k := Real.rpow_pos_of_pos hp _
      rw [Real.rpow_neg hp.le] at hy
      have h := (inv_le_comm₀ hzθ hTLpos).mp hy
      simpa [one_div] using h
    -- summing the increments from `τ` to `m + 1`
    have hsum := abs_sub_sum_le_offset
      (fun j => bandCoordSeq P d ν k j ^ (-(P.theta k)))
      (P.weight k / (green d 0 0 * (1 + 1 / P.theta k))) (η k * P.weight k) τ (m + 1)
      (by omega)
      (fun j hj hjm => hk j (hzj j hj (by omega)).1 (hzj j hj (by omega)).2)
    have hθk := hθ1 k
    have hθk2 := hθ2 k
    have hcast : ((m + 1 - τ : ℕ) : ℝ) ≤ T * R k ^ 2 := by
      have h1 : ((m + 1 - τ : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (by omega : m + 1 - τ ≤ n)
      exact h1.trans hn
    have hη0 : 0 ≤ η k := by
      have h := (abs_nonneg _).trans (hk τ (hzj τ le_rfl hτm).1 (hzj τ le_rfl hτm).2)
      by_contra hneg
      have := mul_neg_of_neg_of_pos (not_le.mp hneg) hω
      linarith
    -- the profile at `m + 1` stays below the barrier
    have hy1 : bandCoordSeq P d ν k (m + 1) ^ (-(P.theta k)) ≤ 2 * T * L k := by
      have h1 := (abs_le.mp hsum).2
      have h2 := bandStep2_sum_arith hG hT hω hθk hθk2 hη0 hηk hcast (hRL k)
      have h7 : bandCoordSeq P d ν k τ ^ (-(P.theta k)) ≤ 16 := hτy
      have h1' : bandCoordSeq P d ν k (m + 1) ^ (-(P.theta k))
          - bandCoordSeq P d ν k τ ^ (-(P.theta k))
          - ((m + 1 - τ : ℕ) : ℝ) * (P.weight k / (green d 0 0 * (1 + 1 / P.theta k)))
          ≤ ((m + 1 - τ : ℕ) : ℝ) * (η k * P.weight k) := h1
      rw [mul_add] at h2
      linarith
    -- the coordinate at `m + 1` stays positive
    have hpos1 : 0 < bandCoordSeq P d ν k (m + 1) := by
      obtain ⟨⟨hz0, hz1⟩, hzθ⟩ := hzj m hτm le_rfl
      exact bandStep2_next_pos hG hT hL1 (hIH' m hτm le_rfl).1 hz1 hθk hzθ hω hωG hω1 (he0 k)
        hLe (abs_le.mp (hmk m ⟨hz0, hz1⟩)).2
    show (if 0 < bandCoordSeq P d ν k (m + 1) then bandCoordSeq P d ν k (m + 1) ^ (-(P.theta k))
        else 2 * T * L k + 1) ≤ 2 * T * L k
    rw [if_pos hpos1]
    exact hy1

set_option linter.unusedVariables false in
/-- **(d) The two-sided index range.**  Past the hitting index and out to the
horizon, the coordinate stays in `Icc 0 (1/2)` AND its profile stays below the
barrier `2TL_k`.

The conclusion is two-sided because the one-step increment needs both ends: the
lower end is the barrier itself, and the upper end `z ≤ 1/2` is the paper's own
range, outside which the exponential term is not controlled.  Stating only the
barrier, as the first version did, leaves the sign of the coordinate free and a
negative coordinate satisfies it.

Proof.  `forall_le_of_step_offset` with `u i = z_{k,i}^{-θ_k}` and `B _ = 2TL_k`,
base case `bandProfile_hitting_le`, step case `bandProfile_increment` at the index
`i` alone.  That is legitimate and not circular: the induction hypothesis supplies
the bound at every index up to `n` and the step uses it only there. -/
theorem bandProfile_range (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hgap : P.lam0 < θ₀ / LatticeProb.greenRatioSup d)
    (hprof : BandIntegratedProfile P ν) (hbp : BandProfile P ν)
    (hdens : BandDensity P ν) (hlow : BandLowerIsolation P ν)
    (e L R : ℕ → ℝ) (he0 : ∀ k, 0 ≤ e k) (he : Tendsto e atTop (𝓝 0))
    (hLpos : ∀ k, 0 < L k) (hL : Tendsto L atTop atTop)
    (hslow : ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) → (∀ k, f k ≤ e k) →
      Tendsto (fun k => L k ^ 2 * f k) atTop (𝓝 0))
    (hmod : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
        |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
            - P.weight k / (green d 0 0 * (P.theta k + 1))
              * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
          ≤ e k * P.weight k)
    (hRL : ∀ k : ℕ, R k ^ 2 * P.weight k = green d 0 0 * L k)
    (T : ℝ) (hT : 0 < T) :
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * R k ^ 2 → ∀ i : ℕ,
      bandTau P hd ν hint hmean hnondeg k ≤ i → i ≤ n →
        bandCoordSeq P d ν k i ∈ Icc (0 : ℝ) (1 / 2) ∧
          bandCoordSeq P d ν k i ^ (-(P.theta k)) ≤ 2 * T * L k := by
  filter_upwards [bandStep2_range_pos P hd ν hint hmean hnondeg e L R he0 hLpos hL hslow hmod
    hRL T hT] with k hk n hn i hτi hin
  obtain ⟨h1, h2, h3⟩ := hk n hn i hτi hin
  exact ⟨⟨h1.le, h2⟩, h3⟩

/-- **The hitting index is at most a constant over the weight.**  Past the hitting index
the increment of the frozen level is at least a constant times `ω_k a_k`, by the modulus
at the coordinate `z_{k,τ_k} ∈ [1/4, 1/2]`; before it the increments are larger, because
the mean odometer is concave, so the hitting time is at most `(1/c + 1)/ω_k`. -/
private theorem bandStep2_tau_le (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hmod : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
        |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
            - P.weight k / (green d 0 0 * (P.theta k + 1))
              * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
          ≤ e k * P.weight k) :
    ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
      ((bandTau P hd ν hint hmean hnondeg k : ℕ) : ℝ) ≤ C / P.weight k := by
  have hd1 : 1 ≤ d := by omega
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hpos := bandStep2_integrable_pos ν hint
  have hmono : Monotone (fun n : ℕ => meanOdometer (centeredMassLaw d ν) n / green d 0 0) :=
    fun m n h => div_le_div_of_nonneg_right (meanOdometer_mono hd1 ν hpos h) hG.le
  have hanti := bandStep2_incr_anti hd ν hint hmean
  have hb0 : meanOdometer (centeredMassLaw d ν) 0 / green d 0 0 = 0 := by
    rw [meanOdometer_zero d ν, zero_div]
  have h1l : 0 < 1 - P.l1 := by linarith [P.hl1.2]
  set c : ℝ := (1 - P.l1) / (384 * green d 0 0) with hcdef
  have hc : 0 < c := by positivity
  refine ⟨1 / c + 1, ?_⟩
  filter_upwards [hmod, bandStep2_hitting_coord P hd ν hint hmean hnondeg,
    he.eventually_lt_const (show (0 : ℝ) < 1 / (384 * green d 0 0) by positivity),
    (bandStep2_weight_tendsto P).eventually_lt_const one_pos] with k hmk hcoord hek hωk
  have ha : 0 < P.level k := P.level_pos k
  have hW : 0 < (1 - P.l1) * P.level k := mul_pos h1l ha
  have hω : 0 < P.weight k := P.weight_pos k
  have hex := bandHitting_exists_sandpile P hd ν hint hmean hnondeg k
  set τ := Nat.find hex with hτdef
  have hτ1 : 1 / 4 ≤ bandCoordSeq P d ν k τ := hcoord.1
  have hτ2 : bandCoordSeq P d ν k τ ≤ 1 / 2 := hcoord.2.1
  have hτspec : P.level k - (1 - P.l1) * P.level k / 2
      ≤ meanOdometer (centeredMassLaw d ν) τ / green d 0 0 := Nat.find_spec hex
  have hz : bandCoordSeq P d ν k τ ∈ Icc (0 : ℝ) (1 / 2) :=
    ⟨by linarith, hτ2⟩
  -- the increment at `τ`
  have hθ := P.htheta k
  have hzpos : 0 < bandCoordSeq P d ν k τ := by linarith
  have hz1 : bandCoordSeq P d ν k τ ≤ 1 := by linarith
  have hlow4 : ((1 : ℝ) / 4) ^ (3 : ℝ) ≤ bandCoordSeq P d ν k τ ^ (P.theta k + 1) := by
    calc ((1 : ℝ) / 4) ^ (3 : ℝ) ≤ ((1 : ℝ) / 4) ^ (P.theta k + 1) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith [hθ.2])
      _ ≤ bandCoordSeq P d ν k τ ^ (P.theta k + 1) :=
          Real.rpow_le_rpow (by norm_num) hτ1 (by linarith [hθ.1])
  have h64 : ((1 : ℝ) / 4) ^ (3 : ℝ) = 1 / 64 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [h64] at hlow4
  have hmm := (abs_le.mp (hmk τ hz)).1
  have hθp : 0 < P.theta k + 1 := by linarith [hθ.1]
  have hcc : P.weight k / (3 * green d 0 0)
      ≤ P.weight k / (green d 0 0 * (P.theta k + 1)) :=
    div_le_div_of_nonneg_left hω.le (mul_pos hG hθp) (by nlinarith [hθ.2, hG])
  have hccz : P.weight k / (3 * green d 0 0) * (1 / 64)
      ≤ P.weight k / (green d 0 0 * (P.theta k + 1))
        * bandCoordSeq P d ν k τ ^ (P.theta k + 1) :=
    mul_le_mul hcc hlow4 (by norm_num) (div_nonneg hω.le (mul_pos hG hθp).le)
  have hew : e k * P.weight k ≤ 1 / (384 * green d 0 0) * P.weight k :=
    mul_le_mul_of_nonneg_right hek.le hω.le
  have hdec : P.weight k / (384 * green d 0 0)
      ≤ bandCoordSeq P d ν k τ - bandCoordSeq P d ν k (τ + 1) := by
    have h1 : P.weight k / (3 * green d 0 0) * (1 / 64) = P.weight k / (192 * green d 0 0) := by
      field_simp; ring
    have h2 : 1 / (384 * green d 0 0) * P.weight k = P.weight k / (384 * green d 0 0) := by
      field_simp
    have h3 : P.weight k / (192 * green d 0 0) = 2 * (P.weight k / (384 * green d 0 0)) := by
      field_simp; ring
    linarith
  have hsub := bandLevelCoord_sub_succ (l1 := P.l1) P.level
    (fun n => meanOdometer (centeredMassLaw d ν) n / green d 0 0) k τ
  have hinc_τ : c * (P.weight k * P.level k)
      ≤ meanOdometer (centeredMassLaw d ν) (τ + 1) / green d 0 0
        - meanOdometer (centeredMassLaw d ν) τ / green d 0 0 := by
    have h1 : meanOdometer (centeredMassLaw d ν) (τ + 1) / green d 0 0
        - meanOdometer (centeredMassLaw d ν) τ / green d 0 0
        = (1 - P.l1) * P.level k * (bandCoordSeq P d ν k τ - bandCoordSeq P d ν k (τ + 1)) := by
      have h : bandCoordSeq P d ν k τ - bandCoordSeq P d ν k (τ + 1)
          = (meanOdometer (centeredMassLaw d ν) (τ + 1) / green d 0 0
            - meanOdometer (centeredMassLaw d ν) τ / green d 0 0)
              / ((1 - P.l1) * P.level k) := hsub
      rw [h]
      field_simp
    rw [h1]
    have h2 : c * (P.weight k * P.level k)
        = (1 - P.l1) * P.level k * (P.weight k / (384 * green d 0 0)) := by
      rw [hcdef]
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left hdec hW.le
  refine bandHittingTime_le P.hl1.1.le P.hl1.2.le hc P.level P.weight
    (fun n => meanOdometer (centeredMassLaw d ν) n / green d 0 0) k ha hω hωk.le hb0 hmono
    ?_ hex
  intro n hn
  have hn' : meanOdometer (centeredMassLaw d ν) n / green d 0 0
      < P.level k - (1 - P.l1) * P.level k / 2 := hn
  have hnτ : n ≤ τ := by
    by_contra hlt
    have hlt := not_le.mp hlt
    have h := hmono hlt.le
    have h' : meanOdometer (centeredMassLaw d ν) τ / green d 0 0
        ≤ meanOdometer (centeredMassLaw d ν) n / green d 0 0 := h
    linarith
  have hai : meanOdometer (centeredMassLaw d ν) (τ + 1) / green d 0 0
      - meanOdometer (centeredMassLaw d ν) τ / green d 0 0
      ≤ meanOdometer (centeredMassLaw d ν) (n + 1) / green d 0 0
      - meanOdometer (centeredMassLaw d ν) n / green d 0 0 := hanti hnτ
  linarith

/-- **The summed profile at a single horizon.**  `scaledProfile_bound_family` asks for the
increment bound at every horizon with ONE error sequence, but only ever reads it at the
horizon `T` of its conclusion; at the sandpile law the error sequence of the one-step
increment depends on that horizon, so this is the same argument with the hypothesis read
at `T` alone. -/
private theorem bandStep2_scaledProfile_bound
    (y : ℕ → ℕ → ℝ) (R L : ℕ → ℝ) (ω η kap : ℕ → ℝ) (s : ℕ → ℕ) (κ0 : ℝ) (hκ0 : 0 < κ0)
    (hkap : ∀ k, κ0 ≤ kap k)
    (G00 : ℝ) (hG : 0 < G00)
    (hRL : ∀ k : ℕ, R k ^ 2 * ω k = G00 * L k)
    (hL : Tendsto L atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hη : Tendsto η atTop (𝓝 0))
    (hs : Tendsto (fun k : ℕ => ((s k : ℕ) : ℝ) / R k ^ 2) atTop (𝓝 0))
    (hys : ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, |y k (s k)| ≤ C)
    (T : ℝ)
    (hinc : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
        (n : ℝ) ≤ T * R k ^ 2 → ∀ i : ℕ, s k ≤ i → i < n →
          |(y k (i + 1) - y k i) - ω k / (G00 * kap k)| ≤ η k * ω k) :
    ∀ δ : ℝ, 0 < δ → δ < T → ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ Set.Icc δ T,
        |y k (⌊t * R k ^ 2⌋₊) / L k - t / kap k| ≤ b k := by
  intro δ hδ hδT
  obtain ⟨C, hC⟩ := hys
  have hkappos : ∀ k, 0 < kap k := fun k => lt_of_lt_of_le hκ0 (hkap k)
  have hLpos : ∀ᶠ k : ℕ in atTop, 0 < L k := hL.eventually_gt_atTop 0
  have hRpos : ∀ᶠ k : ℕ in atTop, 0 < R k := hR.eventually_gt_atTop 0
  have hωpos : ∀ᶠ k : ℕ in atTop, 0 ≤ ω k := by
    filter_upwards [hLpos, hRpos] with k hLk hRk
    have h1 : 0 < R k ^ 2 * ω k := by rw [hRL k]; positivity
    nlinarith [sq_pos_of_pos hRk]
  have hηabs : Tendsto (fun k : ℕ => |η k|) atTop (𝓝 0) := by
    simpa using hη.abs
  have hR2 : Tendsto (fun k : ℕ => R k ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hR
  have hone : Tendsto (fun k : ℕ => 1 / R k ^ 2) atTop (𝓝 0) := hR2.const_div_atTop 1
  have hsum : Tendsto (fun k : ℕ => 1 / R k ^ 2 + ((s k : ℕ) : ℝ) / R k ^ 2) atTop (𝓝 0) := by
    simpa using hone.add hs
  have hsfit0 : ∀ᶠ k : ℕ in atTop, 1 / R k ^ 2 + ((s k : ℕ) : ℝ) / R k ^ 2 ≤ δ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsum δ hδ
    filter_upwards [eventually_ge_atTop N] with k hk
    have hd := hN k hk
    rw [Real.dist_eq, sub_zero] at hd
    exact le_of_lt (lt_of_abs_lt hd)
  have hsfit : ∀ᶠ k : ℕ in atTop, (1 : ℝ) + ((s k : ℕ) : ℝ) ≤ δ * R k ^ 2 := by
    filter_upwards [hsfit0, hRpos] with k h hRk
    have hR2k : 0 < R k ^ 2 := pow_pos hRk 2
    have heq : 1 / R k ^ 2 + ((s k : ℕ) : ℝ) / R k ^ 2
        = (1 + ((s k : ℕ) : ℝ)) / R k ^ 2 := by ring
    rw [heq, div_le_iff₀ hR2k] at h
    linarith
  have hpt : ∀ᶠ k : ℕ in atTop, ∀ t ∈ Set.Icc δ T,
      |y k (⌊t * R k ^ 2⌋₊) / L k - t / kap k| ≤
        C / L k + (1 + ((s k : ℕ) : ℝ)) / (κ0 * R k ^ 2) + |η k| * G00 * T := by
    filter_upwards [hLpos, hRpos, hωpos, hC, hsfit, hinc] with
      k hLk hRk hωk hCk hsfitk hinc_k
    intro t ht
    have ht0 : t ∈ Set.Icc (0 : ℝ) T := ⟨le_trans hδ.le ht.1, ht.2⟩
    have hR2k : 0 < R k ^ 2 := pow_pos hRk 2
    have hfl : (⌊t * R k ^ 2⌋₊ : ℝ) ≤ t * R k ^ 2 :=
      Nat.floor_le (mul_nonneg ht0.1 (sq_nonneg _))
    have hflT : (⌊t * R k ^ 2⌋₊ : ℝ) ≤ T * R k ^ 2 :=
      le_trans hfl (mul_le_mul_of_nonneg_right ht0.2 (sq_nonneg _))
    have hslt : ((s k : ℕ) : ℝ) < (⌊t * R k ^ 2⌋₊ : ℝ) := by
      have h1 : t * R k ^ 2 - 1 < (⌊t * R k ^ 2⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one (t * R k ^ 2)
        linarith
      have h2 : δ * R k ^ 2 ≤ t * R k ^ 2 :=
        mul_le_mul_of_nonneg_right ht.1 hR2k.le
      linarith
    have hsn : s k ≤ ⌊t * R k ^ 2⌋₊ := le_of_lt (by exact_mod_cast hslt)
    have hband : ∀ i : ℕ, s k ≤ i → i < ⌊t * R k ^ 2⌋₊ →
        |(y k (i + 1) - y k i) - ω k / (G00 * kap k)| ≤ |η k| * ω k := by
      intro i hi hi'
      exact le_trans (hinc_k ⌊t * R k ^ 2⌋₊ hflT i hi hi')
        (mul_le_mul_of_nonneg_right (le_abs_self _) hωk)
    have hmain := abs_profile_le_of_increments_offset (y k) R L ω (kap k) G00 C (|η k|) T k
      (s k) t (hkappos k) hG hLk (abs_nonneg _) hωk (hRL k) hsn hCk hband ht0
    refine hmain.trans ?_
    have hle : (1 + ((s k : ℕ) : ℝ)) / (kap k * R k ^ 2)
        ≤ (1 + ((s k : ℕ) : ℝ)) / (κ0 * R k ^ 2) := by
      refine div_le_div_of_nonneg_left (by positivity) (mul_pos hκ0 hR2k) ?_
      exact mul_le_mul_of_nonneg_right (hkap k) hR2k.le
    linarith
  exact ⟨fun k => C / L k + (1 + ((s k : ℕ) : ℝ)) / (κ0 * R k ^ 2) + |η k| * G00 * T,
    tendsto_bound_of_scaled_offset R L (fun k => |η k|) s C κ0 G00 T hκ0 hR hL hηabs hs, hpt⟩

set_option linter.unusedVariables false in
/-- **(e) The scaled profile.**  On compact time ranges bounded away from zero the
profile divided by the auxiliary sequence is the time divided by `κ_k`.

Proof.  `scaledProfile_bound_family` at `G00 := green d 0 0`, which is forced: the
one-step increment is stated with that constant, and at any other the conclusion
is false.  Its `hys` is `bandTau_profile_bounded`, its `hs` is
`bandTau_div_scaleSq_tendsto`, and its `hinc` is `bandProfile_increment`, whose
coordinate hypotheses are exactly `bandProfile_range`. -/
theorem bandScaledProfile (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hgap : P.lam0 < θ₀ / LatticeProb.greenRatioSup d)
    (hprof : BandIntegratedProfile P ν) (hbp : BandProfile P ν)
    (hdens : BandDensity P ν) (hlow : BandLowerIsolation P ν)
    (e L R : ℕ → ℝ) (he0 : ∀ k, 0 ≤ e k) (he : Tendsto e atTop (𝓝 0))
    (hLpos : ∀ k, 0 < L k) (hL : Tendsto L atTop atTop)
    (hslow : ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) → (∀ k, f k ≤ e k) →
      Tendsto (fun k => L k ^ 2 * f k) atTop (𝓝 0))
    (hmod : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
        |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
            - P.weight k / (green d 0 0 * (P.theta k + 1))
              * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
          ≤ e k * P.weight k) (hR : Tendsto R atTop atTop)
    (hRL : ∀ k : ℕ, R k ^ 2 * P.weight k = green d 0 0 * L k) :
    ∀ δ T : ℝ, 0 < δ → δ < T → ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc δ T,
        |bandCoordSeq P d ν k ⌊t * R k ^ 2⌋₊ ^ (-(P.theta k)) / L k
            - t / (1 + 1 / P.theta k)| ≤ b k := by
  intro δ T hδ hδT
  have hT : 0 < T := hδ.trans hδT
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hθ1 : ∀ k, 1 ≤ P.theta k := fun k => (P.htheta k).1
  have hθ2 : ∀ k, P.theta k ≤ 2 := fun k => (P.htheta k).2
  obtain ⟨η, hη, hinc⟩ := bandProfile_increment P hd ν hθ1 hθ2 L hLpos T hT e he0
    (hslow e he0 (fun _ => le_rfl)) hmod
  obtain ⟨C, hC⟩ := bandStep2_tau_le P hd ν hint hmean hnondeg e he hmod
  have hs := bandTau_div_scaleSq_tendsto P hd ν hint hmean hnondeg R L hG P.weight_pos hL hRL hC
  refine bandStep2_scaledProfile_bound
    (fun k i => bandCoordSeq P d ν k i ^ (-(P.theta k))) R L (fun k => P.weight k) η
    (fun k => 1 + 1 / P.theta k) (fun k => bandTau P hd ν hint hmean hnondeg k) (3 / 2)
    (by norm_num) ?_ (green d 0 0) hG hRL hL hR hη hs ?_ T ?_ δ hδ hδT
  · intro k
    have h1 : (1 : ℝ) / 2 ≤ 1 / P.theta k := one_div_le_one_div_of_le (by linarith [hθ1 k]) (hθ2 k)
    linarith
  · refine ⟨16, ?_⟩
    filter_upwards [bandStep2_hitting_coord P hd ν hint hmean hnondeg] with k hk
    have h0 : 0 ≤ bandCoordSeq P d ν k (bandTau P hd ν hint hmean hnondeg k) := by
      linarith [hk.1]
    show |bandCoordSeq P d ν k (bandTau P hd ν hint hmean hnondeg k) ^ (-(P.theta k))| ≤ 16
    rw [abs_of_nonneg (Real.rpow_nonneg h0 _)]
    exact hk.2.2
  · filter_upwards [hinc, bandStep2_range_pos P hd ν hint hmean hnondeg e L R he0 hLpos hL hslow
      hmod hRL T hT] with k hk hrange n hn i hτi hin
    obtain ⟨hp, hle, hy⟩ := hrange n hn i hτi hin.le
    have hzθ : 0 < bandCoordSeq P d ν k i ^ P.theta k := Real.rpow_pos_of_pos hp _
    rw [Real.rpow_neg hp.le] at hy
    have hlow := (inv_le_comm₀ hzθ (by have := hLpos k; positivity)).mp hy
    exact hk i ⟨hp.le, hle⟩ (by simpa [one_div] using hlow)

/-- **The threshold event at the sandpile law is the one-site tail at the frozen level.**
The event `{m < -(G ζ(0))}` is a cylinder event at the origin, so its probability is
`ν {-z > m/G}`. -/
private theorem bandStep2_threshold_measure (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (hG : 0 < green d 0 0) (m : ℕ) :
    (centeredMassLaw d ν) {σ | meanOdometer (centeredMassLaw d ν) m <
        -(green d 0 0 * scenery d σ 0)}
      = ν {z : ℝ | -z > meanOdometer (centeredMassLaw d ν) m / green d 0 0} := by
  have hz : {z : ℝ | meanOdometer (centeredMassLaw d ν) m < -(green d 0 0 * z)}
      = {z : ℝ | -z > meanOdometer (centeredMassLaw d ν) m / green d 0 0} := by
    ext z
    simp only [Set.mem_setOf_eq, gt_iff_lt]
    rw [div_lt_iff₀ hG]
    constructor <;> intro h <;> linarith
  have hmz : MeasurableSet {z : ℝ | meanOdometer (centeredMassLaw d ν) m < -(green d 0 0 * z)} := by
    have hm : Measurable fun z : ℝ => -(green d 0 0 * z) := by fun_prop
    exact measurableSet_lt measurable_const hm
  have hmeas : MeasurableSet {ζ : Site d → ℝ |
      meanOdometer (centeredMassLaw d ν) m < -(green d 0 0 * ζ 0)} := by
    have hm : Measurable fun ζ : Site d → ℝ => -(green d 0 0 * ζ 0) := by fun_prop
    exact measurableSet_lt measurable_const hm
  have hset : {σ : Site d → ℝ | meanOdometer (centeredMassLaw d ν) m
        < -(green d 0 0 * scenery d σ 0)}
      = scenery d ⁻¹' {ζ : Site d → ℝ |
          meanOdometer (centeredMassLaw d ν) m < -(green d 0 0 * ζ 0)} := rfl
  rw [hset, centeredMassLaw_scenery_preimage d ν hd hmeas]
  have hiid : (LatticeProb.iidLaw d ν).map (fun ζ : Site d → ℝ => ζ 0) = ν :=
    Measure.infinitePi_map_eval (fun _ : Site d => ν) 0
  have hpre : {ζ : Site d → ℝ | meanOdometer (centeredMassLaw d ν) m < -(green d 0 0 * ζ 0)}
      = (fun ζ : Site d → ℝ => ζ 0) ⁻¹'
          {z : ℝ | meanOdometer (centeredMassLaw d ν) m < -(green d 0 0 * z)} := rfl
  rw [hpre, ← Measure.map_apply (measurable_pi_apply (0 : Site d)) hmz, hiid, hz]

/-- **The arithmetic of the contact rate.**  With `t = m/R²`, the scaled profile says
`L z^ϑ ≈ κ/t`, the band tail says `μ/ω ≈ z^ϑ`, and `R² ω = G L` turns `(m+1) μ/G` into
`((m+1)/R²) L (μ/ω)`; what is left over is `κ/m`. -/
private theorem bandStep2_rate_arith {r2 m ω G L zθ κ μ ζ ε T : ℝ} (hr2 : 0 < r2) (hm : 0 < m)
    (hG : 0 < G) (hω : 0 < ω) (hRL : r2 * ω = G * L) (hκ0 : 0 < κ) (hκ : κ ≤ 2)
    (hT : m + 1 ≤ T * r2) (hζ : |L * zθ - κ / (m / r2)| ≤ ζ) (hε : |μ / ω - zθ| ≤ ε) :
    |(m + 1) * μ / G - κ| ≤ T * ζ + T * L * ε + 2 / m := by
  have hu0 : 0 ≤ (m + 1) / r2 := by positivity
  have huT : (m + 1) / r2 ≤ T := by rw [div_le_iff₀ hr2]; exact hT
  have hζ0 : 0 ≤ ζ := (abs_nonneg _).trans hζ
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hε
  have hLpos : 0 < L := by
    have h : 0 < G * L := by rw [← hRL]; exact mul_pos hr2 hω
    by_contra hc
    push Not at hc
    nlinarith
  have hL0 : 0 ≤ L := hLpos.le
  have hωe : ω = G * L / r2 := by
    field_simp
    linarith
  have hr2ne : r2 ≠ 0 := hr2.ne'
  have hmne : m ≠ 0 := hm.ne'
  have hGne : G ≠ 0 := hG.ne'
  have hLne : L ≠ 0 := hLpos.ne'
  have key : (m + 1) * μ / G - κ
      = (m + 1) / r2 * (L * zθ - κ / (m / r2)) + (m + 1) / r2 * L * (μ / ω - zθ) + κ / m := by
    rw [hωe]
    field_simp
    ring
  rw [key]
  refine (abs_add_three _ _ _).trans ?_
  have h1 : |(m + 1) / r2 * (L * zθ - κ / (m / r2))| ≤ T * ζ := by
    rw [abs_mul, abs_of_nonneg hu0]
    exact mul_le_mul huT hζ (abs_nonneg _) (hu0.trans huT)
  have h2 : |(m + 1) / r2 * L * (μ / ω - zθ)| ≤ T * L * ε := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hu0 hL0)]
    exact mul_le_mul (mul_le_mul_of_nonneg_right huT hL0) hε (abs_nonneg _)
      (mul_nonneg (hu0.trans huT) hL0)
  have h3 : |κ / m| ≤ 2 / m := by
    rw [abs_of_pos (div_pos hκ0 hm)]
    exact div_le_div_of_nonneg_right hκ hm.le
  linarith

/-- **The exponential moment of the origin-frozen average.**  This is the constant
`C` of the increment estimate, extracted from `exists_avg_originOdometer_exp_bound`. -/
private theorem bandStep2_exp_moment (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hgap : P.lam0 < θ₀ / LatticeProb.greenRatioSup d) :
    ∃ C : ℝ, ∀ n : ℕ,
      ∫ σ, Real.exp (-(P.lam0 * avg (originOdometer (scenery d σ) n) 0)) ∂(centeredMassLaw d ν)
        ≤ C * Real.exp (-(P.lam0 *
          ∫ σ, avg (originOdometer (scenery d σ) n) 0 ∂(centeredMassLaw d ν))) := by
  have hd1 : 1 ≤ d := by omega
  have hlam : 0 < P.lam0 := P.hlam0
  have hB : 0 < LatticeProb.greenRatioSup d := by
    by_contra hn
    have hb := div_nonpos_of_nonneg_of_nonpos hθ₀.le (le_of_not_gt hn)
    linarith
  have hgap' : |-P.lam0| * LatticeProb.greenRatioSup d < θ₀ := by
    rw [abs_neg, abs_of_pos hlam]
    exact (lt_div_iff₀ hB).mp hgap
  obtain ⟨C, hC⟩ := exists_avg_originOdometer_exp_bound External.greenBoundsHigh hd ν hθ₀ hexp
    hB.le (fun z hz => LatticeProb.le_greenRatioSup (by omega) hz) hgap'
  refine ⟨C, fun n => ?_⟩
  have hme := measurable_avg_originOdometer hd1 n
  set M : ℝ := ∫ η, avg (originOdometer η n) 0 ∂LatticeProb.iidLaw d ν with hM
  have hFm : Measurable (fun ζ : Site d → ℝ =>
      Real.exp (-P.lam0 * (avg (originOdometer ζ n) 0 - M))) :=
    Real.measurable_exp.comp ((hme.sub measurable_const).const_mul _)
  have h1 := integral_scenery d ν hd1 hFm.aestronglyMeasurable
  have h2 := integral_scenery d ν hd1
    (F := fun ζ => avg (originOdometer ζ n) 0) hme.aestronglyMeasurable
  have h2' : ∫ σ, avg (originOdometer (scenery d σ) n) 0 ∂(centeredMassLaw d ν) = M := h2
  have hsplit : ∀ σ : Site d → ℝ,
      Real.exp (-(P.lam0 * avg (originOdometer (scenery d σ) n) 0))
        = Real.exp (-(P.lam0 * M)) *
          Real.exp (-P.lam0 * (avg (originOdometer (scenery d σ) n) 0 - M)) := by
    intro σ
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : ∫ σ, Real.exp (-(P.lam0 * avg (originOdometer (scenery d σ) n) 0))
        ∂(centeredMassLaw d ν)
      = Real.exp (-(P.lam0 * M)) * ∫ σ, Real.exp
          (-P.lam0 * (avg (originOdometer (scenery d σ) n) 0 - M)) ∂(centeredMassLaw d ν) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have h5 : ∫ σ, Real.exp (-P.lam0 * (avg (originOdometer (scenery d σ) n) 0 - M))
      ∂(centeredMassLaw d ν) ≤ C := le_trans h1.le (hC n).2
  rw [h3, h2']
  calc Real.exp (-(P.lam0 * M)) * ∫ σ, Real.exp
          (-P.lam0 * (avg (originOdometer (scenery d σ) n) 0 - M)) ∂(centeredMassLaw d ν)
      ≤ Real.exp (-(P.lam0 * M)) * C := mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
    _ = C * Real.exp (-(P.lam0 * M)) := mul_comm _ _

/-- **(f) The contact rate.**

Proof.  `eventually_abs_inv_sub_le` inverts the scaled profile, turning the
profile into the band tail; `BandProfile` evaluates that tail at the coordinate,
which is the threshold probability at `b_{n-1}`; `eventually_abs_ratio_sub_one_le`
absorbs the shift from `n` to `n-1`; and `hRL` converts the auxiliary sequence
into `R_k² ω_k / G(0,0)`, which turns the time into the index and leaves `κ_k`. -/
theorem bandContactRate_of_scaled (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hgap : P.lam0 < θ₀ / LatticeProb.greenRatioSup d)
    (hprof : BandIntegratedProfile P ν) (hbp : BandProfile P ν)
    (hdens : BandDensity P ν) (hlow : BandLowerIsolation P ν)
    (e L R : ℕ → ℝ) (he0 : ∀ k, 0 ≤ e k) (he : Tendsto e atTop (𝓝 0))
    (hLpos : ∀ k, 0 < L k) (hL : Tendsto L atTop atTop)
    (hslow : ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) → (∀ k, f k ≤ e k) →
      Tendsto (fun k => L k ^ 2 * f k) atTop (𝓝 0))
    (hmod : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
        |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
            - P.weight k / (green d 0 0 * (P.theta k + 1))
              * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
          ≤ e k * P.weight k) (hR : Tendsto R atTop atTop)
    (hRL : ∀ k : ℕ, R k ^ 2 * P.weight k = green d 0 0 * L k)
    (T : ℝ) (hT : 0 < T)
    (hmods : BandModuli P d ν e) :
    BandContactRate d ν (fun k => 1 + 1 / P.theta k) R T := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hθ1 : ∀ k, 1 ≤ P.theta k := fun k => (P.htheta k).1
  have hθ2 : ∀ k, P.theta k ≤ 2 := fun k => (P.htheta k).2
  have hκ2 : ∀ k, 1 + 1 / P.theta k ≤ 2 := fun k => by
    have := one_div_le_one_div_of_le zero_lt_one (hθ1 k)
    linarith
  have hκ0 : ∀ k, 0 < 1 + 1 / P.theta k := fun k =>
    add_pos one_pos (one_div_pos.mpr (by linarith [hθ1 k]))
  intro δ hδ η hη
  obtain ⟨hδ0, hδT⟩ := hδ
  have hT : 0 < T := hδ0.trans hδT
  have hδ2 : 0 < δ / 2 := by positivity
  -- the scaled profile on `[δ/2, T]`, the hitting index, and the index range
  obtain ⟨b, hb, hscaled⟩ := bandScaledProfile P hd ν hatom hint hmean hsq hnondeg hθ₀ hexp hgap
    hprof hbp hdens hlow e L R he0 he hLpos hL hslow hmod hR hRL (δ / 2) T hδ2 (by linarith)
  obtain ⟨C, hC⟩ := bandStep2_tau_le P hd ν hint hmean hnondeg e he hmod
  have hs := bandTau_div_scaleSq_tendsto P hd ν hint hmean hnondeg R L hG P.weight_pos hL hRL hC
  have hrange := bandStep2_range_pos P hd ν hint hmean hnondeg e L R he0 hLpos hL hslow hmod
    hRL T hT
  have hR2 : Tendsto (fun k : ℕ => R k ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hR
  -- inverting the scaled profile
  have hB : ∀ᶠ k : ℕ in atTop, ∀ t ∈ Set.Icc (δ / 2) T,
      δ / 4 ≤ t / (1 + 1 / P.theta k) := by
    refine Eventually.of_forall fun k t ht => ?_
    have h1 : t / 2 ≤ t / (1 + 1 / P.theta k) :=
      div_le_div_of_nonneg_left (by linarith [ht.1]) (hκ0 k) (hκ2 k)
    linarith [ht.1]
  have hA : ∀ ζ : ℝ, 0 < ζ → ∀ᶠ k : ℕ in atTop, ∀ t ∈ Set.Icc (δ / 2) T,
      |bandCoordSeq P d ν k ⌊t * R k ^ 2⌋₊ ^ (-(P.theta k)) / L k
        - t / (1 + 1 / P.theta k)| ≤ ζ := by
    intro ζ hζ
    filter_upwards [hscaled, hb.eventually_lt_const hζ] with k hk hbk t ht
    exact (hk t ht).trans hbk.le
  have hinv := eventually_abs_inv_sub_le
    (fun k t => bandCoordSeq P d ν k ⌊t * R k ^ 2⌋₊ ^ (-(P.theta k)) / L k)
    (fun k t => t / (1 + 1 / P.theta k)) (Set.Icc (δ / 2) T) (δ / 4) (by positivity) hB hA
    (η / (3 * T)) (by positivity)
  have hmodsR := hmods.2.1
  filter_upwards [hinv, hrange, hs.eventually_lt_const hδ2, hmodsR,
    (hslow e he0 (fun _ => le_rfl)).eventually_lt_const
      (show (0 : ℝ) < η / (3 * T) by positivity),
    hL.eventually_ge_atTop 1, hR2.eventually_ge_atTop (max (2 / δ) (12 / (δ * η)))]
    with k hinvk hrk hτk htail hLek hLk1 hRk n hn1 hn2
  have h2δ : 2 / δ ≤ R k ^ 2 := le_trans (le_max_left _ _) hRk
  have h12 : 12 / (δ * η) ≤ R k ^ 2 := le_trans (le_max_right _ _) hRk
  have hR2pos : 0 < R k ^ 2 := lt_of_lt_of_le (by positivity) h2δ
  have hδR : 2 ≤ δ * R k ^ 2 := by
    rw [div_le_iff₀ hδ0] at h2δ
    linarith
  have hδηR : 12 ≤ R k ^ 2 * (δ * η) := by
    rw [div_le_iff₀ (mul_pos hδ0 hη)] at h12
    exact h12
  have hnr : (n : ℝ) ≤ R k ^ 2 * T :=
    (by exact_mod_cast hn2 : (n : ℝ) ≤ (⌊R k ^ 2 * T⌋₊ : ℝ)).trans (Nat.floor_le (by positivity))
  have hn2' : (2 : ℝ) ≤ n := hδR.trans hn1
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := by
    have h1n : 1 ≤ n := by exact_mod_cast (by linarith : (1 : ℝ) ≤ n)
    exact ⟨n - 1, by omega⟩
  push_cast at hn1 hnr hn2'
  rw [Nat.add_sub_cancel]
  have hmreal : δ / 2 * R k ^ 2 ≤ (m : ℝ) := by nlinarith
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hmreal
  have hmT : (m : ℝ) ≤ T * R k ^ 2 := by nlinarith
  have hτm : bandTau P hd ν hint hmean hnondeg k ≤ m := by
    have h1 : ((bandTau P hd ν hint hmean hnondeg k : ℕ) : ℝ) < δ / 2 * R k ^ 2 := by
      rwa [div_lt_iff₀ hR2pos] at hτk
    exact_mod_cast (h1.trans_le hmreal).le
  obtain ⟨hz0, hz12, -⟩ := hrk m hmT m hτm le_rfl
  -- the time `t = m/R²` and the profile at `⌊tR²⌋ = m`
  set t : ℝ := (m : ℝ) / R k ^ 2 with htdef
  have hmt : t * R k ^ 2 = m := by rw [htdef]; exact div_mul_cancel₀ _ hR2pos.ne'
  have htI : t ∈ Set.Icc (δ / 2) T := by
    refine ⟨?_, ?_⟩
    · rw [htdef, le_div_iff₀ hR2pos]; exact hmreal
    · rw [htdef, div_le_iff₀ hR2pos]; exact hmT
  have hfl : ⌊t * R k ^ 2⌋₊ = m := by rw [hmt, Nat.floor_natCast]
  have h1 := hinvk t htI
  simp only [hfl] at h1
  have hinv1 : (bandCoordSeq P d ν k m ^ (-(P.theta k)) / L k)⁻¹
      = L k * bandCoordSeq P d ν k m ^ P.theta k := by
    rw [Real.rpow_neg hz0.le, inv_div, div_inv_eq_mul]
  rw [hinv1, inv_div] at h1
  -- the band tail at the coordinate
  have hz1 : bandCoordSeq P d ν k m ∈ Set.Icc (0 : ℝ) 1 := ⟨hz0.le, hz12.trans (by norm_num)⟩
  have hte := htail _ hz1
  have hDne : (1 - P.l1) * P.level k ≠ 0 :=
    (mul_pos (by linarith [P.hl1.2]) (P.level_pos k)).ne'
  have hlevel : P.level k - (1 - P.l1) * P.level k * bandCoordSeq P d ν k m
      = bandLevelSeq d ν m :=
    level_eq_of_bandLevelCoord (l1 := P.l1) P.level (bandLevelSeq d ν) k m hDne
  have hmeas : ((centeredMassLaw d ν) {σ | meanOdometer (centeredMassLaw d ν) m <
        -(green d 0 0 * scenery d σ 0)}).toReal
      = (ν {x : ℝ | -x > P.level k - (1 - P.l1) * P.level k * bandCoordSeq P d ν k m}).toReal := by
    rw [bandStep2_threshold_measure ν hd1 hG m, hlevel]
    rfl
  push_cast
  rw [hmeas]
  have hkey := bandStep2_rate_arith (r2 := R k ^ 2) (m := (m : ℝ)) (ω := P.weight k)
    (G := green d 0 0) (L := L k) (zθ := bandCoordSeq P d ν k m ^ P.theta k)
    (κ := 1 + 1 / P.theta k)
    (μ := (ν {x : ℝ | -x > P.level k - (1 - P.l1) * P.level k * bandCoordSeq P d ν k m}).toReal)
    (ζ := η / (3 * T)) (ε := e k) (T := T) hR2pos hm0 hG (P.weight_pos k) (hRL k) (hκ0 k)
    (hκ2 k) (by linarith) h1 hte
  refine hkey.trans ?_
  have hLe1 : L k * e k ≤ L k ^ 2 * e k := by
    nlinarith [mul_nonneg (mul_nonneg (hLpos k).le (he0 k)) (sub_nonneg.mpr hLk1)]
  have hA1 : T * (η / (3 * T)) = η / 3 := by field_simp
  have hA2 : T * L k * e k ≤ η / 3 := by
    have h := mul_le_mul_of_nonneg_left (hLe1.trans hLek.le) hT.le
    rw [hA1] at h
    linarith
  have hA3 : 2 / (m : ℝ) ≤ η / 3 := by
    rw [div_le_iff₀ hm0]
    nlinarith
  linarith

/-- **The squared scale diverges.**  From `R² ω = G L` with `ω < 1` eventually, `R² ≥ G L`. -/
private theorem bandStep2_scaleSq_tendsto (P : BandParameters) (hd : 5 ≤ d) (L R : ℕ → ℝ)
    (hL : Tendsto L atTop atTop) (hRL : ∀ k : ℕ, R k ^ 2 * P.weight k = green d 0 0 * L k) :
    Tendsto (fun k : ℕ => R k ^ 2) atTop atTop := by
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  refine tendsto_atTop_mono' _ ?_ (hL.const_mul_atTop hG)
  filter_upwards [(bandStep2_weight_tendsto P).eventually_lt_const one_pos] with k hk
  have h := mul_le_mul_of_nonneg_left hk.le (sq_nonneg (R k))
  linarith [hRL k]

/-- **The contact comparison from band estimates at the rate `e`.**  Everything the node
needs, with the three rate-`e` estimates as explicit hypotheses in the shapes that the band
estimates provably have (see `bandStep2_moduli_core`): the mass above the band, the origin
concentration at the times whose frozen level is still below `a_k`, and the lower isolation.

Proof.  For `n = m + 1` in the band, `bandProfile_range` puts the coordinate `z_{k,m}` in
`(0, 1/2]`, so the frozen level `b` lies in `[ℓ₁a_k + (1-ℓ₁)a_k/2, a_k]`;
`contact_estimate_usable` bounds the symmetric difference by three terms, each of order
`e_k ω_k`, and `R² ω = G L` turns the bound into `K L e_k ≤ K L² e_k → 0`. -/
private theorem bandStep2_comparison_core (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hgap : P.lam0 < θ₀ / LatticeProb.greenRatioSup d)
    (hdens : BandDensity P ν)
    (e L R : ℕ → ℝ) (he0 : ∀ k, 0 ≤ e k) (he : Tendsto e atTop (𝓝 0))
    (hLpos : ∀ k, 0 < L k) (hL : Tendsto L atTop atTop)
    (hslow : ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) → (∀ k, f k ≤ e k) →
      Tendsto (fun k => L k ^ 2 * f k) atTop (𝓝 0))
    (hmod : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
        |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
            - P.weight k / (green d 0 0 * (P.theta k + 1))
              * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
          ≤ e k * P.weight k) (hR2 : Tendsto (fun k : ℕ => R k ^ 2) atTop atTop)
    (hRL : ∀ k : ℕ, R k ^ 2 * P.weight k = green d 0 0 * L k)
    (T : ℝ) (hT : 0 < T)
    (hmass : ∀ᶠ k : ℕ in atTop, (ν {z : ℝ | -(z) > P.level k}).toReal ≤ e k * P.weight k)
    (hconc : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      meanOdometer (centeredMassLaw d ν) n / green d 0 0 ≤ P.level k →
        (∫ σ, |avg (originOdometer (scenery d σ) n) 0
            - meanOdometer (centeredMassLaw d ν) n / green d 0 0| ∂centeredMassLaw d ν)
          ≤ e k * P.level k)
    (hlowmod : ∀ᶠ k : ℕ in atTop,
      Real.exp (-(P.lam0 * P.l1 * P.level k)) *
        (∫ z, Real.exp (-(P.lam0 * z)) *
          Set.indicator {z : ℝ | -(z) ≤ P.l1 * P.level k} (fun _ => (1 : ℝ)) z ∂ν) /
        P.weight k ≤ e k) :
    BandContactComparison d ν R T := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hlam : 0 < P.lam0 := P.hlam0
  have h1l : 0 < 1 - P.l1 := by linarith [P.hl1.2]
  obtain ⟨Cd, hCd, hdk⟩ := hdens
  obtain ⟨C, hC⟩ := bandStep2_exp_moment P hd ν hθ₀ hexp hgap
  set C₀ : ℝ := max C 1 with hC₀
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCC₀ : C ≤ C₀ := le_max_left _ _
  set K : ℝ := green d 0 0 * (C₀ + Cd + 1) with hKdef
  have hK : 0 < K := by positivity
  obtain ⟨Cτ, hCτ⟩ := bandStep2_tau_le P hd ν hint hmean hnondeg e he hmod
  have hs := bandTau_div_scaleSq_tendsto P hd ν hint hmean hnondeg R L hG P.weight_pos hL hRL hCτ
  have hrange := bandStep2_range_pos P hd ν hint hmean hnondeg e L R he0 hLpos hL hslow hmod
    hRL T hT
  intro δ hδ η hη
  obtain ⟨hδ0, hδT⟩ := hδ
  have hδ2 : 0 < δ / 2 := by positivity
  filter_upwards [hdk, hmass, hconc, hlowmod, hrange, hs.eventually_lt_const hδ2,
    he.eventually_lt_const (show (0 : ℝ) < (1 - P.l1) / 2 by positivity),
    (hslow e he0 (fun _ => le_rfl)).eventually_lt_const (show (0 : ℝ) < η / K by positivity),
    hL.eventually_ge_atTop 1, hR2.eventually_ge_atTop (2 / δ)]
    with k hdk hmk hck hlk hrk hτk hek hLek hLk1 hRk n hn1 hn2
  have hR2pos : 0 < R k ^ 2 := lt_of_lt_of_le (by positivity) hRk
  have hδR : 2 ≤ δ * R k ^ 2 := by
    rw [div_le_iff₀ hδ0] at hRk
    linarith
  have hnr : (n : ℝ) ≤ R k ^ 2 * T :=
    (by exact_mod_cast hn2 : (n : ℝ) ≤ (⌊R k ^ 2 * T⌋₊ : ℝ)).trans (Nat.floor_le (by positivity))
  have hn2' : (2 : ℝ) ≤ n := hδR.trans hn1
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := by
    have h1n : 1 ≤ n := by exact_mod_cast (by linarith : (1 : ℝ) ≤ n)
    exact ⟨n - 1, by omega⟩
  push_cast at hn1 hnr hn2'
  rw [Nat.add_sub_cancel]
  have hmreal : δ / 2 * R k ^ 2 ≤ (m : ℝ) := by linarith
  have hmT : (m : ℝ) ≤ T * R k ^ 2 := by linarith
  have hτm : bandTau P hd ν hint hmean hnondeg k ≤ m := by
    have h1 : ((bandTau P hd ν hint hmean hnondeg k : ℕ) : ℝ) < δ / 2 * R k ^ 2 := by
      rwa [div_lt_iff₀ hR2pos] at hτk
    exact_mod_cast (h1.trans_le hmreal).le
  obtain ⟨hz0, hz12, -⟩ := hrk m hmT m hτm le_rfl
  -- the threshold event, as a level set of the scenery at the frozen level
  have hset : {σ : Site d → ℝ | meanOdometer (centeredMassLaw d ν) m
        < -(green d 0 0 * scenery d σ 0)}
      = {σ : Site d → ℝ | -(scenery d σ 0) > meanOdometer (centeredMassLaw d ν) m / green d 0 0}
      := by
    ext σ
    simp only [Set.mem_setOf_eq, gt_iff_lt]
    rw [div_lt_iff₀ hG]
    constructor <;> intro h <;> linarith
  rw [hset]
  have ha0 : 0 < P.level k := P.level_pos k
  have hω : 0 < P.weight k := P.weight_pos k
  have hD : 0 < (1 - P.l1) * P.level k := mul_pos h1l ha0
  have hlevel : P.level k - (1 - P.l1) * P.level k * bandCoordSeq P d ν k m
      = bandLevelSeq d ν m :=
    level_eq_of_bandLevelCoord (l1 := P.l1) P.level (bandLevelSeq d ν) k m hD.ne'
  have hbseq : bandLevelSeq d ν m = meanOdometer (centeredMassLaw d ν) m / green d 0 0 := rfl
  rw [hbseq] at hlevel
  set b : ℝ := meanOdometer (centeredMassLaw d ν) m / green d 0 0 with hbdef
  have hbA : b ≤ P.level k := by linarith [mul_nonneg hD.le hz0.le]
  have hb2 : P.l1 * P.level k + (1 - P.l1) * P.level k / 2 ≤ b := by
    have := mul_le_mul_of_nonneg_left hz12 hD.le
    linarith
  have hb : P.l1 * P.level k ≤ b := by
    have : 0 ≤ (1 - P.l1) * P.level k / 2 := by linarith
    linarith
  have hcabs := hck m hbA
  -- the mean of the random level stays above the bottom of the band
  have hWi := integrable_band_origin_average hd1 ν hint m
  have hm : b - e k * P.level k
      ≤ ∫ σ, avg (originOdometer (scenery d σ) m) 0 ∂(centeredMassLaw d ν) := by
    have h1 : ∫ σ, (avg (originOdometer (scenery d σ) m) 0 - b) ∂(centeredMassLaw d ν)
        = (∫ σ, avg (originOdometer (scenery d σ) m) 0 ∂(centeredMassLaw d ν)) - b := by
      rw [integral_sub hWi (integrable_const b)]
      simp only [integral_const, probReal_univ, one_smul]
    have h2 : |∫ σ, (avg (originOdometer (scenery d σ) m) 0 - b) ∂(centeredMassLaw d ν)|
        ≤ ∫ σ, |avg (originOdometer (scenery d σ) m) 0 - b| ∂(centeredMassLaw d ν) :=
      abs_integral_le_integral_abs
    have h3 := neg_abs_le
      (∫ σ, (avg (originOdometer (scenery d σ) m) 0 - b) ∂(centeredMassLaw d ν))
    linarith
  have hlm : P.l1 * P.level k
      ≤ ∫ σ, avg (originOdometer (scenery d σ) m) 0 ∂(centeredMassLaw d ν) := by
    have hεle : e k * P.level k ≤ (1 - P.l1) / 2 * P.level k :=
      mul_le_mul_of_nonneg_right hek.le ha0.le
    have : (1 - P.l1) / 2 * P.level k = (1 - P.l1) * P.level k / 2 := by ring
    linarith
  have hEe : ∫ σ, Real.exp (-(P.lam0 * avg (originOdometer (scenery d σ) m) 0))
        ∂(centeredMassLaw d ν)
      ≤ C₀ * Real.exp (-(P.lam0 * (P.l1 * P.level k))) := by
    refine (hC m).trans ?_
    calc C * Real.exp (-(P.lam0 *
            ∫ σ, avg (originOdometer (scenery d σ) m) 0 ∂(centeredMassLaw d ν)))
        ≤ C₀ * Real.exp (-(P.lam0 *
            ∫ σ, avg (originOdometer (scenery d σ) m) 0 ∂(centeredMassLaw d ν))) :=
          mul_le_mul_of_nonneg_right hCC₀ (Real.exp_pos _).le
      _ ≤ C₀ * Real.exp (-(P.lam0 * (P.l1 * P.level k))) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₀pos.le
          have := mul_le_mul_of_nonneg_left hlm hlam.le
          linarith
  set I : ℝ := ∫ z, expWeightBelow P.lam0 (P.l1 * P.level k) z ∂ν with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun z => expWeightBelow_nonneg _ _ z
  have hlk' : Real.exp (-(P.lam0 * (P.l1 * P.level k))) * I ≤ e k * P.weight k := by
    have h := hlk
    rw [div_le_iff₀ hω, mul_assoc P.lam0 P.l1 (P.level k)] at h
    exact h
  -- the three terms of the contact estimate
  have hcontact := contact_estimate_usable d hd1 ν m P hatom hmean hint k hCd hdk hlam hb
  have hT1 : (∫ σ, Real.exp (-(P.lam0 * avg (originOdometer (scenery d σ) m) 0))
        ∂(centeredMassLaw d ν)) * I ≤ C₀ * (e k * P.weight k) := by
    calc _ ≤ (C₀ * Real.exp (-(P.lam0 * (P.l1 * P.level k)))) * I :=
          mul_le_mul_of_nonneg_right hEe hI0
      _ = C₀ * (Real.exp (-(P.lam0 * (P.l1 * P.level k))) * I) := by ring
      _ ≤ C₀ * (e k * P.weight k) := mul_le_mul_of_nonneg_left hlk' hC₀pos.le
  have hT2 : Cd * P.weight k / P.level k *
        ∫ σ, |avg (originOdometer (scenery d σ) m) 0 - b| ∂(centeredMassLaw d ν)
      ≤ Cd * (e k * P.weight k) := by
    calc _ ≤ Cd * P.weight k / P.level k * (e k * P.level k) :=
          mul_le_mul_of_nonneg_left hcabs (by positivity)
      _ = Cd * (e k * P.weight k) := by field_simp
  have hX : ((centeredMassLaw d ν) (symmDiff {σ : Site d → ℝ | odometer σ (m + 1) 0 = 0}
        {σ : Site d → ℝ | -(scenery d σ 0) > b})).toReal
      ≤ (C₀ + Cd + 1) * (e k * P.weight k) := by
    linarith
  have hfin : R k ^ 2 * ((centeredMassLaw d ν) (symmDiff
        {σ : Site d → ℝ | odometer σ (m + 1) 0 = 0}
        {σ : Site d → ℝ | -(scenery d σ 0) > b})).toReal ≤ K * (L k * e k) := by
    calc _ ≤ R k ^ 2 * ((C₀ + Cd + 1) * (e k * P.weight k)) :=
          mul_le_mul_of_nonneg_left hX hR2pos.le
      _ = (C₀ + Cd + 1) * e k * (R k ^ 2 * P.weight k) := by ring
      _ = K * (L k * e k) := by rw [hRL k, hKdef]; ring
  have hLe1 : L k * e k ≤ L k ^ 2 * e k := by
    have h := mul_nonneg (mul_nonneg (hLpos k).le (he0 k)) (sub_nonneg.mpr hLk1)
    have h' : L k ^ 2 * e k - L k * e k = L k * e k * (L k - 1) := by ring
    linarith
  have hKη : K * (L k ^ 2 * e k) ≤ η := by
    have h := mul_le_mul_of_nonneg_left hLek.le hK.le
    have h2 : K * (η / K) = η := by field_simp
    linarith
  linarith [mul_le_mul_of_nonneg_left hLe1 hK.le]

/-- **(g) The contact comparison.**

Proof.  `measure_contact_symmDiff_le` bounds the symmetric difference by the
below-band term, the level term and the mass above the band.  Its density
hypothesis is `hdens`, which `BandProfile` does NOT supply; the first version of
this statement omitted it.  Each of the three terms is of order `ω_k` times a band
error, so `R_k²` times the bound is `L_k` times that error by `hRL`, and the
slow-scale property of `exists_bandScale` is exactly what makes THAT vanish.  The
lower bounds on the level over the horizon come from `bandProfile_range`. -/
theorem bandContactComparison_of_band (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hgap : P.lam0 < θ₀ / LatticeProb.greenRatioSup d)
    (hdens : BandDensity P ν)
    (e L R : ℕ → ℝ) (he0 : ∀ k, 0 ≤ e k) (he : Tendsto e atTop (𝓝 0))
    (hLpos : ∀ k, 0 < L k) (hL : Tendsto L atTop atTop)
    (hslow : ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) → (∀ k, f k ≤ e k) →
      Tendsto (fun k => L k ^ 2 * f k) atTop (𝓝 0))
    (hmod : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
        |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
            - P.weight k / (green d 0 0 * (P.theta k + 1))
              * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
          ≤ e k * P.weight k)
    (hRL : ∀ k : ℕ, R k ^ 2 * P.weight k = green d 0 0 * L k)
    (T : ℝ) (hT : 0 < T)
    (hmods : BandModuli P d ν e) :
    BandContactComparison d ν R T := by
  refine bandStep2_comparison_core P hd ν hatom hint hmean hnondeg hθ₀ hexp hgap hdens e L R he0
    he hLpos hL hslow hmod (bandStep2_scaleSq_tendsto P hd L R hL hRL) hRL T hT hmods.2.2.1 ?_ ?_
  · -- the origin concentration, at the times whose frozen level is below `a_k`
    filter_upwards [hmods.2.2.2.1] with k hk n hn using hk n hn
  · -- the lower isolation at the rate `e`: the first term of the contact estimate is
    -- `E e^{-λW_n} · ∫ expWeightBelow`, and `R² ω = G L` turns it into `G L` times this ratio
    exact hmods.2.2.2.2

/-- **The band estimates at one rate, in the shapes that ARE provable.**  Diagonalise the
increment, the band tail, the mass above the band, the origin concentration and the lower
isolation together.  Two of these differ from what `BandModuli` records:

* the origin concentration holds only for the times `n` at which the frozen level is still
  below the level `a_k` (`band_origin_concentration` is stated under exactly that hypothesis;
  for larger `n` the only available bound is `γ b_n + C`, which grows with `b_n`);
* the lower isolation, at rate `e`, is a clause of its own, which `BandModuli` omits. -/
private theorem bandStep2_moduli_core (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hgap : P.lam0 < θ₀ / LatticeProb.greenRatioSup d)
    (hprof : BandIntegratedProfile P ν) (hbp : BandProfile P ν)
    (hlow : BandLowerIsolation P ν) :
    ∃ e : ℕ → ℝ, (∀ k, 0 < e k) ∧ Tendsto e atTop (𝓝 0) ∧
      (∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
        bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
          |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
              - P.weight k / (green d 0 0 * (P.theta k + 1))
                * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
            ≤ e k * P.weight k) ∧
      (∀ᶠ k : ℕ in atTop, ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
        |(ν {z : ℝ | -(z) > P.level k - (1 - P.l1) * P.level k * r}).toReal / P.weight k
          - r ^ P.theta k| ≤ e k) ∧
      (∀ᶠ k : ℕ in atTop, (ν {z : ℝ | -(z) > P.level k}).toReal ≤ e k * P.weight k) ∧
      (∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
        meanOdometer (centeredMassLaw d ν) n / green d 0 0 ≤ P.level k →
          (∫ σ, |avg (originOdometer (scenery d σ) n) 0
              - meanOdometer (centeredMassLaw d ν) n / green d 0 0| ∂centeredMassLaw d ν)
            ≤ e k * P.level k) ∧
      (∀ᶠ k : ℕ in atTop,
        Real.exp (-(P.lam0 * P.l1 * P.level k)) *
          (∫ z, Real.exp (-(P.lam0 * z)) *
            Set.indicator {z : ℝ | -(z) ≤ P.l1 * P.level k} (fun _ => (1 : ℝ)) z ∂ν) /
          P.weight k ≤ e k) := by
  have hinc := bandLevel_increment_rel_error P hd ν hatom hint hmean hsq hθ₀ hexp hgap hprof hbp
    hlow
  have hconc := (band_origin_concentration hd ν hatom hmean hsq (fun k => P.level k)
    P.level_tendsto).2
  obtain ⟨e, hepos, he, hev⟩ := bandStep2_diagonal
    (fun η k =>
      (∀ n : ℕ, bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
        |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
            - P.weight k / (green d 0 0 * (P.theta k + 1))
              * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
          ≤ η * P.weight k) ∧
      (∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 →
        |(ν {z : ℝ | -(z) > P.level k - (1 - P.l1) * P.level k * r}).toReal / P.weight k
          - r ^ P.theta k| ≤ η) ∧
      (ν {z : ℝ | -(z) > P.level k}).toReal ≤ η * P.weight k ∧
      (∀ n : ℕ, meanOdometer (centeredMassLaw d ν) n / green d 0 0 ≤ P.level k →
        (∫ σ, |avg (originOdometer (scenery d σ) n) 0
            - meanOdometer (centeredMassLaw d ν) n / green d 0 0| ∂centeredMassLaw d ν)
          ≤ η * P.level k) ∧
      Real.exp (-(P.lam0 * P.l1 * P.level k)) *
          (∫ z, Real.exp (-(P.lam0 * z)) *
            Set.indicator {z : ℝ | -(z) ≤ P.l1 * P.level k} (fun _ => (1 : ℝ)) z ∂ν) /
          P.weight k ≤ η)
    (fun η hη => by
      filter_upwards [hinc η hη, hbp η hη, hconc η hη, hlow.eventually_lt_const hη]
        with k h1 h2 h3 h4
      refine ⟨h1, h2, ?_, ?_, h4.le⟩
      · have h := h2 0 ⟨le_rfl, zero_le_one⟩
        have hθ : P.theta k ≠ 0 := (by linarith [(P.htheta k).1] : (0 : ℝ) < P.theta k).ne'
        rw [mul_zero, sub_zero, Real.zero_rpow hθ, sub_zero,
          abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg (P.weight_pos k).le),
          div_le_iff₀ (P.weight_pos k)] at h
        exact h
      · obtain ⟨ha0, hcn⟩ := h3
        intro n hn
        have h := hcn n hn
        rw [div_le_iff₀ ha0] at h
        linarith)
  exact ⟨e, hepos, he, hev.mono fun k hk => hk.1, hev.mono fun k hk => hk.2.1,
    hev.mono fun k hk => hk.2.2.1, hev.mono fun k hk => hk.2.2.2.1,
    hev.mono fun k hk => hk.2.2.2.2⟩

/-- **All the band estimates at one rate.**  Diagonalise the five qualitative band
estimates simultaneously, so that one sequence dominates them all.  The increment
clause comes from `bandLevel_increment_modulus`, which is proved; the other four
are the band tail, the mass above the band, the origin concentration and the lower
isolation, each already available in qualitative form.

Proof.  `bandStep2_diagonal` applied to the conjunction: for each `j` take an index
beyond which all five hold at `1/(j+1)`, and define the sequence blockwise.  Any
`e` valid for the conjunction is valid for each clause separately, so the increment
clause survives enlarging `e`. -/
theorem exists_bandModuli (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hgap : P.lam0 < θ₀ / LatticeProb.greenRatioSup d)
    (hprof : BandIntegratedProfile P ν) (hbp : BandProfile P ν)
    (hlow : BandLowerIsolation P ν) :
    ∃ e : ℕ → ℝ, (∀ k, 0 ≤ e k) ∧ Tendsto e atTop (𝓝 0) ∧ BandModuli P d ν e := by
  obtain ⟨e, hepos, he, h1, h2, h3, h4, h5⟩ :=
    bandStep2_moduli_core P hd ν hatom hint hmean hsq hθ₀ hexp hgap hprof hbp hlow
  exact ⟨e, fun k => (hepos k).le, he, h1, h2, h3, h4, h5⟩

/-- **(h) Step 2's output, together with the scale it is stated for.**  This is
what Step 3 consumes, and the existential over the scale is what the frozen
statement needs. -/
theorem exists_dgt4AStep2Output (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hgap : P.lam0 < θ₀ / LatticeProb.greenRatioSup d)
    (hprof : BandIntegratedProfile P ν) (hbp : BandProfile P ν)
    (hdens : BandDensity P ν) (hlow : BandLowerIsolation P ν) :
    ∃ R : ℕ → ℝ, StrictMono R ∧ Tendsto R atTop atTop ∧
      Dgt4AStep2Output d ν (fun k => 1 + 1 / P.theta k) R := by
  obtain ⟨e, he0, he, hmods⟩ :=
    exists_bandModuli P hd ν hatom hint hmean hsq hθ₀ hexp hgap hprof hbp hlow
  have hmod := hmods.1
  obtain ⟨L, R, hLpos, hL, hRmono, hR, hRL, hslow⟩ :=
    exists_bandScale P hd ν e he0 he
  refine ⟨R, hRmono, hR, fun T hT => ⟨?_, ?_⟩⟩
  · exact bandContactRate_of_scaled P hd ν hatom hint hmean hsq hnondeg hθ₀ hexp hgap
      hprof hbp hdens hlow e L R he0 he hLpos hL hslow hmod hR hRL T hT hmods
  · exact bandContactComparison_of_band P hd ν hatom hint hmean hnondeg hθ₀ hexp hgap
      hdens e L R he0 he hLpos hL hslow hmod hRL T hT hmods

end Sandpile.Support
