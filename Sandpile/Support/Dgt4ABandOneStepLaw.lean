import Sandpile.Support.Dgt4ABandTauProps
import Sandpile.Support.Dgt4ABandOneStep
import Sandpile.Support.Dgt4ABandIntegrated
import Sandpile.Support.Dgt4ABandSideConditions

/-!
# One-step profile increment at the sandpile law

The one-step profile at the sandpile law.

`scaledProfile_bound_family` consumes a single hypothesis about increments: past
the hitting index, and up to a time of order the square of the scale, the
increment of the profile is the band weight over `G(0,0)` times the exponent
factor, to within a vanishing relative error.  At the sandpile law that comes
from two steps.  First the mean increment of the odometer is the mean overshoot
above the frozen level, which the integrated profile evaluates; that is the
relative-error hypothesis of `abs_oneStep_increment_le'`.  Then that lemma turns
it into the increment of the profile itself.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- The frozen mean level at the sandpile law. -/
def bandLevelSeq (d : ℕ) (ν : Measure ℝ) (n : ℕ) : ℝ :=
  meanOdometer (centeredMassLaw d ν) n / green d 0 0

/-- The profile coordinate at the sandpile law. -/
def bandCoordSeq (P : BandParameters) (d : ℕ) (ν : Measure ℝ) (k n : ℕ) : ℝ :=
  bandLevelCoord P.l1 P.level (bandLevelSeq d ν) k n

/-- **The level increment against the integrated profile.**  The one-step rise of
the frozen level, measured in band units, is the integrated profile at the current
coordinate, to within an error that is small relative to the band weight.  The
error is additive in the weight, not relative to the profile, because the profile
vanishes at the bottom of the band.

The coordinate is restricted to `Icc 0 (1/2)`, which is the paper's own range: the
exponential term below is controlled only once the level is above
`ℓ₁a_k + (1-ℓ₁)a_k/8`, and a statement over all of `Icc 0 1` would be stronger
than the paper's and is not proved here.

Proof, step by step.
1. `bandLevelCoord_sub_succ` rewrites `z_n - z_{n+1}` as `(b_{n+1} - b_n)/((1-ℓ₁)a_k)`.
2. `meanOdometer_increment_sub_frozen_le` bounds `b_{n+1} - b_n` against the mean
   overshoot above the frozen level, its four side conditions supplied by
   `bandSide_exp`, `bandSide_symmDiff`, `bandSide_belowBand`, `bandSide_abs`.
   It leaves two terms over.
3. The LEVEL term is `E|W_n - b|·ν{-z > ℓ₁a_k}`.  `band_origin_concentration`
   bounds the first factor, and `measure_gt_band_bottom_le` bounds the second by
   `(1+η)ω_k`.  That second bound needs `BandProfile`, which the integrated
   profile does NOT imply, so `hbp` is carried explicitly.
4. The EXPONENTIAL term is `E e^{-λ₀W_n}/(λ₀e) · ∫ expWeightBelow λ₀ (ℓ₁a_k) dν`.
   `hlow` makes the integral `e^{λ₀ℓ₁a_k}·o(ω_k)`, so bounding `E e^{-λ₀W_n}` by
   one is short by exactly that factor; the exponential LOWER TAIL of `W_n`,
   `band_origin_lower_tail`, supplies the missing factor.  It needs an exponential
   moment and a gap condition, which are `hexp` and `hgap`.
5. `level_eq_of_bandLevelCoord` turns the level into the coordinate, and `hprof`
   evaluates the overshoot there. -/
theorem bandLevel_increment_rel_error (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hgap : P.lam0 < θ₀ / LatticeProb.greenRatioSup d)
    (hprof : BandIntegratedProfile P ν) (hbp : BandProfile P ν)
    (hlow : BandLowerIsolation P ν) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
        |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
            - P.weight k / (green d 0 0 * (P.theta k + 1))
              * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
          ≤ η * P.weight k := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hlam : 0 < P.lam0 := P.hlam0
  have hl1 : P.l1 < 1 := P.hl1.2
  have h1l : 0 < 1 - P.l1 := by linarith
  -- integrability of the scenery side
  have hposν : Integrable (fun z : ℝ => max (-z) 0) ν := integrable_negPart ν hint
  have hνw : ∀ w : ℝ, Integrable (fun z : ℝ => max (-z - w) 0) ν := by
    intro w
    refine Integrable.mono' (hposν.add (integrable_const |w|))
      (((measurable_id.neg.sub_const w).max measurable_const).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have h1 : -z ≤ max (-z) 0 := le_max_left _ _
    have h2 : -w ≤ |w| := by
      rw [← abs_neg]
      exact le_abs_self _
    have h3 : (0 : ℝ) ≤ max (-z) 0 := le_max_right _ _
    have h4 : (0 : ℝ) ≤ |w| := abs_nonneg _
    exact max_le (by linarith) (by linarith)
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    hint.abs.mono' (by fun_prop) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
      exact max_le (le_abs_self z) (abs_nonneg z))
  have hWiid : ∀ n : ℕ, Integrable (fun ζ : Site d → ℝ => avg (originOdometer ζ n) 0)
      (LatticeProb.iidLaw d ν) := fun n =>
    integrable_avg_field
      (fun x => integrable_localizedOdometer hd1 ν hpos {x : Site d | x ≠ 0} n x) 0
  -- the mean overshoot is `1`-Lipschitz in the level
  have hFlip : ∀ s t : ℝ, |(∫ z, max (-z - s) 0 ∂ν) - ∫ z, max (-z - t) 0 ∂ν| ≤ |s - t| := by
    intro s t
    refine (abs_integral_posPart_sub_le ν (hνw s) (hνw t)).trans ?_
    have h1 : (ν {z : ℝ | -(z) > min s t}).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    calc |s - t| * (ν {z : ℝ | -(z) > min s t}).toReal ≤ |s - t| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |s - t| := mul_one _
  have hFcont : Continuous (fun w : ℝ => ∫ z, max (-z - w) 0 ∂ν) := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun w₁ w₂ => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq]
    simpa using hFlip w₁ w₂
  have hFint : ∀ n : ℕ, Integrable
      (fun σ => ∫ z, max (-z - avg (originOdometer (scenery d σ) n) 0) 0 ∂ν)
      (centeredMassLaw d ν) := by
    intro n
    have hWi := integrable_band_origin_average hd1 ν hint n
    refine Integrable.mono' ((integrable_const |∫ z, max (-z - 0) 0 ∂ν|).add hWi.abs)
      ((hFcont.measurable.comp (measurable_bandLevel d hd1 n)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun σ => ?_)
    have h := hFlip (avg (originOdometer (scenery d σ) n) 0) 0
    have h' := abs_sub_abs_le_abs_sub
      (∫ z, max (-z - avg (originOdometer (scenery d σ) n) 0) 0 ∂ν) (∫ z, max (-z - 0) 0 ∂ν)
    rw [sub_zero] at h
    simp only [Pi.add_apply, Real.norm_eq_abs]
    linarith
  -- the exponential moment of the origin-frozen average
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ n : ℕ,
      ∫ σ, Real.exp (-(P.lam0 * avg (originOdometer (scenery d σ) n) 0)) ∂(centeredMassLaw d ν)
        ≤ C * Real.exp (-(P.lam0 *
          ∫ σ, avg (originOdometer (scenery d σ) n) 0 ∂(centeredMassLaw d ν))) := by
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
  set C₀ : ℝ := max C 1 with hC₀
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCC₀ : C ≤ C₀ := le_max_left _ _
  intro η hη
  -- the four small parameters, one for each source of error
  set ε₂ : ℝ := min ((1 - P.l1) / 2) (green d 0 0 * (1 - P.l1) * η / 6) with hε₂def
  have hε₂ : 0 < ε₂ := lt_min (by linarith) (div_pos (mul_pos (mul_pos hG h1l) hη) (by norm_num))
  have hη₁ : 0 < green d 0 0 * η / 3 := div_pos (mul_pos hG hη) (by norm_num)
  set η₄ : ℝ := η * (P.lam0 * Real.exp 1 * green d 0 0 * (1 - P.l1)) / (3 * C₀) with hη₄def
  have hη₄ : 0 < η₄ := div_pos
    (mul_pos hη (mul_pos (mul_pos (mul_pos hlam (Real.exp_pos 1)) hG) h1l))
    (mul_pos (by norm_num) hC₀pos)
  have hconc := (band_origin_concentration hd ν hatom hmean hsq (fun k => P.level k)
    P.level_tendsto).2 ε₂ hε₂
  filter_upwards [hprof _ hη₁, measure_gt_band_bottom_le P ν hbp 1 one_pos, hconc,
    hlow.eventually_lt_const hη₄, P.level_tendsto.eventually_ge_atTop 1]
    with k hk1 hk2 hk3 hk4 hk5 n hn
  obtain ⟨ha0, hcn⟩ := hk3
  have hD : 0 < (1 - P.l1) * P.level k := mul_pos h1l ha0
  have hω : 0 < P.weight k := P.weight_pos k
  have hθ1 : 0 < P.theta k + 1 := by
    have := (P.htheta k).1
    linarith
  have hGne : green d 0 0 ≠ 0 := hG.ne'
  have hDne : (1 - P.l1) * P.level k ≠ 0 := hD.ne'
  have hωne : P.weight k ≠ 0 := hω.ne'
  have h1lne : 1 - P.l1 ≠ 0 := h1l.ne'
  have hane : P.level k ≠ 0 := ha0.ne'
  have hθne : P.theta k + 1 ≠ 0 := hθ1.ne'
  obtain ⟨hz0, hz1⟩ := hn
  -- the profile coordinate reads the frozen level back
  have hlevel : P.level k - (1 - P.l1) * P.level k * bandCoordSeq P d ν k n
      = bandLevelSeq d ν n :=
    level_eq_of_bandLevelCoord (l1 := P.l1) P.level (bandLevelSeq d ν) k n hDne
  have hb2 : P.l1 * P.level k + (1 - P.l1) * P.level k / 2 ≤ bandLevelSeq d ν n := by
    have := mul_le_mul_of_nonneg_left hz1 hD.le
    linarith
  have hbA : bandLevelSeq d ν n ≤ P.level k := by
    have := mul_nonneg hD.le hz0
    linarith
  -- step 1: the decrement of the coordinate is the increment of the frozen level
  have hstep : bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1)
      = (meanOdometer (centeredMassLaw d ν) (n + 1) - meanOdometer (centeredMassLaw d ν) n)
          / (green d 0 0 * ((1 - P.l1) * P.level k)) := by
    have h := bandLevelCoord_sub_succ (l1 := P.l1) P.level (bandLevelSeq d ν) k n
    unfold bandCoordSeq
    rw [h]
    unfold bandLevelSeq
    field_simp
  have hcn' : meanOdometer (centeredMassLaw d ν) n / green d 0 0 ≤ P.level k := hbA
  have hconcn := hcn n hcn'
  have hbseq : bandLevelSeq d ν n = meanOdometer (centeredMassLaw d ν) n / green d 0 0 := rfl
  rw [hbseq] at hlevel hb2 hbA
  set b : ℝ := meanOdometer (centeredMassLaw d ν) n / green d 0 0 with hbdef
  have hcabs : ∫ σ, |avg (originOdometer (scenery d σ) n) 0 - b| ∂(centeredMassLaw d ν)
      ≤ ε₂ * P.level k := by
    rw [div_le_iff₀ ha0] at hconcn
    linarith
  have hb : P.l1 * P.level k ≤ b := by
    have : 0 ≤ (1 - P.l1) * P.level k / 2 := by linarith
    linarith
  -- step 2: the increment replacement
  have hinc := meanOdometer_increment_sub_frozen_le P d hd1 ν hatom hmean hint hlam k n
    (b := b) hb hposν hνw (hWiid n) (bandSide_exp d hd1 ν n hlam) (hFint n)
    (((hFint n).sub (integrable_const (∫ z, max (-z - b) 0 ∂ν))).abs)
    (bandSide_abs d hd1 ν n hint b)
  -- the mean of the random level stays above the bottom of the band
  have hWi := integrable_band_origin_average hd1 ν hint n
  have hm : b - ε₂ * P.level k
      ≤ ∫ σ, avg (originOdometer (scenery d σ) n) 0 ∂(centeredMassLaw d ν) := by
    have h1 : ∫ σ, (avg (originOdometer (scenery d σ) n) 0 - b) ∂(centeredMassLaw d ν)
        = (∫ σ, avg (originOdometer (scenery d σ) n) 0 ∂(centeredMassLaw d ν)) - b := by
      rw [integral_sub hWi (integrable_const b)]
      simp only [integral_const, probReal_univ, one_smul]
    have h2 : |∫ σ, (avg (originOdometer (scenery d σ) n) 0 - b) ∂(centeredMassLaw d ν)|
        ≤ ∫ σ, |avg (originOdometer (scenery d σ) n) 0 - b| ∂(centeredMassLaw d ν) :=
      abs_integral_le_integral_abs
    have h3 := neg_abs_le
      (∫ σ, (avg (originOdometer (scenery d σ) n) 0 - b) ∂(centeredMassLaw d ν))
    linarith
  have hεle : ε₂ * P.level k ≤ (1 - P.l1) / 2 * P.level k :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) ha0.le
  have hlm : P.l1 * P.level k
      ≤ ∫ σ, avg (originOdometer (scenery d σ) n) 0 ∂(centeredMassLaw d ν) := by
    have : (1 - P.l1) / 2 * P.level k = (1 - P.l1) * P.level k / 2 := by ring
    linarith
  -- step 4: the exponential term
  have hEe : ∫ σ, Real.exp (-(P.lam0 * avg (originOdometer (scenery d σ) n) 0))
        ∂(centeredMassLaw d ν)
      ≤ C₀ * Real.exp (-(P.lam0 * (P.l1 * P.level k))) := by
    refine (hC n).trans ?_
    calc C * Real.exp (-(P.lam0 *
            ∫ σ, avg (originOdometer (scenery d σ) n) 0 ∂(centeredMassLaw d ν)))
        ≤ C₀ * Real.exp (-(P.lam0 *
            ∫ σ, avg (originOdometer (scenery d σ) n) 0 ∂(centeredMassLaw d ν))) :=
          mul_le_mul_of_nonneg_right hCC₀ (Real.exp_pos _).le
      _ ≤ C₀ * Real.exp (-(P.lam0 * (P.l1 * P.level k))) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₀pos.le
          have := mul_le_mul_of_nonneg_left hlm hlam.le
          linarith
  set I : ℝ := ∫ z, expWeightBelow P.lam0 (P.l1 * P.level k) z ∂ν with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun z => expWeightBelow_nonneg _ _ z
  have hlowk : Real.exp (-(P.lam0 * (P.l1 * P.level k))) * I ≤ η₄ * P.weight k := by
    have h := hk4
    rw [div_lt_iff₀ hω, mul_assoc P.lam0 P.l1 (P.level k)] at h
    exact h.le
  have hlen : 0 < P.lam0 * Real.exp 1 := mul_pos hlam (Real.exp_pos 1)
  have hE1 : (∫ σ, Real.exp (-(P.lam0 * avg (originOdometer (scenery d σ) n) 0))
        ∂(centeredMassLaw d ν)) / (P.lam0 * Real.exp 1) * I
      ≤ η * green d 0 0 * ((1 - P.l1) * P.level k) / 3 * P.weight k := by
    calc (∫ σ, Real.exp (-(P.lam0 * avg (originOdometer (scenery d σ) n) 0))
            ∂(centeredMassLaw d ν)) / (P.lam0 * Real.exp 1) * I
        ≤ (C₀ * Real.exp (-(P.lam0 * (P.l1 * P.level k))) / (P.lam0 * Real.exp 1)) * I :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hEe hlen.le) hI0
      _ = C₀ / (P.lam0 * Real.exp 1) * (Real.exp (-(P.lam0 * (P.l1 * P.level k))) * I) := by
          ring
      _ ≤ C₀ / (P.lam0 * Real.exp 1) * (η₄ * P.weight k) :=
          mul_le_mul_of_nonneg_left hlowk (div_nonneg hC₀pos.le hlen.le)
      _ = η * green d 0 0 * (1 - P.l1) / 3 * P.weight k := by
          rw [hη₄def]
          field_simp
      _ ≤ η * green d 0 0 * ((1 - P.l1) * P.level k) / 3 * P.weight k := by
          have h1 : 1 - P.l1 ≤ (1 - P.l1) * P.level k := by nlinarith
          have h2 : η * green d 0 0 * (1 - P.l1)
              ≤ η * green d 0 0 * ((1 - P.l1) * P.level k) :=
            mul_le_mul_of_nonneg_left h1 (mul_pos hη hG).le
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h2 (by norm_num)) hω.le
  -- step 3: the level term
  have hE2 : (∫ σ, |avg (originOdometer (scenery d σ) n) 0 - b| ∂(centeredMassLaw d ν)) *
        (ν {z : ℝ | -(z) > P.l1 * P.level k}).toReal
      ≤ η * green d 0 0 * ((1 - P.l1) * P.level k) / 3 * P.weight k := by
    have hnn : 0 ≤ ∫ σ, |avg (originOdometer (scenery d σ) n) 0 - b| ∂(centeredMassLaw d ν) :=
      integral_nonneg fun σ => abs_nonneg _
    have hmass : (ν {z : ℝ | -(z) > P.l1 * P.level k}).toReal ≤ 2 * P.weight k := by
      linarith [hk2]
    have hε₂le : ε₂ ≤ green d 0 0 * (1 - P.l1) * η / 6 := min_le_right _ _
    calc (∫ σ, |avg (originOdometer (scenery d σ) n) 0 - b| ∂(centeredMassLaw d ν)) *
          (ν {z : ℝ | -(z) > P.l1 * P.level k}).toReal
        ≤ (ε₂ * P.level k) * (2 * P.weight k) :=
          mul_le_mul hcabs hmass ENNReal.toReal_nonneg (mul_pos hε₂ ha0).le
      _ = 2 * ε₂ * P.level k * P.weight k := by ring
      _ ≤ 2 * (green d 0 0 * (1 - P.l1) * η / 6) * P.level k * P.weight k := by
          have h1 : 2 * ε₂ ≤ 2 * (green d 0 0 * (1 - P.l1) * η / 6) := by linarith
          have h2 := mul_le_mul_of_nonneg_right h1 ha0.le
          exact mul_le_mul_of_nonneg_right h2 hω.le
      _ = η * green d 0 0 * ((1 - P.l1) * P.level k) / 3 * P.weight k := by ring
  -- step 5: the integrated profile at the coordinate
  have hprofk := hk1 (bandCoordSeq P d ν k n) ⟨hz0, hz1.trans (by norm_num)⟩
  rw [hlevel] at hprofk
  rw [hstep]
  have hkey : (meanOdometer (centeredMassLaw d ν) (n + 1) - meanOdometer (centeredMassLaw d ν) n)
        / (green d 0 0 * ((1 - P.l1) * P.level k))
        - P.weight k / (green d 0 0 * (P.theta k + 1)) * bandCoordSeq P d ν k n ^ (P.theta k + 1)
      = ((meanOdometer (centeredMassLaw d ν) (n + 1) - meanOdometer (centeredMassLaw d ν) n)
          - ∫ z, max (-z - b) 0 ∂ν) / (green d 0 0 * ((1 - P.l1) * P.level k))
        + P.weight k / green d 0 0 *
          ((∫ z, max (-z - b) 0 ∂ν) / (P.weight k * (1 - P.l1) * P.level k)
            - bandCoordSeq P d ν k n ^ (P.theta k + 1) / (P.theta k + 1)) := by
    field_simp
    ring
  rw [hkey]
  refine (abs_add_le _ _).trans ?_
  have h1 : |((meanOdometer (centeredMassLaw d ν) (n + 1) - meanOdometer (centeredMassLaw d ν) n)
        - ∫ z, max (-z - b) 0 ∂ν) / (green d 0 0 * ((1 - P.l1) * P.level k))|
      ≤ 2 * η / 3 * P.weight k := by
    rw [abs_div, abs_of_pos (mul_pos hG hD), div_le_iff₀ (mul_pos hG hD)]
    calc _ ≤ _ := hinc
      _ ≤ η * green d 0 0 * ((1 - P.l1) * P.level k) / 3 * P.weight k
          + η * green d 0 0 * ((1 - P.l1) * P.level k) / 3 * P.weight k := add_le_add hE1 hE2
      _ = 2 * η / 3 * P.weight k * (green d 0 0 * ((1 - P.l1) * P.level k)) := by ring
  have h2 : |P.weight k / green d 0 0 *
        ((∫ z, max (-z - b) 0 ∂ν) / (P.weight k * (1 - P.l1) * P.level k)
          - bandCoordSeq P d ν k n ^ (P.theta k + 1) / (P.theta k + 1))|
      ≤ η / 3 * P.weight k := by
    rw [abs_mul, abs_of_pos (div_pos hω hG)]
    calc P.weight k / green d 0 0 * |_|
        ≤ P.weight k / green d 0 0 * (green d 0 0 * η / 3) :=
          mul_le_mul_of_nonneg_left hprofk (div_nonneg hω.le hG.le)
      _ = η / 3 * P.weight k := by field_simp
  linarith

/-- **The level increment with an EXPLICIT modulus.**  The qualitative form above,
"for every `η > 0`, eventually in `k`", cannot feed the one-step increment, which
needs a rate: the conversion from an additive to a relative error costs a factor
`L_k²`, so what is required is `L_k² e_k → 0`, and a statement with no `e` has no
rate to pair with a fast `L`.

Proof.  Diagonalise the theorem above, exactly as `bandErrorSeq` does. -/
theorem bandLevel_increment_modulus (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hgap : P.lam0 < θ₀ / LatticeProb.greenRatioSup d)
    (hprof : BandIntegratedProfile P ν) (hbp : BandProfile P ν)
    (hlow : BandLowerIsolation P ν) :
    ∃ e : ℕ → ℝ, (∀ k, 0 ≤ e k) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
        bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
          |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
              - P.weight k / (green d 0 0 * (P.theta k + 1))
                * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
            ≤ e k * P.weight k := by
  have hq := bandLevel_increment_rel_error P hd ν hatom hint hmean hsq hθ₀ hexp hgap hprof hbp hlow
  -- for each `j`, an index beyond which the estimate holds at `1/(j+1)`
  have hN : ∀ j : ℕ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ n : ℕ,
      bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
        |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
            - P.weight k / (green d 0 0 * (P.theta k + 1))
              * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
          ≤ ((j : ℝ) + 1)⁻¹ * P.weight k := fun j =>
    Filter.eventually_atTop.mp (hq ((j : ℝ) + 1)⁻¹ (by positivity))
  choose N hN using hN
  -- `J k` is the last block whose starting index has been reached
  set J : ℕ → ℕ := fun k => Nat.findGreatest (fun j => N j ≤ k) k with hJ
  have hJtop : Tendsto J atTop atTop := by
    refine tendsto_atTop.mpr fun j => Filter.eventually_atTop.mpr ⟨max (N j) j, fun k hk => ?_⟩
    exact Nat.le_findGreatest (le_trans (le_max_right _ _) hk) (le_trans (le_max_left _ _) hk)
  refine ⟨fun k => ((J k : ℝ) + 1)⁻¹, fun k => by positivity, ?_, ?_⟩
  · have h1 : Tendsto (fun k => (J k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hJtop)
    exact tendsto_inv_atTop_zero.comp h1
  · filter_upwards [Filter.eventually_ge_atTop (N 0)] with k hk
    exact hN (J k) k (Nat.findGreatest_spec (P := fun j => N j ≤ k) (Nat.zero_le k) hk)

/-- **The one-step profile increment at the sandpile law, at a single index.**

Stated POINTWISE, so it is not circular with the index range, and carrying the
MODULUS and the slow-scale property explicitly, because the conversion from the
additive error to the relative error `abs_oneStep_increment_le'` wants costs a
factor `z^{-(θ+1)}`, and `hzlow` bounds that by `(2TL_k)²`.  The proof therefore
needs `L_k² e_k → 0`, which is `hLe`.  Without it the statement is false: with
`L ≡ 0` the lower bound `hzlow` degenerates and the increment fails at the last
index where the coordinate is still nonnegative. -/
theorem bandProfile_increment (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hθ1 : ∀ k, 1 ≤ P.theta k) (hθ2 : ∀ k, P.theta k ≤ 2)
    (L : ℕ → ℝ) (hLpos : ∀ k, 0 < L k) (T : ℝ) (hT : 0 < T)
    (e : ℕ → ℝ) (he0 : ∀ k, 0 ≤ e k)
    (hLe : Tendsto (fun k => L k ^ 2 * e k) atTop (𝓝 0))
    (hincr : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      bandCoordSeq P d ν k n ∈ Icc (0 : ℝ) (1 / 2) →
        |(bandCoordSeq P d ν k n - bandCoordSeq P d ν k (n + 1))
            - P.weight k / (green d 0 0 * (P.theta k + 1))
              * bandCoordSeq P d ν k n ^ (P.theta k + 1)|
          ≤ e k * P.weight k) :
    ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, ∀ i : ℕ,
        bandCoordSeq P d ν k i ∈ Icc (0 : ℝ) (1 / 2) →
          1 / (2 * T * L k) ≤ bandCoordSeq P d ν k i ^ P.theta k →
            |(bandCoordSeq P d ν k (i + 1) ^ (-(P.theta k))
                - bandCoordSeq P d ν k i ^ (-(P.theta k)))
              - P.weight k / (green d 0 0 * (1 + 1 / P.theta k))|
              ≤ η k * P.weight k := by
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  have hwt : Tendsto (fun k => P.weight k) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp P.level_tendsto)).const_mul P.c0
    simpa [Function.comp_def, BandParameters.weight] using h
  -- the relative error: the additive error `e ω` against the size `ω z^{θ+1}` of the step
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ∀ k, ε k = 12 * green d 0 0 * T ^ 2 * (L k ^ 2 * e k) :=
    ⟨fun k => 12 * green d 0 0 * T ^ 2 * (L k ^ 2 * e k), fun _ => rfl⟩
  have hε0 : ∀ k, 0 ≤ ε k := fun k => by
    have := he0 k
    have := hLpos k
    rw [hεdef]
    positivity
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have h := hLe.const_mul (12 * green d 0 0 * T ^ 2)
    rw [mul_zero] at h
    exact Filter.Tendsto.congr (fun k => (hεdef k).symm) h
  refine ⟨fun k => ε k / green d 0 0 + 8 * (1 + ε k) ^ 2 * P.weight k / green d 0 0 ^ 2, ?_, ?_⟩
  · have h1 : Tendsto (fun k => ε k / green d 0 0) atTop (𝓝 0) := by
      simpa using hεt.div_const (green d 0 0)
    have h2 : Tendsto (fun k => 8 * (1 + ε k) ^ 2 * P.weight k / green d 0 0 ^ 2) atTop (𝓝 0) := by
      have h := (((tendsto_const_nhds (x := (1 : ℝ))).add hεt).pow 2 |>.const_mul 8).mul hwt
        |>.div_const (green d 0 0 ^ 2)
      simpa using h
    simpa using h1.add h2
  · filter_upwards [hincr, hεt.eventually_lt_const one_pos,
      hwt.eventually_lt_const (show (0 : ℝ) < green d 0 0 / 4 by positivity)]
      with k hk hεk hωk i hi hlow
    obtain ⟨hz0, hz1⟩ := hi
    have hθk1 := hθ1 k
    have hθk2 := hθ2 k
    have hθ0 : 0 < P.theta k := by linarith
    have hω := P.weight_pos k
    have hL := hLpos k
    have hs : 0 < 1 / (2 * T * L k) := by positivity
    have hinc := hk i ⟨hz0, hz1⟩
    set z : ℝ := bandCoordSeq P d ν k i with hzdef
    have hzpos : 0 < z := by
      refine lt_of_le_of_ne hz0 fun h => ?_
      rw [← h, Real.zero_rpow hθ0.ne'] at hlow
      linarith
    have hz1' : z ≤ 1 := hz1.trans (by norm_num)
    have hzθ0 : 0 < z ^ P.theta k := Real.rpow_pos_of_pos hzpos _
    have hzθ1 : z ^ P.theta k ≤ z := by
      have h := Real.rpow_le_rpow_of_exponent_ge hzpos hz1' hθk1
      simpa using h
    have hzθle : z ^ P.theta k ≤ 1 := hzθ1.trans hz1'
    have hZ : z ^ (P.theta k + 1) = z ^ P.theta k * z := Real.rpow_add_one hzpos.ne' _
    have hZlow : (1 / (2 * T * L k)) * (1 / (2 * T * L k)) ≤ z ^ (P.theta k + 1) := by
      rw [hZ]
      exact mul_le_mul hlow (hlow.trans hzθ1) hs.le hzθ0.le
    have hZpos : 0 < z ^ (P.theta k + 1) := Real.rpow_pos_of_pos hzpos _
    -- `(2TL)² z^{θ+1} ≥ 1`, which is the bound `z^{-(θ+1)} ≤ (2TL)²`
    have hqZ : 1 ≤ (2 * T * L k) ^ 2 * z ^ (P.theta k + 1) := by
      have h1 : (2 * T * L k) ^ 2 * ((1 / (2 * T * L k)) * (1 / (2 * T * L k))) = 1 := by
        field_simp
      calc (1 : ℝ) = (2 * T * L k) ^ 2 * ((1 / (2 * T * L k)) * (1 / (2 * T * L k))) := h1.symm
        _ ≤ (2 * T * L k) ^ 2 * z ^ (P.theta k + 1) :=
          mul_le_mul_of_nonneg_left hZlow (by positivity)
    have hcpos : 0 < P.weight k / (green d 0 0 * (P.theta k + 1)) :=
      div_pos hω (mul_pos hG (by linarith))
    have hrel : e k * P.weight k
        ≤ ε k * (P.weight k / (green d 0 0 * (P.theta k + 1)) * z ^ (P.theta k + 1)) := by
      have hid : ε k * (P.weight k / (green d 0 0 * (P.theta k + 1)) * z ^ (P.theta k + 1))
          = 3 * (e k * P.weight k) * ((2 * T * L k) ^ 2 * z ^ (P.theta k + 1))
              / (P.theta k + 1) := by
        rw [hεdef]
        field_simp
        ring
      rw [hid, le_div_iff₀ (by linarith)]
      have hep : 0 ≤ e k * P.weight k := mul_nonneg (he0 k) hω.le
      nlinarith [mul_le_mul_of_nonneg_left hqZ hep,
        mul_nonneg hep (by linarith : 0 ≤ 3 - (P.theta k + 1))]
    have hδ := hinc.trans hrel
    have hcZ : 0 < P.weight k / (green d 0 0 * (P.theta k + 1)) * z ^ (P.theta k + 1) :=
      mul_pos hcpos hZpos
    have hδ0 : 0 ≤ z - bandCoordSeq P d ν k (i + 1) := by
      have h1 := (abs_le.mp hδ).1
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - ε k) hcZ.le]
    have hsmall : P.theta k * ((z - bandCoordSeq P d ν k (i + 1)) / z) ≤ 1 / 2 := by
      have hδle : z - bandCoordSeq P d ν k (i + 1)
          ≤ (1 + ε k) * (P.weight k / (green d 0 0 * (P.theta k + 1)) * z ^ (P.theta k + 1)) := by
        have h1 := (abs_le.mp hδ).2
        linarith
      have h1 : (z - bandCoordSeq P d ν k (i + 1)) / z
          ≤ (1 + ε k) * (P.weight k / (green d 0 0 * (P.theta k + 1)) * z ^ P.theta k) := by
        rw [div_le_iff₀ hzpos]
        calc _ ≤ _ := hδle
          _ = (1 + ε k) * (P.weight k / (green d 0 0 * (P.theta k + 1)) * z ^ P.theta k) * z := by
            rw [hZ]
            ring
      have hc2 : P.weight k / (green d 0 0 * (P.theta k + 1)) ≤ P.weight k / (2 * green d 0 0) := by
        refine div_le_div_of_nonneg_left hω.le (by positivity) ?_
        nlinarith
      have hX : P.weight k / (green d 0 0 * (P.theta k + 1)) * z ^ P.theta k
          ≤ P.weight k / (2 * green d 0 0) :=
        (mul_le_mul hc2 hzθle hzθ0.le (by positivity)).trans_eq (mul_one _)
      have hX0 : 0 ≤ P.weight k / (green d 0 0 * (P.theta k + 1)) * z ^ P.theta k :=
        mul_nonneg hcpos.le hzθ0.le
      have h3 : P.weight k / (2 * green d 0 0) ≤ 1 / 8 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      have h4 : (1 + ε k) * (P.weight k / (green d 0 0 * (P.theta k + 1)) * z ^ P.theta k)
          ≤ 1 / 4 := by
        nlinarith
      have h5 : P.theta k * ((z - bandCoordSeq P d ν k (i + 1)) / z)
          ≤ 2 * ((z - bandCoordSeq P d ν k (i + 1)) / z) :=
        mul_le_mul_of_nonneg_right hθk2 (div_nonneg hδ0 hzpos.le)
      linarith
    have h := abs_oneStep_increment_le' hθk1 hθk2 hzpos hz1' hG hω (hε0 k) hδ0 hδ hsmall
    rw [sub_sub_cancel] at h
    exact h

end Sandpile.Support
