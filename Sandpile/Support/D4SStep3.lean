/-
Step 3 of `prop:d4-superdiffusive-limit` (`sandpile.tex:3385-3404`): the
reflection window `S_R=\sum_{k<n_R}P^kr_{t_R-1-k}` is negligible in `H^{-s}(D)`
once its mean is removed.

The paper splits the second moment of the window at `A_0\log(t+2)+1`, bounding
the low part by the mean and the high part by `lem:d4-difference-tail`.  The
version of that lemma proved in this repository is the exponential moment
`\E[e^{c(D_t-A_0\log(t+2))_+}-1]\leq C(t+2)^{-2}`, and the split needs no layer
cake: `e^u-1\geq u^2/2` turns the exponential moment into a second moment of the
excess directly, and on the event that the window exceeds `A_0\log(t+2)+1` the
whole difference is at most `(A_0\log(t+2)+1)` times that excess.
-/
import Sandpile.Frozen.D4DifferenceTail
import Sandpile.Support.D4WindowMean
import Sandpile.Support.D4SStep2

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

open Sandpile.Support Sandpile.Continuum Sandpile.D4Super

/-- `e^{cu}-1 \geq c^2u^2/4` for `u \geq 0`: the exponential moment controls the
second moment with no layer cake, because `e^{x}\geq(1+x/2)^2`. -/
theorem sq_le_four_div_mul_exp_sub_one {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    u ^ 2 ≤ 4 / c ^ 2 * (Real.exp (c * u) - 1) := by
  have hcu : 0 ≤ c * u := mul_nonneg hc.le hu
  have hhalf : c * u / 2 + 1 ≤ Real.exp (c * u / 2) := by
    have h := Real.add_one_le_exp (c * u / 2)
    linarith
  have hsq : Real.exp (c * u / 2) * Real.exp (c * u / 2) = Real.exp (c * u) := by
    rw [← Real.exp_add]; ring_nf
  have hge : (c * u / 2 + 1) ^ 2 ≤ Real.exp (c * u) := by
    rw [← hsq]
    nlinarith [hhalf, hcu]
  have hc2 : (0:ℝ) < c ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
  nlinarith [hge, hcu, sq_nonneg (c * u)]

/-- **The splitting of the second moment of the window** at `A+1`
(`sandpile.tex:3394-3398`). -/
theorem window_sq_split {S Dt Y A : ℝ} (hS0 : 0 ≤ S) (hSD : S ≤ Dt)
    (hA : 0 ≤ A) (hY : Y = max 0 (Dt - A)) :
    S ^ 2 ≤ (A + 1) * S + (A + 1) ^ 2 * Y ^ 2 := by
  have hY0 : 0 ≤ Y := by rw [hY]; exact le_max_left 0 _
  rcases le_or_gt S (A + 1) with hle | hgt
  · have h1 : S ^ 2 ≤ (A + 1) * S := by nlinarith
    nlinarith [sq_nonneg Y, sq_nonneg (A + 1)]
  · have hD : A + 1 < Dt := lt_of_lt_of_le hgt hSD
    have hYv : Y = Dt - A := by
      rw [hY]; exact max_eq_right (by linarith)
    have hY1 : 1 ≤ Y := by rw [hYv]; linarith
    have hDt : Dt ≤ (A + 1) * Y := by rw [hYv]; nlinarith
    have hD0 : 0 ≤ Dt := by linarith
    nlinarith [hDt, hD0, hS0, hSD, hY1, hA]

/-- **The second moment of the excess of `u_t-V_t` over `A_0\log(t+2)`**, from
the exponential form of `lem:d4-difference-tail`. -/
theorem exists_excess_sq_bound_four (_hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    ∃ A₀ C : ℝ, 0 < A₀ ∧ 0 ≤ C ∧ ∀ t : ℕ, 2 ≤ t → ∀ x : Site 4,
      Integrable (fun ζ => (max 0 (odometerOf ζ t x - membrane ζ t x -
        A₀ * Real.log ((t : ℝ) + 2))) ^ 2) (LatticeProb.iidLaw 4 ν) ∧
      ∫ ζ, (max 0 (odometerOf ζ t x - membrane ζ t x -
        A₀ * Real.log ((t : ℝ) + 2))) ^ 2 ∂(LatticeProb.iidLaw 4 ν) ≤
          C / ((t : ℝ) + 2) ^ 2 := by
  obtain ⟨A₀, c, C, hA₀, hc, hC, htail⟩ :=
    Sandpile.Frozen.d4_difference_tail ν hprob hmean hvar hvar' θ hθ hexp
  refine ⟨A₀, 4 / c ^ 2 * C, hA₀, by positivity, ?_⟩
  intro t ht x
  set P : Measure (Site 4 → ℝ) := LatticeProb.iidLaw 4 ν with hP
  set Y : (Site 4 → ℝ) → ℝ := fun ζ =>
    max 0 (odometerOf ζ t x - membrane ζ t x - A₀ * Real.log ((t : ℝ) + 2)) with hY
  have hYm : Measurable Y := by
    rw [hY]
    exact measurable_const.max (((measurable_odometerOf t x).sub
      (measurable_membrane t x)).sub measurable_const)
  have hY0 : ∀ ζ, 0 ≤ Y ζ := fun ζ => le_max_left _ _
  -- the pointwise comparison with the exponential moment
  have hpt : ∀ ζ, ENNReal.ofReal (Y ζ ^ 2) ≤
      ENNReal.ofReal (4 / c ^ 2) * ENNReal.ofReal (Real.exp (c * Y ζ) - 1) := by
    intro ζ
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (sq_le_four_div_mul_exp_sub_one hc (hY0 ζ))
  have hlin : ∫⁻ ζ, ENNReal.ofReal (Y ζ ^ 2) ∂P ≤
      ENNReal.ofReal (4 / c ^ 2 * C / ((t : ℝ) + 2) ^ 2) := by
    have h1 : ∫⁻ ζ, ENNReal.ofReal (Y ζ ^ 2) ∂P ≤
        ∫⁻ ζ, ENNReal.ofReal (4 / c ^ 2) *
          ENNReal.ofReal (Real.exp (c * Y ζ) - 1) ∂P := lintegral_mono hpt
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
    have h2 := htail t ht x
    have h3 : ENNReal.ofReal (4 / c ^ 2) *
        ∫⁻ ζ, ENNReal.ofReal (Real.exp (c * Y ζ) - 1) ∂P ≤
        ENNReal.ofReal (4 / c ^ 2) * ENNReal.ofReal (C / ((t : ℝ) + 2) ^ 2) := by
      gcongr
    refine le_trans (le_trans h1 h3) (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  -- integrability and the Bochner integral
  have hYsq0 : 0 ≤ᵐ[P] fun ζ => Y ζ ^ 2 :=
    Filter.Eventually.of_forall fun ζ => sq_nonneg _
  have hYsqm : AEStronglyMeasurable (fun ζ => Y ζ ^ 2) P :=
    (hYm.pow_const 2).aestronglyMeasurable
  have hfin : HasFiniteIntegral (fun ζ => Y ζ ^ 2) P := by
    rw [hasFiniteIntegral_iff_ofReal hYsq0]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hint : Integrable (fun ζ => Y ζ ^ 2) P := ⟨hYsqm, hfin⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hYsq0 hYsqm]
  have hle : (∫⁻ ζ, ENNReal.ofReal (Y ζ ^ 2) ∂P).toReal ≤
      (ENNReal.ofReal (4 / c ^ 2 * C / ((t : ℝ) + 2) ^ 2)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  refine le_trans hle (le_of_eq ?_)
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- **The mesh sum of a uniformly bounded second moment.**  The box the domain
meets has `(2N+1)^4` cells with `N\leq RL+2`, so the normalisation `R^{-4}`
leaves a constant of `L` alone. -/
theorem integral_mesh_sum_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (G : Ω → Site 4 → ℝ) (V : ℝ)
    (hint : ∀ x : Site 4, Integrable (fun ω => (G ω x) ^ 2) P)
    (hV : ∀ x : Site 4, ∫ ω, (G ω x) ^ 2 ∂P ≤ V)
    (R L : ℝ) (hR : 1 ≤ R) (hL : 0 ≤ L) :
    ∫ ω, (R⁻¹ ^ 4 * ∑ x ∈ Sandpile.boxFinset (0 : Site 4) (⌈|R| * L⌉₊ + 1),
        (G ω x) ^ 2) ∂P ≤ (2 * L + 5) ^ 4 * V := by
  classical
  set N : ℕ := ⌈|R| * L⌉₊ + 1 with hN
  set s : Finset (Site 4) := Sandpile.boxFinset (0 : Site 4) N with hs
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hV0 : (0:ℝ) ≤ V := le_trans (integral_nonneg fun ω => sq_nonneg _) (hV 0)
  have hNle : ((N : ℝ)) ≤ R * L + 2 := by
    have habs : |R| = R := abs_of_pos hR0
    have hceil : (⌈R * L⌉₊ : ℝ) ≤ R * L + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    rw [hN]; push_cast; rw [habs]; linarith
  have hcard : (s.card : ℝ) = (2 * (N : ℝ) + 1) ^ 4 := by
    rw [hs, Sandpile.card_boxFinset]; push_cast; ring
  have hsum : ∫ ω, (∑ x ∈ s, (G ω x) ^ 2) ∂P ≤ (2 * (N : ℝ) + 1) ^ 4 * V := by
    rw [integral_finsetSum s (fun x _ => hint x)]
    calc ∑ x ∈ s, ∫ ω, (G ω x) ^ 2 ∂P ≤ ∑ _x ∈ s, V := Finset.sum_le_sum fun x _ => hV x
      _ = (s.card : ℝ) * V := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 * (N : ℝ) + 1) ^ 4 * V := by rw [hcard]
  rw [integral_const_mul]
  have hgeo : 2 * (N : ℝ) + 1 ≤ R * (2 * L + 5) := by nlinarith
  have hgeo0 : (0:ℝ) ≤ 2 * (N : ℝ) + 1 := by positivity
  have hpow : (2 * (N : ℝ) + 1) ^ 4 ≤ (R * (2 * L + 5)) ^ 4 := pow_le_pow_left₀ hgeo0 hgeo 4
  have hRinv : (0:ℝ) ≤ R⁻¹ ^ 4 := by positivity
  have hfin : R⁻¹ ^ 4 * ((2 * (N : ℝ) + 1) ^ 4 * V) ≤ (2 * L + 5) ^ 4 * V := by
    have h1 : R⁻¹ ^ 4 * ((2 * (N : ℝ) + 1) ^ 4 * V) ≤ R⁻¹ ^ 4 * ((R * (2 * L + 5)) ^ 4 * V) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hV0) hRinv
    have h2 : R⁻¹ ^ 4 * ((R * (2 * L + 5)) ^ 4 * V) = (2 * L + 5) ^ 4 * V := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  exact le_trans (mul_le_mul_of_nonneg_left hsum hRinv) hfin

/-- **The second moment of the reflection window**, split at `A_0\log(t+2)+1`
(`sandpile.tex:3394-3401`). -/
theorem exists_window_second_moment_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hintν : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν) :
    ∃ A₀ C : ℝ, 0 < A₀ ∧ 0 ≤ C ∧ ∀ n t : ℕ, n ≤ t → 2 ≤ t → ∀ x : Site 4,
      Integrable (fun ζ => (reflectionSum ζ n t x) ^ 2) (LatticeProb.iidLaw 4 ν) ∧
      ∫ ζ, (reflectionSum ζ n t x) ^ 2 ∂(LatticeProb.iidLaw 4 ν) ≤
        (A₀ * Real.log ((t : ℝ) + 2) + 1) *
          (∫ ζ, reflectionSum ζ n t x ∂(LatticeProb.iidLaw 4 ν))
        + (A₀ * Real.log ((t : ℝ) + 2) + 1) ^ 2 * (C / ((t : ℝ) + 2) ^ 2) := by
  haveI := hprob
  obtain ⟨A₀, C, hA₀, hC, hexc⟩ :=
    exists_excess_sq_bound_four hVS ν hprob hmean hvar hvar' θ hθ hexp
  refine ⟨A₀, C, hA₀, hC, ?_⟩
  intro n t hnt ht x
  set P : Measure (Site 4 → ℝ) := LatticeProb.iidLaw 4 ν with hP
  set A : ℝ := A₀ * Real.log ((t : ℝ) + 2) with hA
  have htR : (2:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hLg : (0:ℝ) ≤ Real.log ((t : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hA0 : (0:ℝ) ≤ A := by rw [hA]; positivity
  obtain ⟨hYint, hYbound⟩ := hexc t ht x
  set Y : (Site 4 → ℝ) → ℝ := fun ζ =>
    max 0 (odometerOf ζ t x - membrane ζ t x - A) with hY
  have hSint : Integrable (fun ζ => reflectionSum ζ n t x) P :=
    integrable_reflectionSum ν hintν hpos n t x
  have hmaj : Integrable (fun ζ => (A + 1) * reflectionSum ζ n t x + (A + 1) ^ 2 * Y ζ ^ 2) P :=
    (hSint.const_mul _).add (hYint.const_mul _)
  have hptw : ∀ ζ : Site 4 → ℝ, (reflectionSum ζ n t x) ^ 2 ≤
      (A + 1) * reflectionSum ζ n t x + (A + 1) ^ 2 * Y ζ ^ 2 := by
    intro ζ
    refine window_sq_split (reflectionSum_nonneg ζ n t x) ?_ hA0 rfl
    have h := reflectionSum_le_diffField ζ hnt x
    exact h
  have hSsqm : AEStronglyMeasurable (fun ζ => (reflectionSum ζ n t x) ^ 2) P :=
    hSint.aestronglyMeasurable.pow 2
  have hSsq : Integrable (fun ζ => (reflectionSum ζ n t x) ^ 2) P := by
    refine Integrable.mono' hmaj hSsqm (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hptw ζ
  refine ⟨hSsq, ?_⟩
  have hmono := integral_mono hSsq hmaj hptw
  rw [integral_add (hSint.const_mul _) (hYint.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  have hA1 : (0:ℝ) ≤ (A + 1) ^ 2 := sq_nonneg _
  nlinarith [hmono, mul_le_mul_of_nonneg_left hYbound hA1]

/-- **The window mean, weighted by the logarithm of the time, still vanishes**
(`sandpile.tex:3399-3401`).  This is where the second limit of
`eq:d4-superdiffusive-scale-separation` is spent. -/
theorem tendsto_log_mul_window_mean (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexpint : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hintν : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν)
    (α : ℝ) (hα : 2 < α) (A₀ : ℝ) (hA₀ : 0 ≤ A₀) :
    Tendsto (fun R : ℝ => (A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) *
        ∫ η, reflectionSum η ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ 0
          ∂(LatticeProb.iidLaw 4 ν)) atTop (𝓝 0) := by
  haveI := hprob
  obtain ⟨Cw, hCw, hmb⟩ := window_mean_bound_four hVS ν hprob hmean θ
    (∫ z, Real.exp (θ * |z|) ∂ν) hθ hexpint le_rfl hintν hpos
  have hmaj : Tendsto (fun R : ℝ => (A₀ + 1) * Cw *
      ((⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2
        / ((⌊R ^ α⌋₊ : ℝ) - (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ)))) atTop (𝓝 0) := by
    simpa using (tendsto_scale_sep_second α hα).const_mul ((A₀ + 1) * Cw)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (2:ℝ)] with R hR
    have hc0 : (0:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := Nat.cast_nonneg _
    have h1 : (0:ℝ) ≤ Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) := Real.log_nonneg (by linarith)
    have h2 : (0:ℝ) ≤ ∫ η, reflectionSum η ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ 0
        ∂(LatticeProb.iidLaw 4 ν) :=
      integral_nonneg fun η => reflectionSum_nonneg η _ _ 0
    have h3 : (0:ℝ) ≤ A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1 := by nlinarith
    exact mul_nonneg h3 h2
  · filter_upwards [eventually_ge_atTop (2:ℝ), nR_le_half_floor α hα] with R hR hhalf
    set t : ℕ := ⌊R ^ α⌋₊ with hts
    set n : ℕ := ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ with hns
    have ht4 : (4:ℝ) ≤ (t : ℝ) := four_le_floor_rpow α hα R hR
    have hnt : n ≤ t := by
      have h : (n : ℝ) ≤ (t : ℝ) := by linarith
      exact_mod_cast h
    have hcast : ((t - n : ℕ) : ℝ) = (t : ℝ) - (n : ℝ) := Nat.cast_sub hnt
    have hgap : (0:ℝ) < (t : ℝ) - (n : ℝ) := by linarith
    have hLg : (1:ℝ) ≤ Real.log ((t : ℝ) + 2) :=
      (Sandpile.log_time_bounds_four (by linarith : (3:ℝ) ≤ (t : ℝ))).2.2.1
    have hm0 : (0:ℝ) ≤ ∫ η, reflectionSum η n t 0 ∂(LatticeProb.iidLaw 4 ν) :=
      integral_nonneg fun η => reflectionSum_nonneg η _ _ 0
    have hb := hmb n t hnt 0
    rw [hcast] at hb
    have hmle : (∫ η, reflectionSum η n t 0 ∂(LatticeProb.iidLaw 4 ν)) ≤
        Cw * (n : ℝ) * Real.log ((t : ℝ) + 2) / ((t : ℝ) - (n : ℝ)) := by
      rw [le_div_iff₀ hgap]; linarith [hb]
    have hcoef : A₀ * Real.log ((t : ℝ) + 2) + 1 ≤ (A₀ + 1) * Real.log ((t : ℝ) + 2) := by
      nlinarith
    calc (A₀ * Real.log ((t : ℝ) + 2) + 1) * ∫ η, reflectionSum η n t 0
            ∂(LatticeProb.iidLaw 4 ν)
        ≤ ((A₀ + 1) * Real.log ((t : ℝ) + 2)) *
            (Cw * (n : ℝ) * Real.log ((t : ℝ) + 2) / ((t : ℝ) - (n : ℝ))) :=
          mul_le_mul hcoef hmle hm0 (by positivity)
      _ = (A₀ + 1) * Cw * ((n : ℝ) * Real.log ((t : ℝ) + 2) ^ 2 / ((t : ℝ) - (n : ℝ))) := by
          field_simp

/-- The centred reflection window `S_R-\E S_R(0)` of Step 3. -/
noncomputable def windowField (ν : Measure ℝ) (α R : ℝ) (ζ : Site 4 → ℝ) : Site 4 → ℝ :=
  fun x => reflectionSum ζ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x -
    ∫ η, reflectionSum η ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ 0
      ∂(LatticeProb.iidLaw 4 ν)

/-- **Step 3 of `prop:d4-superdiffusive-limit`** (`sandpile.tex:3385-3404`).  At
superdiffusive times the `ω`-representative of the rescaled centred window tends
to zero in probability in `H^{-s}(D)`. -/
theorem tendsto_step3_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hintν : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν)
    {D : Set (Space 4)} (hD : IsDomain D) {w : Space 4 → ℝ} (hw : IsAveragingDensity D w)
    {α : ℝ} (hα : 2 < α) {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => LatticeProb.iidLaw 4 ν
      {ζ | ENNReal.ofReal ε <
        negSobolevNorm 4 s D (omegaRep D w (latticePairing R (windowField ν α R ζ)))})
      atTop (𝓝 0) := by
  classical
  haveI := hprob
  set P : Measure (Site 4 → ℝ) := LatticeProb.iidLaw 4 ν with hP
  obtain ⟨A₀, Cx, hA₀, hCx, hwin⟩ :=
    exists_window_second_moment_four hVS ν hprob hmean hvar hvar' θ hθ hexp hintν hpos
  obtain ⟨K, L, hK0, hL0, hKb⟩ := exists_negSobolevNorm_omegaRep_le (d := 4) hs.le hD hw
  set mm : ℝ → ℝ := fun R =>
    ∫ η, reflectionSum η ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ 0 ∂P with hmm
  set Y : ℝ → (Site 4 → ℝ) → ℝ := fun R ζ =>
    R⁻¹ ^ 4 * ∑ x ∈ Sandpile.boxFinset (0 : Site 4) (⌈|R| * L⌉₊ + 1),
      (windowField ν α R ζ x) ^ 2 with hY
  set V : ℝ → ℝ := fun R =>
    2 * ((A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) * mm R + (A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) ^ 2 * (Cx / ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2))
      + 2 * (mm R) ^ 2 with hV
  set B : ℝ → ℝ := fun R => K ^ 2 * ((2 * L + 5) ^ 4 * V R) with hB
  -- the scales
  have hev : ∀ᶠ R : ℝ in atTop, (2:ℝ) ≤ R ∧
      1 ≤ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ∧
      ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ≤ ⌊R ^ α⌋₊ ∧
      3 ≤ ⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ := eventually_step2_scales α hα
  -- the uniform second moment of the centred window
  have hunif : ∀ R : ℝ, 2 ≤ R → ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ≤ ⌊R ^ α⌋₊ →
      (∀ x : Site 4, Integrable (fun ζ => (windowField ν α R ζ x) ^ 2) P) ∧
      (∀ x : Site 4, ∫ ζ, (windowField ν α R ζ x) ^ 2 ∂P ≤ V R) := by
    intro R hR hnt
    have ht2 : 2 ≤ ⌊R ^ α⌋₊ := by
      have h4 : (4:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := four_le_floor_rpow α hα R hR
      have : (2:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := by linarith
      exact_mod_cast this
    have hcon : ∀ x : Site 4, (∀ ζ : Site 4 → ℝ, (windowField ν α R ζ x) ^ 2 ≤
        2 * (reflectionSum ζ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x) ^ 2
          + 2 * (mm R) ^ 2) := by
      intro x ζ
      show (reflectionSum ζ _ _ x - mm R) ^ 2 ≤ _
      nlinarith [sq_nonneg (reflectionSum ζ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x
        + mm R)]
    have hSint : ∀ x : Site 4, Integrable (fun ζ => reflectionSum ζ
        ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x) P :=
      fun x => integrable_reflectionSum ν hintν hpos _ _ x
    have hmajx : ∀ x : Site 4, Integrable (fun ζ =>
        2 * (reflectionSum ζ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x) ^ 2
          + 2 * (mm R) ^ 2) P := by
      intro x
      exact ((hwin _ _ hnt ht2 x).1.const_mul 2).add (integrable_const _)
    have hwf : ∀ x : Site 4, Integrable (fun ζ => (windowField ν α R ζ x) ^ 2) P := by
      intro x
      refine Integrable.mono' (hmajx x)
        (((hSint x).aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2)
        (Filter.Eventually.of_forall fun ζ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hcon x ζ
    refine ⟨hwf, fun x => ?_⟩
    obtain ⟨hSsq, hSb⟩ := hwin _ _ hnt ht2 x
    have hx0 : (∫ ζ, reflectionSum ζ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ x ∂P)
        = mm R := by
      have e1 := integral_reflectionSum (d := 4) (by norm_num) ν hintν hmean hpos x
        ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ hnt
      have e2 := integral_reflectionSum (d := 4) (by norm_num) ν hintν hmean hpos
        (0 : Site 4) ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ⌊R ^ α⌋₊ hnt
      simp only [hmm, hP]
      rw [e1, e2]
    have hmono := integral_mono (hwf x) (hmajx x) (hcon x)
    have hconst : ∫ _ζ : Site 4 → ℝ, 2 * (mm R) ^ 2 ∂P = 2 * (mm R) ^ 2 := by
      rw [hP]; simp
    rw [integral_add ((hwin _ _ hnt ht2 x).1.const_mul 2) (integrable_const _),
      integral_const_mul, hconst] at hmono
    rw [hx0] at hSb
    rw [hV]
    linarith [hmono, hSb]
  -- Markov
  refine tendsto_measure_gt_of_tendsto_bound P _ Y B (fun _ => K)
    (Filter.Eventually.of_forall fun _ => hK0) ?_ ?_ ?_ ?_ ?_ hε
  · intro R ζ
    rw [hY]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => sq_nonneg _)
  · filter_upwards [hev] with R hRs
    obtain ⟨hR2, hn1, hnt, h3⟩ := hRs
    rw [hY]
    exact (integrable_finsetSum _ (fun x _ => (hunif R hR2 hnt).1 x)).const_mul _
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR0 ζ
    rw [hY]
    exact hKb R hR0 _
  · filter_upwards [hev] with R hRs
    obtain ⟨hR2, hn1, hnt, h3⟩ := hRs
    obtain ⟨hi, hVb⟩ := hunif R hR2 hnt
    have hb := integral_mesh_sum_le P (fun ζ x => windowField ν α R ζ x) (V R) hi hVb
      R L (by linarith) hL0
    rw [hB, hY]
    exact mul_le_mul_of_nonneg_left hb (sq_nonneg K)
  · rw [hB]
    have h1 : Tendsto (fun R : ℝ => (A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) * mm R) atTop (𝓝 0) :=
      tendsto_log_mul_window_mean hVS ν hprob hmean θ hθ hexp hintν hpos α hα A₀ hA₀.le
    have h0 : Tendsto mm atTop (𝓝 0) :=
      tendsto_window_mean_four hVS ν hprob hmean θ (∫ z, Real.exp (θ * |z|) ∂ν) hθ hexp
        le_rfl hintν hpos α hα 0
    have h2 : Tendsto (fun R : ℝ => (A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) ^ 2 *
        (Cx / ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2)) atTop (𝓝 0) := by
      have hT : Tendsto (fun R : ℝ => ((⌊R ^ α⌋₊ : ℝ) + 2)) atTop atTop := by
        have hpow : Tendsto (fun R : ℝ => R ^ α) atTop atTop := tendsto_rpow_atTop (by linarith)
        refine tendsto_atTop_mono' atTop ?_ hpow
        filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
        have h := Nat.lt_floor_add_one (R ^ α)
        linarith
      have hbase : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) := by
        simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have hsq2 : Tendsto (fun T : ℝ => Real.log T ^ 2 / T ^ 2) atTop (𝓝 0) := by
        have h := hbase.pow 2
        simpa [div_pow] using h
      have hlog : Tendsto (fun R : ℝ => Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2 /
          ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2) atTop (𝓝 0) := hsq2.comp hT
      have hmaj : Tendsto (fun R : ℝ => Cx *
          ((A₀ + 1) ^ 2 * (Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2 /
            ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2))) atTop (𝓝 0) := by
        simpa using (hlog.const_mul ((A₀ + 1) ^ 2)).const_mul Cx
      refine squeeze_zero' ?_ ?_ hmaj
      · filter_upwards [eventually_ge_atTop (2:ℝ)] with R hR
        exact mul_nonneg (sq_nonneg _) (div_nonneg hCx (by positivity))
      · filter_upwards [eventually_ge_atTop (2:ℝ)] with R hR
        have ht4 : (4:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := four_le_floor_rpow α hα R hR
        have hLg1 : (1:ℝ) ≤ Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) :=
          (Sandpile.log_time_bounds_four (by linarith : (3:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ))).2.2.1
        have hcoef : A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1 ≤
            (A₀ + 1) * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) := by nlinarith
        have hcoef0 : (0:ℝ) ≤ A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1 := by nlinarith
        have hCxT : (0:ℝ) ≤ Cx / ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2 := div_nonneg hCx (by positivity)
        have hsq : (A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) ^ 2 ≤
            ((A₀ + 1) * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2)) ^ 2 := pow_le_pow_left₀ hcoef0 hcoef 2
        have hexp2 : ((A₀ + 1) * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2)) ^ 2
            = (A₀ + 1) ^ 2 * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2 := by ring
        calc (A₀ * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) + 1) ^ 2 *
              (Cx / ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2)
            ≤ ((A₀ + 1) ^ 2 * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2) *
                (Cx / ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2) := by
              rw [← hexp2]; exact mul_le_mul_of_nonneg_right hsq hCxT
          _ = Cx * ((A₀ + 1) ^ 2 * (Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2 /
                ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2)) := by ring
    have hsum : Tendsto V atTop (𝓝 0) := by
      rw [hV]
      have h3 := (h1.add h2).const_mul 2
      have h4 := (h0.mul h0).const_mul 2
      have h5 := h3.add h4
      simpa [pow_two] using h5
    have h6 := (hsum.const_mul ((2 * L + 5) ^ 4)).const_mul (K ^ 2)
    simpa using h6

end Sandpile
