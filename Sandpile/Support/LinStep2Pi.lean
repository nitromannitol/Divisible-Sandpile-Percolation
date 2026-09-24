/-
The connectors Step 2 of `lem:dgt4-path-survival` needs between the paper's data and the
one-path chain (`sandpile.tex:5529-5571`).

Four are recorded here.

`measureReal_le_eq_one_sub` is the complement identity the paper writes as
`\P(J(0)\leq b)=1-\pi`.  The threshold event of the Gaussian branch is only NULL measurable,
since the Green field is defined by a case split on the existence of the box limit, so the
identity is read through `measure_compl₀`; `nullMeasurableSet_threshold_field` supplies the
null measurability in the independent branch, and `Support/LinThresholdNull.lean` in
the Gaussian one.

`weight_ge_of_abs_le` is the lower half of the weight asymptotic `\pi_{R,r}=G(0,0)\kappa/(n_R-r)(1+o(1))`,
the companion of `weight_le_of_abs_le`; Step 1 needs it because the normal comparison
inequality is applied only to levels whose tail is between `1/(KR^2)` and `K/R^2`.

`sqrt_le_of_gauss_tail_lt` removes the remaining level hypothesis of Step 1: a level whose
Gaussian tail is below `e^{-2}/\sqrt{2\pi}` is at least one standard deviation, because the
tail at one standard deviation is at least that number.  With it,
`eventually_gauss_path_factorization_tails` is Step 1 with the two tail bounds alone.

`stepLevel` is the paper's level `b_r=\E u_{n-r-1}(0)` of `sandpile.tex:5532`, clamped at the
path length `j`.  The clamp changes nothing for `r\leq j`, which is the only range the
threshold replacement and the weight asymptotic use, and it makes every level of every index
of `ℕ` lie between `\E u_{n-j-1}(0)` and `\E u_{n-1}(0)`, which is what makes the tail bounds
Step 1 asks for hold at EVERY index rather than only along the last visits.
-/
import Sandpile.Support.LinStep2Profile
import Sandpile.Support.LinStep1Bridge
import Sandpile.Support.LinThresholdNull

open LatticeProb.GaussTail

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### The complement identity and the null measurability behind it -/

/-- `\P(J(0)\leq b)=1-\P(J(0)>b)` for a null measurable threshold event. -/
theorem measureReal_le_eq_one_sub {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsProbabilityMeasure mu] (f : alpha → ℝ) (b : ℝ)
    (h : NullMeasurableSet {z : alpha | b < f z} mu) :
    mu.real {z : alpha | f z ≤ b} = 1 - mu.real {z : alpha | b < f z} := by
  have hcompl : {z : alpha | f z ≤ b} = {z : alpha | b < f z}ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  rw [hcompl, measureReal_def, measure_compl₀ h (measure_ne_top _ _), measure_univ,
    ENNReal.toReal_sub_of_le (prob_le_one) (by norm_num), ENNReal.toReal_one]
  rfl

/-- The threshold event of the independent branch is measurable: `J(x)` is a continuous
function of the scenery at `x`. -/
theorem nullMeasurableSet_threshold_indep (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : ∀ σ x, J σ x = -(green d 0 0 * scenery d σ x)) (x : Site d) (b : ℝ) :
    NullMeasurableSet {σ : Site d → ℝ | b < J σ x} (centeredMassLaw d ν) := by
  have hset : {σ : Site d → ℝ | b < J σ x}
      = {σ : Site d → ℝ | b < -(green d 0 0 * scenery d σ x)} := by
    ext σ
    simp only [Set.mem_setOf_eq, hJ]
  rw [hset]
  refine MeasurableSet.nullMeasurableSet (measurableSet_lt measurable_const ?_)
  exact (((measurable_pi_apply x).comp (measurable_scenery d)).const_mul (green d 0 0)).neg

/-! ### The lower half of the weight asymptotic -/

/-- The companion of `weight_le_of_abs_le`: a relative error at most `1/2` in
`m\pi/(G(0,0)\kappa)` gives `\pi\geq G(0,0)\kappa/(2m)`. -/
theorem weight_ge_of_abs_le (m : ℕ) (hm : 0 < m) (Gk eta pi : ℝ) (hGk : 0 < Gk)
    (heta : eta ≤ 1 / 2) (h : |(m : ℝ) * pi / Gk - 1| ≤ eta) :
    Gk / (2 * (m : ℝ)) ≤ pi := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlb : -eta ≤ (m : ℝ) * pi / Gk - 1 := (abs_le.mp h).1
  have h2 : (1 : ℝ) / 2 ≤ (m : ℝ) * pi / Gk := by linarith
  rw [le_div_iff₀ hGk] at h2
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))]
  nlinarith [h2]

/-! ### The monotone levels -/

/-- The mean odometer is monotone in the number of relaxation steps whenever the one-site law
has finite variance, which is the standing hypothesis of the subsection. -/
theorem monotone_meanOdometer_of_var (hd1 : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hvar' : evariance (id : ℝ → ℝ) ν < ⊤) :
    Monotone (fun t : ℕ => meanOdometer (centeredMassLaw d ν) t) := by
  have hsq : MemLp (id : ℝ → ℝ) 2 ν :=
    (ProbabilityTheory.evariance_lt_top_iff_memLp aestronglyMeasurable_id).mp hvar'
  have hint : Integrable (id : ℝ → ℝ) ν := hsq.integrable (by norm_num)
  have hpos : Integrable (fun z : ℝ => max z 0) ν := by
    refine Integrable.mono' hint.abs
      (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
    exact max_le (le_abs_self z) (abs_nonneg z)
  exact meanOdometer_mono hd1 ν hpos

/-! ### `lem:dgt4-weighted-last-visits` along the diffusive scale -/

/-- `lem:dgt4-weighted-last-visits` read along `n_R=\lfloor R^2T\rfloor`. -/
theorem eventually_lastVisit_real [NeZero d] (hd3 : 3 ≤ d) (T : ℝ) (hT : 0 < T)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ R : ℝ in atTop, ∀ j : ℕ, j ≤ ⌊(1 - ε) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)⌋₊ →
      ∫ X, |green d 0 0 * lvSum ⌊R ^ 2 * T⌋₊ j X
          + Real.log (1 - (j : ℝ) / ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ))| ∂(walkLaw d 0) ≤ η := by
  have hsq : Tendsto (fun R : ℝ => R ^ 2 * T) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).atTop_mul_const hT
  have hfl : Tendsto (fun R : ℝ => ⌊R ^ 2 * T⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hsq
  exact hfl.eventually (lastVisit_eventually (d := d) hd3 hε0 hε1 hη)

/-! ### Step 1 with the two tail bounds alone -/

/-- A level whose Gaussian tail is below `e^{-2}/\sqrt{2\pi}` is at least one standard
deviation, because the tail at one standard deviation is at least that number. -/
theorem sqrt_le_of_gauss_tail_lt {v : ℝ≥0} (hv : 0 < (v : ℝ)) (a q : ℝ)
    (hup : (gaussianReal 0 v).real (Set.Ioi a) ≤ q)
    (hq : q < Real.exp (-2) / Real.sqrt (2 * Real.pi)) :
    Real.sqrt (v : ℝ) ≤ a := by
  by_contra hcon
  rw [not_le] at hcon
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hv
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hv
  have hmono : (gaussianReal 0 v).real (Set.Ioi (Real.sqrt (v : ℝ)))
      ≤ (gaussianReal 0 v).real (Set.Ioi a) :=
    measureReal_mono (Set.Ioi_subset_Ioi hcon.le) (measure_ne_top _ _)
  have hlow := gaussianReal_real_Ioi_ge hv (le_refl (Real.sqrt (v : ℝ)))
  have hsq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt hv.le
  have hhalf : (v : ℝ) / (2 * (v : ℝ)) = 1 / 2 := by
    rw [div_eq_iff (by positivity : (2 * (v : ℝ)) ≠ 0)]
    ring
  have hval : Real.sqrt (v : ℝ) / Real.sqrt (v : ℝ)
      * Real.exp (-(Real.sqrt (v : ℝ) ^ 2 / (2 * (v : ℝ))) - 3 / 2) / Real.sqrt (2 * Real.pi)
      = Real.exp (-2) / Real.sqrt (2 * Real.pi) := by
    rw [div_self (ne_of_gt hs), one_mul, hsq, hhalf]
    norm_num
  rw [hval] at hlow
  linarith

/-- **Step 1 of `lem:dgt4-path-survival`, Gaussian branch, with the two tail bounds alone.**
The level bound `\sqrt{\Var J(0)}\leq b` of `eventually_gauss_path_factorization_of_field`
is implied by the upper tail bound once `K/R^2` is below `e^{-2}/\sqrt{2\pi}`. -/
theorem eventually_gauss_path_factorization_tails
    (hNormal : External.NormalComparison) (hd : 5 ≤ d) (v : ℝ≥0) (hv : 0 < (v : ℝ))
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : ∀ σ x, J σ x = -infiniteGreenField (scenery d σ) x)
    (A K : ℝ) (hA : 0 < A) (hK : 1 ≤ K) {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ R : ℝ in atTop, ∀ (m : ℕ) (xs : Fin m → Site d), Function.Injective xs →
      (m : ℝ) ≤ A * R ^ 2 →
      ∀ c : Fin m → ℝ,
        (∀ i, (centeredMassLaw d (gaussianReal 0 v)).real
            {σ : Site d → ℝ | c i < J σ 0} ≤ K / R ^ 2) →
        (∀ i, 1 / (K * R ^ 2) ≤ (centeredMassLaw d (gaussianReal 0 v)).real
            {σ : Site d → ℝ | c i < J σ 0}) →
        |(centeredMassLaw d (gaussianReal 0 v)).real
              {σ : Site d → ℝ | ∀ i : Fin m, J σ (xs i) ≤ c i}
            - ∏ i : Fin m, (centeredMassLaw d (gaussianReal 0 v)).real
              {σ : Site d → ℝ | J σ 0 ≤ c i}| ≤ theta := by
  have hgs : (0 : ℝ) < greenSqSum d := lt_of_lt_of_le zero_lt_one (one_le_greenSqSum hd)
  have hw : (0 : ℝ) < (v : ℝ) * greenSqSum d := by positivity
  have hwc : ((((v : ℝ) * greenSqSum d).toNNReal : ℝ≥0) : ℝ) = (v : ℝ) * greenSqSum d :=
    Real.coe_toNNReal _ hw.le
  have hp0 : (0 : ℝ) < Real.exp (-2) / Real.sqrt (2 * Real.pi) := by positivity
  have htend : Tendsto (fun R : ℝ => K / R ^ 2) atTop (𝓝 0) :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).const_div_atTop K
  have hsmall : ∀ᶠ R : ℝ in atTop, K / R ^ 2 < Real.exp (-2) / Real.sqrt (2 * Real.pi) :=
    htend.eventually (eventually_lt_nhds hp0)
  filter_upwards [eventually_gauss_path_factorization_of_field hNormal hd v hv J hJ A K hA hK
    htheta, hsmall] with R hR hRs
  intro m xs hxs hm c hup hlow
  refine hR m xs hxs hm c (fun i => ?_) hup hlow
  have hev : {σ : Site d → ℝ | c i < J σ 0}
      = {σ : Site d → ℝ | c i < -infiniteGreenField (scenery d σ) 0} := by
    ext σ
    simp only [Set.mem_setOf_eq, hJ]
  have hi : (gaussianReal 0 (((v : ℝ) * greenSqSum d).toNNReal)).real (Set.Ioi (c i))
      ≤ K / R ^ 2 := by
    rw [← measureReal_threshold_gt_gauss hd v (c i), ← hev]
    exact hup i
  have hfin := sqrt_le_of_gauss_tail_lt (v := ((v : ℝ) * greenSqSum d).toNNReal)
    (by rw [hwc]; exact hw) (c i) (K / R ^ 2) hi hRs
  rwa [hwc] at hfin

/-! ### The clamped levels -/

/-- The paper's levels `b_r = \E u_{n-r-1}(0)` of `sandpile.tex:5527`, clamped at the path
length `j`.  For `r\leq j` this is the paper's level; beyond `j` it repeats the level at `j`,
so that every index carries a level between `\E u_{n-j-1}(0)` and `\E u_{n-1}(0)`. -/
noncomputable def stepLevel (ν : Measure ℝ) (d n j r : ℕ) : ℝ :=
  meanOdometer (centeredMassLaw d ν) (n - min r j - 1)

/-- Below the path length the clamp does nothing. -/
theorem stepLevel_of_le (ν : Measure ℝ) (n j r : ℕ) (hr : r ≤ j) :
    stepLevel ν d n j r = meanOdometer (centeredMassLaw d ν) (n - r - 1) := by
  rw [stepLevel, min_eq_left hr]

/-- The clamped levels are antitone, which is what the reduction to last visits needs. -/
theorem antitone_stepLevel (ν : Measure ℝ) (n j : ℕ)
    (hmono : Monotone (fun t : ℕ => meanOdometer (centeredMassLaw d ν) t)) :
    Antitone (stepLevel ν d n j) := by
  intro r s hrs
  exact hmono (by omega)

/-- Every clamped level is at least the level at the path length. -/
theorem stepLevel_last_le (ν : Measure ℝ) (n j r : ℕ)
    (hmono : Monotone (fun t : ℕ => meanOdometer (centeredMassLaw d ν) t)) :
    stepLevel ν d n j j ≤ stepLevel ν d n j r := hmono (by omega)

/-- Every clamped level is at most the level at time zero. -/
theorem stepLevel_le_first (ν : Measure ℝ) (n j r : ℕ)
    (hmono : Monotone (fun t : ℕ => meanOdometer (centeredMassLaw d ν) t)) :
    stepLevel ν d n j r ≤ stepLevel ν d n j 0 := hmono (by omega)

end Sandpile
