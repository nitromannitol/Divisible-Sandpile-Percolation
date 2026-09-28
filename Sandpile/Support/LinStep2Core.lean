import Sandpile.Support.LinStep2Assembly
import Sandpile.Support.LinGaussShift
import Sandpile.Support.LinStationary

/-!
# The uniform smallness of the mean deviation over early times

This file assembles the five errors of the path-survival estimate into a single uniform bound: for
every `ε ∈ (0, 1)` and every target size, eventually in `R` the survival probability along any path
of at most `(1 - ε) n_R` steps differs from the profile `(1 - j / (R² T)) ^ κ` in mean by at most
the target. The factorization of Step 1 enters as a single hypothesis both branches of the
threshold-field dichotomy supply: for every target and every `K ≥ 1`, eventually in `R`, a family
of at most `T R²` distinct sites whose levels have threshold probability between `1 / (K R²)` and
`K / R²` factorizes up to the target, exactly in the independent branch and via the normal
comparison inequality in the Gaussian branch. Combining the two branches gives the first
conclusion of the path-survival lemma as a limit.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- **The uniform smallness of the mean deviation** (`sandpile.tex:5566-5569`): for every
`\varepsilon\in(0,1)` and every target, eventually in `R` the survival probability along any
path of at most `(1-\varepsilon)n_R` steps differs from `(1-j/(R^2T))^\kappa` in mean by at
most the target. The contact and factorization estimates may hold along any
filter of scales tending to infinity. -/
theorem eventually_uniform_survival_core [NeZero d] {l : Filter ℝ}
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (J : (Site d → ℝ) → Site d → ℝ)
    (hshift : ∀ (t : ℕ) (b : ℝ) (y : Site d),
      (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t y = 0} {σ : Site d → ℝ | b < J σ y})
        = (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t 0 = 0} {σ : Site d → ℝ | b < J σ 0}))
    (hnull : ∀ b : ℝ, NullMeasurableSet {σ : Site d → ℝ | b < J σ 0} (centeredMassLaw d ν))
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (hthresholds : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ R : ℝ in l, ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
        |(m : ℝ) * ((centeredMassLaw d ν)
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
            (green d 0 0 * κ) - 1| +
          (m : ℝ) * ((centeredMassLaw d ν)
            (symmDiff {σ | odometer σ m 0 = 0}
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0})).toReal ≤ η)
    (hfactev : ∀ theta : ℝ, 0 < theta → ∀ K : ℝ, 1 ≤ K → ∀ᶠ R : ℝ in l,
      ∀ (m : ℕ) (xs : Fin m → Site d), Function.Injective xs → (m : ℝ) ≤ T * R ^ 2 →
      ∀ lev : Fin m → ℝ,
        (∀ i, (centeredMassLaw d ν).real {σ : Site d → ℝ | lev i < J σ 0} ≤ K / R ^ 2) →
        (∀ i, 1 / (K * R ^ 2) ≤ (centeredMassLaw d ν).real
          {σ : Site d → ℝ | lev i < J σ 0}) →
        |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ i : Fin m, J σ (xs i) ≤ lev i}
          - ∏ i : Fin m, (centeredMassLaw d ν).real
            {σ : Site d → ℝ | J σ 0 ≤ lev i}| ≤ theta)
    (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (c : ℝ) (hc : 0 < c)
    (hl : l ≤ atTop := by exact le_rfl) :
    ∀ᶠ R : ℝ in l, ∀ j : ℕ, j ≤ ⌊(1 - ε) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)⌋₊ →
      ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d |
              ∀ r ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Y r)}
              (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν))
            - (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ| ∂(walkLaw d 0) ≤ c := by
  obtain ⟨hε0, hε1⟩ := hε
  have hd3 : 3 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hmono := monotone_meanOdometer_of_var hd1 ν hvar'
  have hG : (0 : ℝ) < green d 0 0 := lt_of_lt_of_le zero_lt_one (one_le_green hd3)
  have hGk : (0 : ℝ) < κ * green d 0 0 := mul_pos hκ hG
  have hL0 : (0 : ℝ) ≤ Real.log (1 / ε) := Real.log_nonneg ((one_le_div hε0).mpr hε1.le)
  obtain ⟨eta0, heta0p, heta0le, hA1, hA5⟩ :=
    exists_eta_targets κ (Real.log (1 / ε)) (c / 2) hκ hL0 (by linarith)
  obtain ⟨eta', heta'p, heta'le1, h4⟩ := exists_etaPrime_target κ (c / 2) hκ (by linarith)
  set eta : ℝ := min eta0 (1 / 2) with hetadef
  have hetap : 0 < eta := lt_min heta0p (by norm_num)
  have hetahalf : eta ≤ 1 / 2 := min_le_right _ _
  have hetale0 : eta ≤ eta0 := min_le_left _ _
  have h1 : eta * (1 + Real.log (1 / ε)) ≤ c / 2 / 5 :=
    le_trans (mul_le_mul_of_nonneg_right hetale0 (by linarith)) hA1
  have h5 : eta * κ * (1 + Real.log (1 / ε)) ≤ c / 2 / 5 := by
    refine le_trans ?_ hA5
    have := mul_le_mul_of_nonneg_right hetale0 hκ.le
    exact mul_le_mul_of_nonneg_right this (by linarith)
  set theta : ℝ := c / 2 / 5 with hthetadef
  have hthetap : 0 < theta := by positivity
  set Gk : ℝ := κ * green d 0 0 with hGkdef
  set K : ℝ := max 1 (max (4 * Gk / (ε * T)) (2 * T / Gk)) with hKdef
  have hK : 1 ≤ K := le_max_left _ _
  have hK1 : 4 * Gk / (ε * T) ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK2 : 2 * T / Gk ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hsq : Tendsto (fun R : ℝ => R ^ 2 * T) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).atTop_mul_const hT
  have hfl : Tendsto (fun R : ℝ => ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp hsq)
  filter_upwards [hthresholds ε ⟨hε0, hε1⟩ eta hetap,
    hfactev theta hthetap K hK,
    (eventually_lastVisit_real hd3 T hT ε hε0 hε1 eta' heta'p).filter_mono hl,
    (eventually_abs_profile_sub_lt T hT κ hκ.le (c / 2) (by linarith)).filter_mono hl,
    (hsq.eventually_ge_atTop 2).filter_mono hl,
    (hfl.eventually_ge_atTop (max (4 * Gk / ε) (160 * Gk ^ 2 / (ε * c)))).filter_mono hl,
    (eventually_gt_atTop (0 : ℝ)).filter_mono hl] with R h_thr h_fact h_lv h_prof h_RT h_M h_R0
  intro j hj
  have hRT0 : (0 : ℝ) < R ^ 2 * T := by linarith
  set n : ℕ := ⌊R ^ 2 * T⌋₊ with hndef
  have hnle : (n : ℝ) ≤ R ^ 2 * T := Nat.floor_le hRT0.le
  have hnlt : R ^ 2 * T < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnhalf : R ^ 2 * T / 2 ≤ (n : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hn0 : 0 < n := by exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
  have hnR0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hjnR : (j : ℝ) ≤ (1 - ε) * (n : ℝ) := by
    have h0 : (0 : ℝ) ≤ (1 - ε) * (n : ℝ) := by nlinarith
    have hcast : (j : ℝ) ≤ ((⌊(1 - ε) * ((n : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hj
    exact le_trans hcast (Nat.floor_le h0)
  have hjlt : j < n := by
    have hlt : (j : ℝ) < (n : ℝ) := by nlinarith
    exact_mod_cast hlt
  have hge : ε * (n : ℝ) ≤ ((n - j : ℕ) : ℝ) := by
    rw [cast_nat_sub_eq n j (le_of_lt hjlt)]
    nlinarith [hjnR]
  have hnj0 : (0 : ℝ) < ((n - j : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hge
  obtain ⟨hAw, hBw⟩ := window_of_thresholds n j hjlt ε hε0 hjnR eta
    (fun m => |(m : ℝ) * ((centeredMassLaw d ν)
        {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
        (green d 0 0 * κ) - 1|)
    (fun m => (m : ℝ) * ((centeredMassLaw d ν)
        (symmDiff {σ | odometer σ m 0 = 0}
          {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0})).toReal)
    (fun m => abs_nonneg _)
    (fun m => mul_nonneg (Nat.cast_nonneg m) ENNReal.toReal_nonneg) h_thr
  have hwin : ∀ r ∈ Finset.range (j + 1),
      |((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
          {σ : Site d → ℝ | stepLevel ν d n j r < J σ 0} / (κ * green d 0 0) - 1| ≤ eta := by
    intro r hr
    have hrj : r ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hAr := hAw r hrj
    rw [stepLevel_of_le ν n j r hrj, measureReal_def, mul_comm κ (green d 0 0)]
    exact hAr
  have hthr : ∀ r, r ≤ j → ((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
      (symmDiff {σ : Site d → ℝ | odometer σ (n - r) 0 = 0}
        {σ : Site d → ℝ | stepLevel ν d n j r < J σ 0}) ≤ eta := by
    intro r hrj
    have hBr := hBw r hrj
    rw [stepLevel_of_le ν n j r hrj, measureReal_def]
    exact hBr
  obtain ⟨hpiu, -⟩ := weights_of_window n j hjlt
    (fun r => (centeredMassLaw d ν).real {σ : Site d → ℝ | stepLevel ν d n j r < J σ 0})
    (κ * green d 0 0) eta hGk (by linarith) hwin
  have hpij : (centeredMassLaw d ν).real {σ : Site d → ℝ | stepLevel ν d n j j < J σ 0}
      ≤ 2 * Gk / ((n - j : ℕ) : ℝ) := hpiu j (Finset.mem_range.mpr (by omega))
  have hpi0 : Gk / (2 * (n : ℝ))
      ≤ (centeredMassLaw d ν).real {σ : Site d → ℝ | stepLevel ν d n j 0 < J σ 0} := by
    have h := weight_ge_of_abs_le (n - 0) (by omega) (κ * green d 0 0) eta
      ((centeredMassLaw d ν).real {σ : Site d → ℝ | stepLevel ν d n j 0 < J σ 0}) hGk
      hetahalf (hwin 0 (Finset.mem_range.mpr (by omega)))
    simpa [Nat.sub_zero] using h
  have hK1' : 4 * Gk ≤ K * (ε * T) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ε * T)] at hK1
    linarith
  have hK2' : 2 * T ≤ K * Gk := by
    rw [div_le_iff₀ hGk] at hK2
    linarith
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hfact : ∀ X : ℕ → Site d, ∀ (m : ℕ) (ts : Fin m → ℕ),
      Function.Injective (fun i => X (ts i)) → (m : ℝ) ≤ (j : ℝ) + 1 →
      |(centeredMassLaw d ν).real
          {σ : Site d → ℝ | ∀ i : Fin m, J σ (X (ts i)) ≤ stepLevel ν d n j (ts i)}
        - ∏ i : Fin m, (centeredMassLaw d ν).real
          {σ : Site d → ℝ | J σ 0 ≤ stepLevel ν d n j (ts i)}| ≤ theta := by
    intro X m ts hinj hmle
    refine h_fact m (fun i => X (ts i)) hinj ?_ (fun i => stepLevel ν d n j (ts i))
      (fun i => ?_) (fun i => ?_)
    · have hj1 : (j : ℝ) + 1 ≤ (n : ℝ) := by
        have : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hjlt
        exact this
      calc (m : ℝ) ≤ (j : ℝ) + 1 := hmle
        _ ≤ (n : ℝ) := hj1
        _ ≤ R ^ 2 * T := hnle
        _ = T * R ^ 2 := by ring
    · have hmono' : (centeredMassLaw d ν).real
          {σ : Site d → ℝ | stepLevel ν d n j (ts i) < J σ 0}
          ≤ (centeredMassLaw d ν).real {σ : Site d → ℝ | stepLevel ν d n j j < J σ 0} :=
        measureReal_mono
          (fun σ hσ => lt_of_le_of_lt (stepLevel_last_le ν n j (ts i) hmono) hσ)
          (measure_ne_top _ _)
      refine le_trans hmono' (le_trans hpij ?_)
      rw [div_le_div_iff₀ hnj0 hR2]
      have e1 : ε * (R ^ 2 * T / 2) ≤ ε * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hnhalf hε0.le
      have e3 : K * (ε * (R ^ 2 * T / 2)) ≤ K * ((n - j : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (le_trans e1 hge) hK0.le
      have e5 : 4 * Gk * (R ^ 2 / 2) ≤ K * (ε * T) * (R ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hK1' (by positivity)
      have e6 : K * (ε * (R ^ 2 * T / 2)) = K * (ε * T) * (R ^ 2 / 2) := by ring
      linarith [e3, e5, e6.le, e6.ge]
    · have hmono' : (centeredMassLaw d ν).real
          {σ : Site d → ℝ | stepLevel ν d n j 0 < J σ 0}
          ≤ (centeredMassLaw d ν).real
            {σ : Site d → ℝ | stepLevel ν d n j (ts i) < J σ 0} :=
        measureReal_mono
          (fun σ hσ => lt_of_le_of_lt (stepLevel_le_first ν n j (ts i) hmono) hσ)
          (measure_ne_top _ _)
      refine le_trans ?_ (le_trans hpi0 hmono')
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have f2 : 2 * T * R ^ 2 ≤ K * Gk * R ^ 2 :=
        mul_le_mul_of_nonneg_right hK2' hR2.le
      linarith [hnle, f2]
  have hMn := h_M
  have hn4 : 4 * (κ * green d 0 0) ≤ ε * (n : ℝ) := by
    have hle : 4 * Gk / ε ≤ (n : ℝ) := le_trans (le_max_left _ _) hMn
    rw [div_le_iff₀ hε0] at hle
    linarith
  have hQ : 16 * (κ * green d 0 0) ^ 2 / (ε * (n : ℝ)) ≤ theta := by
    have hle : 160 * Gk ^ 2 / (ε * c) ≤ (n : ℝ) := le_trans (le_max_right _ _) hMn
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ε * c)] at hle
    rw [hthetadef, div_le_iff₀ (by positivity : (0 : ℝ) < ε * (n : ℝ))]
    linarith [hle]
  have hmain := integral_abs_survival_sub_profile_le_steps ν J hshift hnull hmono hd3 n j
    hjlt ε hε0 hjnR κ hκ eta theta eta' hetap.le hetahalf hn4 hthr hwin hfact (h_lv j hj)
  have hsum := error_sum_le_of_targets κ (Real.log (1 / ε)) (c / 2) eta theta
    (16 * (κ * green d 0 0) ^ 2 / (ε * (n : ℝ))) eta' hκ hL0 hetap.le heta'le1 h1
    (le_refl theta) hQ h4 h5
  have hle2 : ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d |
        ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)} (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν))
      - (1 - (j : ℝ) / (n : ℝ)) ^ κ| ∂(walkLaw d 0) ≤ c / 2 := le_trans hmain hsum
  have hprofj := h_prof j hjlt
  have hfin := integral_abs_survival_sub_profile_real_le ν n j
    ((1 - (j : ℝ) / (n : ℝ)) ^ κ) ((1 - (j : ℝ) / (R ^ 2 * T)) ^ κ) (c / 2) (c / 2)
    hle2 hprofj.le
  linarith [hfin]

/-- **The uniform smallness in both branches of the threshold-field dichotomy**
(`sandpile.tex:5449-5450`, `sandpile.tex:5494-5578`).  In the independent branch the
factorization of Step 1 is exact; in the Gaussian branch it is the normal comparison
inequality applied to the levels the window hypothesis produces. -/
theorem eventually_uniform_survival [NeZero d]
    (hNormal : External.NormalComparison) (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hatom : ∀ z : ℝ, ν {z} = 0)
    (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : ((∀ σ x, J σ x = -(green d 0 0 * scenery d σ x)) ∨
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧
        ∀ σ x, J σ x = -infiniteGreenField (scenery d σ) x)))
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (hthresholds : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ R : ℝ in atTop, ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
        |(m : ℝ) * ((centeredMassLaw d ν)
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
            (green d 0 0 * κ) - 1| +
          (m : ℝ) * ((centeredMassLaw d ν)
            (symmDiff {σ | odometer σ m 0 = 0}
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0})).toReal ≤ η) :
    ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ c : ℝ, 0 < c →
      ∀ᶠ R : ℝ in atTop, ∀ j : ℕ, j ≤ ⌊(1 - ε) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)⌋₊ →
        ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d |
                ∀ r ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Y r)}
                (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν))
              - (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ| ∂(walkLaw d 0) ≤ c := by
  intro ε hε c hc
  rcases hJ with hind | ⟨⟨v, hvdef⟩, hgau⟩
  · refine eventually_uniform_survival_core hd ν hvar' J
      (fun t b y => measure_threshold_symmDiff_shift ν J hind t b y)
      (fun b => nullMeasurableSet_threshold_indep ν J hind 0 b) T hT κ hκ hthresholds
      ?_ ε hε c hc
    intro theta htheta K hK
    refine Filter.Eventually.of_forall (fun R m xs hxs _ lev _ _ => ?_)
    rw [indep_path_factorization ν J hind m xs hxs lev, sub_self, abs_zero]
    exact htheta.le
  · subst hvdef
    have hv : 0 < (v : ℝ) := by
      rcases lt_or_eq_of_le v.coe_nonneg with h | h
      · exact h
      · exfalso
        have hv0 : v = 0 := by
          have hz : (v : ℝ) = 0 := h.symm
          exact_mod_cast hz
        have hz := hatom 0
        rw [hv0, ProbabilityTheory.gaussianReal_zero_var] at hz
        rw [MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_singleton (0 : ℝ))] at hz
        exact one_ne_zero hz
    refine eventually_uniform_survival_core hd (gaussianReal 0 v) hvar' J
      (fun t b y => measure_threshold_symmDiff_shift_gauss hd v J hgau t b y)
      (fun b => nullMeasurableSet_threshold_of hd v J hgau 0 b) T hT κ hκ hthresholds
      ?_ ε hε c hc
    intro theta htheta K hK
    exact eventually_gauss_path_factorization_tails hNormal hd v hv J hgau T K hT hK htheta

/-- **`eq:dgt4-averaged-positive-path-limit`**, the first conclusion of
`lem:dgt4-path-survival` (`sandpile.tex:5464-5481`), from the window hypothesis. -/
theorem tendsto_averaged_survival_of_thresholds [NeZero d]
    (hNormal : External.NormalComparison) (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hatom : ∀ z : ℝ, ν {z} = 0)
    (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : ((∀ σ x, J σ x = -(green d 0 0 * scenery d σ x)) ∨
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧
        ∀ σ x, J σ x = -infiniteGreenField (scenery d σ) x)))
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (hthresholds : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ R : ℝ in atTop, ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
        |(m : ℝ) * ((centeredMassLaw d ν)
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
            (green d 0 0 * κ) - 1| +
          (m : ℝ) * ((centeredMassLaw d ν)
            (symmDiff {σ | odometer σ m 0 = 0}
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0})).toReal ≤ η) :
    Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d |
                ∀ r ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Y r)}
                (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν))
              - (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ| ∂(walkLaw d 0)) atTop (𝓝 0) :=
  tendsto_averaged_survival_of_uniform ν T κ hT hκ
    (eventually_uniform_survival hNormal hd ν hatom hvar' J hJ T hT κ hκ hthresholds)

end Sandpile
