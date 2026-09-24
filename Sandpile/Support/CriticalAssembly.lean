/-
The arithmetic that turns the fixed-scale bound into the statement of
`thm:critical-toppling`.

`Sandpile.exists_critical_scale_bound` reads the odometer's lower event at the
geometric scales `n_j = N q^j` and returns `κ^m` plus the Berry-Esseen
remainder.  What is left is the bookkeeping of `sandpile.tex:1735-1793`: the
standard deviation of the membrane field from below, the third-moment rate
against the Green supremum, the count of scales against `log t`, and the passage
from `κ^m` to `L^{-c}`.
-/
import Sandpile.Support.LogRates
import Sandpile.Support.ThresholdRate
import Sandpile.Support.Smoothed
import Sandpile.External.VarianceScale

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

/-- The square root of the lower half of `eq:Qt-table`. -/
theorem sqrt_greenSq_lower {cQ : ℝ} (hcQ : 0 < cQ) {n : ℕ}
    (hQ : cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2)) ≤ greenSq d n) :
    Real.sqrt cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4)) ≤ Real.sqrt (greenSq d n) := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hhalf : Real.sqrt ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2))
      = (n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0]
    congr 1
    ring
  calc Real.sqrt cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4))
      = Real.sqrt (cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2))) := by
        rw [Real.sqrt_mul hcQ.le, hhalf]
    _ ≤ Real.sqrt (greenSq d n) := Real.sqrt_le_sqrt hQ

/-- A geometric ratio below one half forces `q ≥ 2`. -/
theorem two_le_of_geomRatio_le_half {q : ℕ} (hq : 1 ≤ q) (h : geomRatio q ≤ 1 / 2) :
    2 ≤ q := by
  by_contra hcon
  have hq1 : q = 1 := by omega
  subst hq1
  rw [geomRatio] at h
  norm_num [Real.one_rpow] at h

/-- The third-moment rate at one scale, against the Green supremum. -/
theorem ratio_le_supOverSd {cQ CS : ℝ} (hcQ : 0 < cQ) (hCS : 0 ≤ CS) {n : ℕ} (hn : 1 ≤ n)
    (hQ : cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2)) ≤ greenSq d n) :
    CS * greenSupRate d n / Real.sqrt (greenSq d n)
      ≤ (CS / Real.sqrt cQ) * supOverSd d n := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hlow := Sandpile.sqrt_greenSq_lower hcQ hQ
  have hpos : (0:ℝ) < Real.sqrt cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4)) := by
    positivity
  have hnum : (0:ℝ) ≤ CS * greenSupRate d n :=
    mul_nonneg hCS (Sandpile.greenSupRate_nonneg d n)
  calc CS * greenSupRate d n / Real.sqrt (greenSq d n)
      ≤ CS * greenSupRate d n / (Real.sqrt cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4))) :=
        div_le_div_of_nonneg_left hnum hpos hlow
    _ = (CS / Real.sqrt cQ) * Sandpile.supOverSd d n := by
        rw [Sandpile.supOverSd, div_mul_eq_mul_div, mul_div_assoc]
        ring_nf

/-- The count of scales against `log t`. -/
theorem log_count_pow {q t m : ℕ} (hq : 2 ≤ q) (ht : 3 ≤ t)
    (hm : (m : ℝ) ≤ 1 + Real.log (t : ℝ) / Real.log (q : ℝ)) :
    (m : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (1 + 1 / Real.log (q : ℝ)) ^ ((3 : ℝ) / 4) * Real.log (t : ℝ) ^ ((3 : ℝ) / 4) := by
  have hq1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hlq : 0 < Real.log (q:ℝ) := Real.log_pos hq1
  have hlt : (1:ℝ) ≤ Real.log (t:ℝ) := one_le_log_of_three_le ht
  have hid : (1 + 1 / Real.log (q:ℝ)) * Real.log (t:ℝ)
      = Real.log (t:ℝ) + Real.log (t:ℝ) / Real.log (q:ℝ) := by
    field_simp
  have hstep : (m:ℝ) ≤ (1 + 1 / Real.log (q:ℝ)) * Real.log (t:ℝ) := by
    rw [hid]; linarith [hm]
  have h1 : (0:ℝ) ≤ 1 + 1 / Real.log (q:ℝ) := by positivity
  have h2 : (0:ℝ) ≤ Real.log (t:ℝ) := by linarith
  calc (m : ℝ) ^ ((3 : ℝ) / 4)
      ≤ ((1 + 1 / Real.log (q:ℝ)) * Real.log (t:ℝ)) ^ ((3 : ℝ) / 4) :=
        Real.rpow_le_rpow (Nat.cast_nonneg m) hstep (by norm_num)
    _ = (1 + 1 / Real.log (q:ℝ)) ^ ((3 : ℝ) / 4) * Real.log (t:ℝ) ^ ((3 : ℝ) / 4) :=
        Real.mul_rpow h1 h2


set_option maxHeartbeats 4000000 in
/-- **`thm:critical-toppling` in real form.**  The two-term bound of
`sandpile.tex:1735-1793`, before the passage to `ℝ≥0∞`. -/
theorem exists_critical_toppling_bound
    (hVarScale : Sandpile.External.VarianceScale)
    (hBerryEsseen : Sandpile.External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν₀ M : ℝ) (hν₀ : 0 < ν₀)
    (a : ℝ) (ha : 0 < a) (ha' : a < 4 / (4 - (d : ℝ))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → 0 < variance (id : ℝ → ℝ) ν →
      Integrable (fun z => |z| ^ 3) ν →
      ν₀ ^ 2 ≤ variance (id : ℝ → ℝ) ν →
      ∫ z, |z| ^ 3 ∂ν ≤ M * variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) →
      ∀ (t : ℕ) (L : ℝ), 3 ≤ t → 2 ≤ L → L ^ a ≤ (t : ℝ) / 2 →
        (Sandpile.centeredMassLaw d ν
            {σ | Sandpile.odometer σ t 0 ≤ (t : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4) / L}).toReal ≤
          C * L ^ (-c) + C *
            (if d = 2 then
              Real.log (t : ℝ) ^ ((7 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 2) * L ^ (a / 2)
            else
              Real.log (t : ℝ) ^ ((3 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 4) * L ^ (a / 4)) := by
  classical
  obtain ⟨cQ, CQ, hcQ, hCQ, hQ⟩ := hVarScale.1 d hd
  obtain ⟨Ccor, hCcor, hcorr⟩ := hVarScale.2.1 d hd (by omega)
  obtain ⟨CS, hCS, hSup⟩ := exists_greenTime_sup_le d hd hd3
  -- the geometric ratio
  have hεpos : (0 : ℝ) < min (1 / 2) (persistDelta / (12 * Ccor)) :=
    lt_min (by norm_num) (div_pos persistDelta_pos (by positivity))
  obtain ⟨q, hq1, hqr⟩ := exists_geomRatio_le hεpos
  have hrhalf : geomRatio q ≤ 1 / 2 := le_trans hqr (min_le_left _ _)
  have hq2 : 2 ≤ q := two_le_of_geomRatio_le_half hq1 hrhalf
  have hrho : 12 * Ccor * geomRatio q ≤ persistDelta := by
    have h := le_trans hqr (min_le_right _ _)
    have h2 : 12 * Ccor * geomRatio q ≤ 12 * Ccor * (persistDelta / (12 * Ccor)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h3 : 12 * Ccor * (persistDelta / (12 * Ccor)) = persistDelta := by
      field_simp
    linarith
  -- the Berry-Esseen constant
  have hMmom : (0 : ℝ) < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨CBE, hCBE, hcap⟩ := exists_critical_scale_bound (d := d) hBerryEsseen hd hd3 hMmom
  -- the exponents
  have hd3R : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h4d : (0 : ℝ) < 4 - (d : ℝ) := by linarith
  set β : ℝ := ((4 : ℝ) - (d : ℝ)) / 4 with hβdef
  have hβpos : 0 < β := by rw [hβdef]; linarith
  have haβ : a * β < 1 := by
    rw [lt_div_iff₀ h4d] at ha'
    rw [hβdef]
    nlinarith
  -- the standard-deviation constant
  have hK : (0 : ℝ) < ν₀ * Real.sqrt cQ := by positivity
  set K : ℝ := ν₀ * Real.sqrt cQ with hKdef
  have h2β : (0 : ℝ) < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) β
  set Kp : ℝ := (2 : ℝ) ^ β / K with hKpdef
  have hKp : 0 < Kp := by rw [hKpdef]; positivity
  obtain ⟨L0, hL02, hL0⟩ := exists_threshold hKp (by linarith : (0 : ℝ) < 1 - a * β)
  -- the exponent of the level
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq2
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  have hlogκ : 0 < -Real.log persistKappa := by
    have := Real.log_neg persistKappa_pos persistKappa_lt_one
    linarith
  set cexp : ℝ := a * (-Real.log persistKappa) / Real.log (q : ℝ) with hcexpdef
  have hcexp : 0 < cexp := by
    rw [hcexpdef]; exact div_pos (mul_pos ha hlogκ) hlogq
  set Aq : ℝ := (1 + 1 / Real.log (q : ℝ)) ^ ((3 : ℝ) / 4) with hAqdef
  have hAq : 0 < Aq := Real.rpow_pos_of_pos (by positivity) _
  have hcQs : (0 : ℝ) < Real.sqrt cQ := Real.sqrt_pos.mpr hcQ
  set Cbig : ℝ := 24 * CBE * Aq * (CS / Real.sqrt cQ) with hCbigdef
  have hCbig : 0 < Cbig := by rw [hCbigdef]; positivity
  set C : ℝ := max (max (L0 ^ cexp) Cbig) 1 with hCdef
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨cexp, C, hcexp, hC, ?_⟩
  intro ν hprob hmean hvar hint hν₀var hmom t L ht hL hLa
  have ht1 : 1 ≤ t := by omega
  have htR : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hlogt : (0 : ℝ) ≤ Real.log (t : ℝ) := Real.log_natCast_nonneg t
  have hL0R : (0 : ℝ) < L := by linarith
  -- the rate is nonnegative
  have hrate0 : (0 : ℝ) ≤
      (if d = 2 then
        Real.log (t : ℝ) ^ ((7 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 2) * L ^ (a / 2)
      else
        Real.log (t : ℝ) ^ ((3 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 4) * L ^ (a / 4)) := by
    split <;> positivity
  by_cases hLL0 : L0 ≤ L
  · -- the main case
    obtain ⟨hN2, hNup, hNlow, hNt⟩ := floor_scale_bounds ht hL ha hLa
    set N : ℕ := ⌊(t : ℝ) * L ^ (-a)⌋₊ with hNdef
    have hN1 : 1 ≤ N := by omega
    obtain ⟨m, hm1, hmle, hmgt⟩ := exists_scaleCount hq2 hN1 hNt
    have hns1 : ∀ j : Fin m, 1 ≤ N * q ^ (j : ℕ) := by
      intro j
      have : 1 ≤ q ^ (j : ℕ) := Nat.one_le_pow _ _ (by omega)
      calc 1 = 1 * 1 := by ring
        _ ≤ N * q ^ (j : ℕ) := Nat.mul_le_mul hN1 this
    have hns2 : ∀ j : Fin m, 2 ≤ N * q ^ (j : ℕ) := by
      intro j
      have : 1 ≤ q ^ (j : ℕ) := Nat.one_le_pow _ _ (by omega)
      calc 2 ≤ N * 1 := by omega
        _ ≤ N * q ^ (j : ℕ) := Nat.mul_le_mul_left _ this
    have hnsN : ∀ j : Fin m, N ≤ N * q ^ (j : ℕ) := by
      intro j
      have : 1 ≤ q ^ (j : ℕ) := Nat.one_le_pow _ _ (by omega)
      calc N = N * 1 := by ring
        _ ≤ N * q ^ (j : ℕ) := Nat.mul_le_mul_left _ this
    have hnt : ∀ j : Fin m, N * q ^ (j : ℕ) ≤ t := fun j => hmle j j.isLt
    set s : Finset (Site d) := boxFinset (0 : Site d) t with hsdef
    have hsub : ∀ j : Fin m, boxFinset (0 : Site d) (N * q ^ (j : ℕ)) ⊆ s := fun j =>
      boxFinset_mono (hnt j)
    have hQlow : ∀ n : ℕ, 2 ≤ n → cQ * ((n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2)) ≤ greenSq d n := by
      intro n hn
      have h := (hQ n hn).1
      rwa [varianceRate_eq_rpow hd hd3 n] at h
    set Msup : Fin m → ℝ := fun j => CS * greenSupRate d (N * q ^ (j : ℕ)) with hMsupdef
    have hMsup : ∀ (j : Fin m) (x : Site d), greenTime d (N * q ^ (j : ℕ)) 0 x ≤ Msup j :=
      fun j x => hSup _ 0 x
    set hv : ℝ := (t : ℝ) ^ β / L with hvdef
    have hthrle : ∀ j : Fin m, hv / membraneSd d ν (N * q ^ (j : ℕ)) ≤ 1 := by
      intro j
      have hsdpos : 0 < membraneSd d ν (N * q ^ (j : ℕ)) := membraneSd_pos ν hvar (hns1 j)
      have hsl : (2 : ℝ) ^ (-β) * ((t : ℝ) ^ β * L ^ (-(a * β))) ≤ (N : ℝ) ^ β :=
        scale_pow_lower hβpos hL ht1 hNlow
      have hNn : (N : ℝ) ^ β ≤ ((N * q ^ (j : ℕ) : ℕ) : ℝ) ^ β :=
        Real.rpow_le_rpow (Nat.cast_nonneg N) (by exact_mod_cast hnsN j) hβpos.le
      have hchain : K * ((2 : ℝ) ^ (-β) * ((t : ℝ) ^ β * L ^ (-(a * β))))
          ≤ membraneSd d ν (N * q ^ (j : ℕ)) := by
        calc K * ((2 : ℝ) ^ (-β) * ((t : ℝ) ^ β * L ^ (-(a * β))))
            ≤ K * ((N * q ^ (j : ℕ) : ℕ) : ℝ) ^ β :=
              mul_le_mul_of_nonneg_left (le_trans hsl hNn) hK.le
          _ ≤ membraneSd d ν (N * q ^ (j : ℕ)) :=
              membraneSd_lower ν hν₀ hcQ hν₀var (hQlow _ (hns2 j))
      have hth := threshold_le_of_lower (β := β) (a := a) (L := L) (K := K)
        (sd := membraneSd d ν (N * q ^ (j : ℕ))) hβpos hL ht1 hK hchain
      have hle1 : Kp * L ^ (-(1 - a * β)) ≤ 1 := hL0 L hLL0
      have hfinal : hv ≤ membraneSd d ν (N * q ^ (j : ℕ)) := by
        calc hv ≤ Kp * L ^ (-(1 - a * β)) * membraneSd d ν (N * q ^ (j : ℕ)) := hth
          _ ≤ 1 * membraneSd d ν (N * q ^ (j : ℕ)) :=
              mul_le_mul_of_nonneg_right hle1 hsdpos.le
          _ = membraneSd d ν (N * q ^ (j : ℕ)) := one_mul _
      rw [div_le_one hsdpos]
      exact hfinal
    have hmomM : ∫ z, |z| ^ 3 ∂ν ≤ max M 1 * variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) :=
      le_trans hmom (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (variance_nonneg _ _) _))
    have hcapap := hcap ν hprob hmean hvar hint hmomM Ccor hCcor.le hcorr q N
      (by omega) hN1 hrhalf hrho m t hm1 hnt s hsub Msup hMsup hv hthrle
    -- the persistence factor against a power of the level
    have hkappa : persistKappa ^ m ≤ L ^ (-cexp) := by
      have hlow2 : a * Real.log L / Real.log (q : ℝ) ≤ (m : ℝ) :=
        scaleCount_log_lower hq2 hN1 ht1 hmgt ha hL hNup
      exact pow_le_rpow_of_scales persistKappa_pos persistKappa_lt_one hq2 ha
        (by linarith) hlow2
    -- the third-moment sum
    set Ssum : ℝ := ∑ j, Msup j / Real.sqrt (greenSq d (N * q ^ (j : ℕ))) with hSsumdef
    have hSle : Ssum ≤ (CS / Real.sqrt cQ) * (6 * supOverSd d N) := by
      have hterm : ∀ j : Fin m, Msup j / Real.sqrt (greenSq d (N * q ^ (j : ℕ)))
          ≤ (CS / Real.sqrt cQ) * supOverSd d (N * q ^ (j : ℕ)) := fun j =>
        ratio_le_supOverSd hcQ hCS.le (hns1 j) (hQlow _ (hns2 j))
      calc Ssum ≤ ∑ j : Fin m, (CS / Real.sqrt cQ) * supOverSd d (N * q ^ (j : ℕ)) :=
            Finset.sum_le_sum fun j _ => hterm j
        _ = (CS / Real.sqrt cQ) * ∑ j : Fin m, supOverSd d (N * q ^ (j : ℕ)) := by
            rw [Finset.mul_sum]
        _ = (CS / Real.sqrt cQ) * ∑ j ∈ Finset.range m, supOverSd d (N * q ^ j) := by
            rw [Fin.sum_univ_eq_sum_range (fun j => supOverSd d (N * q ^ j)) m]
        _ ≤ (CS / Real.sqrt cQ) * (6 * supOverSd d N) :=
            mul_le_mul_of_nonneg_left (sum_supOverSd_geom_le hd hd3 (by omega) hN1 hrhalf m)
              (div_nonneg hCS.le (Real.sqrt_nonneg _))
    -- the count of scales against the logarithm
    have hmupper : (m : ℝ) ≤ 1 + Real.log (t : ℝ) / Real.log (q : ℝ) :=
      scaleCount_log_upper hq2 hN1 hm1 ht1 (hmle (m - 1) (by omega))
    have hm34 : (m : ℝ) ^ ((3 : ℝ) / 4) ≤ Aq * Real.log (t : ℝ) ^ ((3 : ℝ) / 4) :=
      log_count_pow hq2 ht hmupper
    have hbnn : (0 : ℝ) ≤ (CS / Real.sqrt cQ) * (6 * supOverSd d N) :=
      mul_nonneg (div_nonneg hCS.le (Real.sqrt_nonneg _))
        (by have := supOverSd_nonneg d N; linarith)
    have hlogpow : (0 : ℝ) ≤ Real.log (t : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hlogt _
    have hkey : CBE * (m : ℝ) ^ ((1 : ℝ) / 4) * (Real.sqrt (m : ℝ) * Ssum)
        ≤ CBE * (Aq * Real.log (t : ℝ) ^ ((3 : ℝ) / 4)) *
            ((CS / Real.sqrt cQ) * (6 * supOverSd d N)) := by
      have e1 : CBE * (m : ℝ) ^ ((1 : ℝ) / 4) * (Real.sqrt (m : ℝ) * Ssum)
          = CBE * ((m : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (m : ℝ)) * Ssum := by ring
      rw [e1, rpow_quarter_mul_sqrt m]
      have h34pos : (0 : ℝ) ≤ (m : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg m) _
      calc CBE * (m : ℝ) ^ ((3 : ℝ) / 4) * Ssum
          ≤ CBE * (m : ℝ) ^ ((3 : ℝ) / 4) * ((CS / Real.sqrt cQ) * (6 * supOverSd d N)) :=
            mul_le_mul_of_nonneg_left hSle (mul_nonneg hCBE.le h34pos)
        _ ≤ CBE * (Aq * Real.log (t : ℝ) ^ ((3 : ℝ) / 4)) *
              ((CS / Real.sqrt cQ) * (6 * supOverSd d N)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm34 hCBE.le) hbnn
    have hXnn : (0 : ℝ) ≤ CBE * Aq * (CS / Real.sqrt cQ) := by positivity
    have hfacnn : (0 : ℝ) ≤ CBE * (Aq * Real.log (t : ℝ) ^ ((3 : ℝ) / 4)) := by positivity
    have hLneg : (0 : ℝ) < L ^ (-cexp) := Real.rpow_pos_of_pos hL0R _
    have hCone : (1 : ℝ) ≤ C := le_max_right _ _
    have hCbC : Cbig ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
    have hkappaC : persistKappa ^ m ≤ C * L ^ (-cexp) := by
      refine hkappa.trans ?_
      calc L ^ (-cexp) = 1 * L ^ (-cexp) := (one_mul _).symm
        _ ≤ C * L ^ (-cexp) := mul_le_mul_of_nonneg_right hCone hLneg.le
    by_cases hd2 : d = 2
    · rw [if_pos hd2]
      set R : ℝ := Real.log (t : ℝ) ^ ((7 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 2) * L ^ (a / 2)
        with hRdef
      have hR0 : (0 : ℝ) ≤ R := by
        rw [hRdef]
        exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hlogt _)
          (Real.rpow_nonneg (Nat.cast_nonneg t) _)) (Real.rpow_nonneg hL0R.le _)
      have hρ : supOverSd d N
          ≤ 2 * (1 + Real.log (t : ℝ)) *
              ((t : ℝ) ^ (-((1 : ℝ) / 2)) * L ^ (a * ((1 : ℝ) / 2))) := by
        rw [hd2]
        exact supOverSd_le_scale_two hL ht1 hN1 hNt hNlow
      have hρ' : supOverSd d N
          ≤ 4 * Real.log (t : ℝ) *
              ((t : ℝ) ^ (-((1 : ℝ) / 2)) * L ^ (a * ((1 : ℝ) / 2))) := by
        have h1 := one_add_log_le_two_log ht
        have h2 : (0 : ℝ) ≤ (t : ℝ) ^ (-((1 : ℝ) / 2)) * L ^ (a * ((1 : ℝ) / 2)) := by
          exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)
            (Real.rpow_nonneg hL0R.le _)
        nlinarith [hρ, h1, h2]
      have hstep : CBE * (Aq * Real.log (t : ℝ) ^ ((3 : ℝ) / 4)) *
            ((CS / Real.sqrt cQ) * (6 * supOverSd d N)) ≤ Cbig * R := by
        have hb : (CS / Real.sqrt cQ) * (6 * supOverSd d N)
            ≤ (CS / Real.sqrt cQ) *
                (6 * (4 * Real.log (t : ℝ) *
                  ((t : ℝ) ^ (-((1 : ℝ) / 2)) * L ^ (a * ((1 : ℝ) / 2))))) :=
          mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hCS.le (Real.sqrt_nonneg _))
        have hlog74 : Real.log (t : ℝ) ^ ((3 : ℝ) / 4) * Real.log (t : ℝ)
            = Real.log (t : ℝ) ^ ((7 : ℝ) / 4) := rpow_three_quarter_mul hlogt
        have he1 : (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) := by norm_num
        have he2 : a / 2 = a * ((1 : ℝ) / 2) := by ring
        calc CBE * (Aq * Real.log (t : ℝ) ^ ((3 : ℝ) / 4)) *
              ((CS / Real.sqrt cQ) * (6 * supOverSd d N))
            ≤ CBE * (Aq * Real.log (t : ℝ) ^ ((3 : ℝ) / 4)) *
                ((CS / Real.sqrt cQ) *
                  (6 * (4 * Real.log (t : ℝ) *
                    ((t : ℝ) ^ (-((1 : ℝ) / 2)) * L ^ (a * ((1 : ℝ) / 2)))))) :=
              mul_le_mul_of_nonneg_left hb hfacnn
          _ = 24 * (CBE * Aq * (CS / Real.sqrt cQ)) *
                ((Real.log (t : ℝ) ^ ((3 : ℝ) / 4) * Real.log (t : ℝ)) *
                  (t : ℝ) ^ (-((1 : ℝ) / 2)) * L ^ (a * ((1 : ℝ) / 2))) := by ring
          _ = Cbig * R := by
              rw [hlog74, hCbigdef, hRdef, he1, he2]; ring
        
      calc (Sandpile.centeredMassLaw d ν {σ | Sandpile.odometer σ t 0 ≤ hv}).toReal
          ≤ persistKappa ^ m + CBE * (m : ℝ) ^ ((1 : ℝ) / 4) *
              (Real.sqrt (m : ℝ) * Ssum) := hcapap
        _ ≤ C * L ^ (-cexp) + Cbig * R := add_le_add hkappaC (le_trans hkey hstep)
        _ ≤ C * L ^ (-cexp) + C * R :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hCbC hR0)
    · rw [if_neg hd2]
      set R : ℝ := Real.log (t : ℝ) ^ ((3 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 4) * L ^ (a / 4)
        with hRdef
      have hR0 : (0 : ℝ) ≤ R := by
        rw [hRdef]
        exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hlogt _)
          (Real.rpow_nonneg (Nat.cast_nonneg t) _)) (Real.rpow_nonneg hL0R.le _)
      have hρ : supOverSd d N
          ≤ 2 * ((t : ℝ) ^ (-((1 : ℝ) / 4)) * L ^ (a * ((1 : ℝ) / 4))) :=
        supOverSd_le_scale_ne_two hd hd3 hd2 hL ht1 hN1 hNlow
      have hstep : CBE * (Aq * Real.log (t : ℝ) ^ ((3 : ℝ) / 4)) *
            ((CS / Real.sqrt cQ) * (6 * supOverSd d N)) ≤ Cbig * R := by
        have hb : (CS / Real.sqrt cQ) * (6 * supOverSd d N)
            ≤ (CS / Real.sqrt cQ) *
                (6 * (2 * ((t : ℝ) ^ (-((1 : ℝ) / 4)) * L ^ (a * ((1 : ℝ) / 4))))) :=
          mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hCS.le (Real.sqrt_nonneg _))
        have he1 : (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) := by norm_num
        have he2 : a / 4 = a * ((1 : ℝ) / 4) := by ring
        calc CBE * (Aq * Real.log (t : ℝ) ^ ((3 : ℝ) / 4)) *
              ((CS / Real.sqrt cQ) * (6 * supOverSd d N))
            ≤ CBE * (Aq * Real.log (t : ℝ) ^ ((3 : ℝ) / 4)) *
                ((CS / Real.sqrt cQ) *
                  (6 * (2 * ((t : ℝ) ^ (-((1 : ℝ) / 4)) * L ^ (a * ((1 : ℝ) / 4)))))) :=
              mul_le_mul_of_nonneg_left hb hfacnn
          _ = 12 * (CBE * Aq * (CS / Real.sqrt cQ)) *
                (Real.log (t : ℝ) ^ ((3 : ℝ) / 4) *
                  (t : ℝ) ^ (-((1 : ℝ) / 4)) * L ^ (a * ((1 : ℝ) / 4))) := by ring
          _ ≤ 24 * (CBE * Aq * (CS / Real.sqrt cQ)) *
                (Real.log (t : ℝ) ^ ((3 : ℝ) / 4) *
                  (t : ℝ) ^ (-((1 : ℝ) / 4)) * L ^ (a * ((1 : ℝ) / 4))) := by
              have hRR : (0 : ℝ) ≤ Real.log (t : ℝ) ^ ((3 : ℝ) / 4) *
                  (t : ℝ) ^ (-((1 : ℝ) / 4)) * L ^ (a * ((1 : ℝ) / 4)) :=
                mul_nonneg (mul_nonneg (Real.rpow_nonneg hlogt _)
                  (Real.rpow_nonneg (Nat.cast_nonneg t) _)) (Real.rpow_nonneg hL0R.le _)
              nlinarith [hXnn, hRR]
          _ = Cbig * R := by rw [hCbigdef, hRdef, he1, he2]; ring
      calc (Sandpile.centeredMassLaw d ν {σ | Sandpile.odometer σ t 0 ≤ hv}).toReal
          ≤ persistKappa ^ m + CBE * (m : ℝ) ^ ((1 : ℝ) / 4) *
              (Real.sqrt (m : ℝ) * Ssum) := hcapap
        _ ≤ C * L ^ (-cexp) + Cbig * R := add_le_add hkappaC (le_trans hkey hstep)
        _ ≤ C * L ^ (-cexp) + C * R :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hCbC hR0)
  · -- bounded levels
    have hprob1 : (Sandpile.centeredMassLaw d ν
        {σ | Sandpile.odometer σ t 0 ≤ (t : ℝ) ^ β / L}).toReal ≤ 1 := by
      have h := prob_le_one (μ := Sandpile.centeredMassLaw d ν)
        (s := {σ | Sandpile.odometer σ t 0 ≤ (t : ℝ) ^ β / L})
      have := ENNReal.toReal_mono (by norm_num) h
      simpa using this
    have hLneg : (0 : ℝ) < L ^ (-cexp) := Real.rpow_pos_of_pos hL0R _
    have h1 : (1 : ℝ) ≤ L0 ^ cexp * L ^ (-cexp) :=
      le_mul_rpow_of_le hcexp hL02 hL (not_le.mp hLL0).le
    have h2 : L0 ^ cexp ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
    have h3 : L0 ^ cexp * L ^ (-cexp) ≤ C * L ^ (-cexp) :=
      mul_le_mul_of_nonneg_right h2 hLneg.le
    nlinarith [hprob1, h1, h3, mul_nonneg hC.le hrate0]

end Sandpile
