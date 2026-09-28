import Sandpile.Support.CrudeIncrement
import Sandpile.Frozen.DGT4GreenSceneryTail

/-!
# The refined increment bound

The refined increment bound `eq:dgt4-reduction-increment` of `sandpile.tex:4503-4582` and the
resulting refined upper bound.

Iterating `u_{n+1} ≥ ζ + P u_n` peels the last `m` steps off the odometer:
`ζ(0) + P u_t(0) ≥ ∑_{k≤m} P^k ζ(0) + P^{m+1} u_{t-m}(0)`, and the first sum is the Green
average `∑_y g_{m+1}(0,y) ζ(y)`. With `m` proportional to the level `h`, the mean moves by at
most `h/8` over the last `m` steps, so the event that `ζ(0)+Pu_t(0)` falls `h` below the mean
forces one of the two summands to fall `7h/16` below its own mean; the first is
`lem:dgt4-stretched-green-scenery-tail` and the second is `lem:dgt4-smoothed-odometer-tail`.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### Algebra of the averaging operator and its iterates -/

/-- The neighborhood-average operator `avg` is additive: `avg (f + g) = avg f + avg g`, by
splitting the defining sum over the `2d` neighbors. -/
theorem avg_add (f g : Site d → ℝ) (x : Site d) :
    avg (fun y => f y + g y) x = avg f x + avg g x := by
  show (∑ i : Fin d, ((f (x + unit i) + g (x + unit i)) + (f (x - unit i) + g (x - unit i))))
      / (2 * (d : ℝ))
    = (∑ i : Fin d, (f (x + unit i) + f (x - unit i))) / (2 * (d : ℝ))
      + (∑ i : Fin d, (g (x + unit i) + g (x - unit i))) / (2 * (d : ℝ))
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The `k`-fold iterate of `avg` is additive, extending `avg_add` to `avg^[k]` by induction
on `k`. -/
theorem avg_iterate_add : ∀ (k : ℕ) (f g : Site d → ℝ) (x : Site d),
    (avg^[k] fun y => f y + g y) x = (avg^[k] f) x + (avg^[k] g) x := by
  intro k
  induction k with
  | zero => intro f g x; simp
  | succ n ih =>
      intro f g x
      have h : avg (fun y => f y + g y) = fun z => avg f z + avg g z := funext (avg_add f g)
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, h]
      exact ih (avg f) (avg g) x

/-- The `k`-fold iterate of `avg` is monotone: a pointwise inequality `f ≤ g` is preserved by
`avg^[k]`, proved by induction on `k` using that `avg` itself preserves the order
(`avg_mono_le`). -/
theorem avg_iterate_mono : ∀ (k : ℕ) {f g : Site d → ℝ}, (∀ y, f y ≤ g y) →
    ∀ x, (avg^[k] f) x ≤ (avg^[k] g) x := by
  intro k
  induction k with
  | zero => intro f g h x; exact h x
  | succ n ih =>
      intro f g h x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih (fun y => avg_mono_le h y) x

/-! ### Peeling the last steps off the odometer -/

/-- **The iteration inequality.**  `ζ(0) + P u_{n+m}(0) ≥ ∑_{k≤m} P^k ζ(0) +
P^{m+1} u_n(0)`, from `u_{n+1} ≥ ζ + P u_n`. -/
theorem odometerOf_iterate_lower (ζ : Site d → ℝ) :
    ∀ (m n : ℕ),
      (∑ k ∈ Finset.range (m + 1), (avg^[k] ζ) 0) + (avg^[m + 1] (odometerOf ζ n)) 0
        ≤ ζ 0 + avg (odometerOf ζ (n + m)) 0 := by
  intro m
  induction m with
  | zero =>
      intro n
      simp
  | succ m ih =>
      intro n
      have hstep : ∀ y : Site d, ζ y + avg (odometerOf ζ n) y ≤ odometerOf ζ (n + 1) y := by
        intro y
        show _ ≤ max 0 (ζ y + avg (odometerOf ζ n) y)
        exact le_max_right _ _
      have h1 : (avg^[m + 1] fun y => ζ y + avg (odometerOf ζ n) y) 0
          ≤ (avg^[m + 1] (odometerOf ζ (n + 1))) 0 := avg_iterate_mono (m + 1) hstep 0
      have h2 : (avg^[m + 1] fun y => ζ y + avg (odometerOf ζ n) y) 0
          = (avg^[m + 1] ζ) 0 + (avg^[m + 2] (odometerOf ζ n)) 0 := by
        rw [show (avg^[m + 2] (odometerOf ζ n)) = avg^[m + 1] (avg (odometerOf ζ n)) from
              Function.iterate_succ_apply avg (m + 1) (odometerOf ζ n)]
        exact avg_iterate_add (m + 1) ζ (avg (odometerOf ζ n)) 0
      have hIH := ih (n + 1)
      have hidx : n + 1 + m = n + (m + 1) := by omega
      rw [hidx] at hIH
      rw [Finset.sum_range_succ]
      have hkey : (avg^[m + 1] ζ) 0 + (avg^[m + 2] (odometerOf ζ n)) 0
          ≤ (avg^[m + 1] (odometerOf ζ (n + 1))) 0 := by rw [← h2]; exact h1
      linarith [hIH, hkey]

/-- **The Green identity.**  `∑_{k<m} P^k ζ(0) = ∑_y g_m(0,y) ζ(y)`. -/
theorem sum_avg_iterate_eq_tsum_greenTime (m : ℕ) (ζ : Site d → ℝ) :
    ∑ k ∈ Finset.range m, (avg^[k] ζ) 0 = ∑' y : Site d, greenTime d m 0 y * ζ y := by
  have h1 : ∀ k ∈ Finset.range m, (avg^[k] ζ) 0 = ∑' y : Site d, heatKernel d k 0 y * ζ y :=
    fun k _ => avg_iterate k ζ 0
  rw [Finset.sum_congr rfl h1,
    ← Summable.tsum_finsetSum fun k (_ : k ∈ Finset.range m) => summable_heatKernel_mul k 0 ζ]
  refine tsum_congr fun y => ?_
  rw [greenTime, LatticeProb.greenTime, Finset.sum_mul]

/-! ### The mean over the last steps -/

/-- Summing `eq:dgt4-one-step-mean-increment` over the last `j` steps. -/
theorem meanOdometerOf_backward (hd1 : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (n : ℕ) : ∀ j : ℕ,
    (∫ ζ, odometerOf ζ (n + j) 0 ∂(LatticeProb.iidLaw d ν))
        - ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)
      ≤ (j : ℝ) * ∫ ζ, max 0 (-(ζ 0)) ∂(LatticeProb.iidLaw d ν) := by
  intro j
  induction j with
  | zero => simp
  | succ k ih =>
      have h := meanOdometerOf_succ_sub_le hd1 ν hint hmean hpos (n + k)
      have hidx : n + (k + 1) = (n + k) + 1 := by omega
      rw [hidx]
      push_cast
      linarith

/-! ### The exponent of the smoothed tail at the scale `m ≈ ε h` -/

/-- With `m ≥ ε h`, both arguments of the minimum in
`lem:dgt4-smoothed-odometer-tail` at level `s = 7h/16` are at least
`(49/256) ε^{(d-2)/2} h^{d/2}`, hence at least the same multiple of `h^β`. -/
theorem smoothed_exponent_lower {d : ℕ} (hd : 5 ≤ d) {ε h M β : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hh : 1 ≤ h) (hM : ε * h ≤ M) (hβd : β ≤ (d : ℝ) / 2) :
    (49 / 256) * ε ^ (((d : ℝ) - 2) / 2) * h ^ β
      ≤ min ((7 / 16 * h) ^ 2 * M ^ (((d : ℝ) - 4) / 2))
          ((7 / 16 * h) * M ^ (((d : ℝ) - 2) / 2)) := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hh0 : (0 : ℝ) < h := lt_of_lt_of_le one_pos hh
  have hεh : (0 : ℝ) < ε * h := by positivity
  have hp4 : (0 : ℝ) < ((d : ℝ) - 4) / 2 := by linarith
  have hp2 : (0 : ℝ) < ((d : ℝ) - 2) / 2 := by linarith
  have hhd : h ^ β ≤ h ^ ((d : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hh hβd
  have hβnn : (0 : ℝ) ≤ h ^ β := Real.rpow_nonneg hh0.le _
  have hsplit4 : (ε * h) ^ (((d : ℝ) - 4) / 2)
      = ε ^ (((d : ℝ) - 4) / 2) * h ^ (((d : ℝ) - 4) / 2) := Real.mul_rpow hε.le hh0.le
  have hsplit2 : (ε * h) ^ (((d : ℝ) - 2) / 2)
      = ε ^ (((d : ℝ) - 2) / 2) * h ^ (((d : ℝ) - 2) / 2) := Real.mul_rpow hε.le hh0.le
  have hpow4 : h ^ (2 : ℕ) * h ^ (((d : ℝ) - 4) / 2) = h ^ ((d : ℝ) / 2) := by
    have hcast : (h ^ (2 : ℕ)) = h ^ ((2 : ℝ)) := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hcast, ← Real.rpow_add hh0]
    congr 1
    ring
  have hpow2 : h * h ^ (((d : ℝ) - 2) / 2) = h ^ ((d : ℝ) / 2) := by
    have hadd : h ^ ((1 : ℝ) + ((d : ℝ) - 2) / 2)
        = h ^ (1 : ℝ) * h ^ (((d : ℝ) - 2) / 2) := Real.rpow_add hh0 _ _
    rw [Real.rpow_one] at hadd
    rw [← hadd]
    congr 1
    ring
  have hεmono : ε ^ (((d : ℝ) - 2) / 2) ≤ ε ^ (((d : ℝ) - 4) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have hε2nn : (0 : ℝ) ≤ ε ^ (((d : ℝ) - 2) / 2) := Real.rpow_nonneg hε.le _
  have hε4nn : (0 : ℝ) ≤ ε ^ (((d : ℝ) - 4) / 2) := Real.rpow_nonneg hε.le _
  refine le_min ?_ ?_
  · have hMm : (ε * h) ^ (((d : ℝ) - 4) / 2) ≤ M ^ (((d : ℝ) - 4) / 2) :=
      Real.rpow_le_rpow hεh.le hM hp4.le
    have hstart : (49 / 256) * ε ^ (((d : ℝ) - 2) / 2) * h ^ β
        ≤ (49 / 256) * ε ^ (((d : ℝ) - 4) / 2) * h ^ ((d : ℝ) / 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hεmono (by norm_num)) hhd hβnn (by positivity)
    refine le_trans hstart ?_
    calc (49 / 256) * ε ^ (((d : ℝ) - 4) / 2) * h ^ ((d : ℝ) / 2)
        = (49 / 256) * h ^ (2 : ℕ) * (ε * h) ^ (((d : ℝ) - 4) / 2) := by
          rw [← hpow4, hsplit4]; ring
      _ ≤ (49 / 256) * h ^ (2 : ℕ) * M ^ (((d : ℝ) - 4) / 2) :=
          mul_le_mul_of_nonneg_left hMm (by positivity)
      _ = (7 / 16 * h) ^ 2 * M ^ (((d : ℝ) - 4) / 2) := by ring
  · have hMm : (ε * h) ^ (((d : ℝ) - 2) / 2) ≤ M ^ (((d : ℝ) - 2) / 2) :=
      Real.rpow_le_rpow hεh.le hM hp2.le
    have hstart : (49 / 256) * ε ^ (((d : ℝ) - 2) / 2) * h ^ β
        ≤ (7 / 16) * ε ^ (((d : ℝ) - 2) / 2) * h ^ ((d : ℝ) / 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (by norm_num) hε2nn) hhd hβnn (by positivity)
    refine le_trans hstart ?_
    calc (7 / 16) * ε ^ (((d : ℝ) - 2) / 2) * h ^ ((d : ℝ) / 2)
        = (7 / 16) * h * (ε * h) ^ (((d : ℝ) - 2) / 2) := by rw [← hpow2, hsplit2]; ring
      _ ≤ (7 / 16) * h * M ^ (((d : ℝ) - 2) / 2) :=
          mul_le_mul_of_nonneg_left hMm (by positivity)
      _ = (7 / 16 * h) * M ^ (((d : ℝ) - 2) / 2) := by ring

/-! ### The refined lower tail -/

/-- **The refined lower tail of `ζ(0) + P u_t(0)`.**  For `h = u + E u_t(0)`
between a fixed threshold and `t/ε`, the tail is at most `C e^{-c h^β}` with
`β = min(γ, d/2)`. -/
theorem exists_refined_tail (_hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (γ : ℝ) (hγ : 1 ≤ γ) (hγd : γ ≠ (d : ℝ) / 2)
    (c₁ C₁ s₀ : ℝ) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hs₀ : 0 < s₀)
    (htailν : ∀ s : ℝ, s₀ ≤ s →
      ν (Set.Iic (-s)) ≤ ENNReal.ofReal (C₁ * Real.exp (-(c₁ * s ^ γ)))) :
    ∃ c C ε h₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧ 0 < h₀ ∧ ∀ (t : ℕ) (u : ℝ), 0 ≤ u →
      h₀ ≤ u + (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)) →
      ε * (u + (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν))) ≤ (t : ℝ) →
      (LatticeProb.iidLaw d ν).real
          {ζ : Site d → ℝ | u ≤ -(ζ 0) - avg (odometerOf ζ t) 0} ≤
        C * Real.exp (-(c * (u + (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)))
          ^ min γ ((d : ℝ) / 2))) := by
  classical
  haveI := hprob
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hint : Integrable id ν := integrable_id_of_exp_moment ν θ₀ hθ₀ hexpint
  have hposν : Integrable (fun z : ℝ => max z 0) ν :=
    Integrable.mono' hint.abs (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  set P : Measure (Site d → ℝ) := LatticeProb.iidLaw d ν with hP
  set β : ℝ := min γ ((d : ℝ) / 2) with hβdef
  have hβ1 : (1 : ℝ) ≤ β := le_min hγ (by linarith)
  have hβd : β ≤ (d : ℝ) / 2 := min_le_right _ _
  set D : ℝ := ∫ ζ, max 0 (-(ζ 0)) ∂P with hD
  have hD0 : 0 ≤ D := integral_nonneg fun ζ => le_max_left _ _
  set ε : ℝ := min 1 (1 / (8 * (D + 1))) with hεdef
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεD : ε * D ≤ 1 / 8 := by
    have h1 : ε ≤ 1 / (8 * (D + 1)) := min_le_right _ _
    have h2 : (0 : ℝ) < 8 * (D + 1) := by positivity
    have h3 : ε * D ≤ (1 / (8 * (D + 1))) * D := mul_le_mul_of_nonneg_right h1 hD0
    have hD1 : D ≤ D + 1 := by linarith
    have h4 : (1 / (8 * (D + 1))) * D ≤ 1 / 8 := by
      calc (1 / (8 * (D + 1))) * D ≤ (1 / (8 * (D + 1))) * (D + 1) :=
            mul_le_mul_of_nonneg_left hD1 (by positivity)
        _ = 1 / 8 := by field_simp
    linarith
  obtain ⟨cG, CG, hcG, hCG, hsummable, hGtail⟩ :=
    Sandpile.Frozen.dgt4_green_scenery_tail d hd ν hprob hmean hvar hvar' θ₀ K₀ hθ₀
      hexpint hexp γ hγ hγd c₁ C₁ s₀ hc₁ hC₁ hs₀ htailν
  obtain ⟨cS, CS, hcS, hCS, hStail⟩ :=
    Sandpile.Frozen.dgt4_smoothed_odometer_tail d hd ν hprob hmean hvar hvar' θ₀ K₀ hθ₀
      hexpint hexp
  set κ : ℝ := 49 / 256 * ε ^ (((d : ℝ) - 2) / 2) with hκdef
  have hκ0 : 0 < κ := by rw [hκdef]; positivity
  have h716 : (0 : ℝ) < (7 / 16 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨min (cG * (7 / 16) ^ β) (cS * κ), CG + CS, ε, max (1 / ε) (16 / 7),
    lt_min (by positivity) (by positivity), by positivity, hε,
    lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro t u hu hh0 hht
  set mean : ℝ := ∫ ζ, odometerOf ζ t 0 ∂P with hmeandef
  set h : ℝ := u + mean with hhdef
  have hh167 : (16 : ℝ) / 7 ≤ h := le_trans (le_max_right _ _) hh0
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hhpos : (0 : ℝ) < h := by linarith
  have hεinv : 1 / ε ≤ h := le_trans (le_max_left _ _) hh0
  have hεh1 : (1 : ℝ) ≤ ε * h := by
    rw [div_le_iff₀ hε] at hεinv
    linarith
  set mh : ℕ := ⌊ε * h⌋₊ with hmhdef
  have hmh1 : 1 ≤ mh := Nat.le_floor (by exact_mod_cast hεh1)
  have hmht : mh ≤ t := by
    have h1 := Nat.floor_le_of_le hht
    simpa using h1
  have hmhle : (mh : ℝ) ≤ ε * h := Nat.floor_le (by positivity)
  have hmhge : ε * h ≤ (mh : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  set n : ℕ := t - mh with hndef
  have htn : n + mh = t := by omega
  set meann : ℝ := ∫ ζ, odometerOf ζ n 0 ∂P with hmeanndef
  have hback : mean - meann ≤ h / 8 := by
    have hb := meanOdometerOf_backward hd1 ν hint hmean hposν n mh
    rw [htn] at hb
    calc mean - meann ≤ (mh : ℝ) * D := hb
      _ ≤ (ε * h) * D := mul_le_mul_of_nonneg_right hmhle hD0
      _ = h * (ε * D) := by ring
      _ ≤ h * (1 / 8) := mul_le_mul_of_nonneg_left hεD hhpos.le
      _ = h / 8 := by ring
  set s : ℝ := 7 / 16 * h with hsdef
  have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; linarith
  set A₁ : Set (Site d → ℝ) :=
    {ζ : Site d → ℝ | ∑' y : Site d, greenTime d (mh + 1) 0 y * ζ y ≤ -s} with hA₁
  set A₂ : Set (Site d → ℝ) :=
    {ζ : Site d → ℝ | (avg^[mh + 1] fun x => odometerOf ζ n x - meann) 0 ≤ -s} with hA₂
  have hsub : {ζ : Site d → ℝ | u ≤ -(ζ 0) - avg (odometerOf ζ t) 0} ⊆ A₁ ∪ A₂ := by
    intro ζ hζ
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [hA₁, Set.mem_setOf_eq, not_le] at h1
    rw [hA₂, Set.mem_setOf_eq, not_le] at h2
    have hiter := odometerOf_iterate_lower ζ mh n
    rw [htn, sum_avg_iterate_eq_tsum_greenTime (mh + 1) ζ] at hiter
    have hsc : (avg^[mh + 1] (odometerOf ζ n)) 0
        = (avg^[mh + 1] fun x => odometerOf ζ n x - meann) 0 + meann := by
      rw [avg_iterate_sub_const hd1 (mh + 1) (odometerOf ζ n) meann 0]; ring
    rw [hsc] at hiter
    have hζle : ζ 0 + avg (odometerOf ζ t) 0 ≤ -u := by
      have hz : u ≤ -(ζ 0) - avg (odometerOf ζ t) 0 := hζ
      linarith
    linarith [hiter, hζle, hback, h1, h2]
  have hb₁ : P.real A₁ ≤ CG * Real.exp (-(cG * s ^ β)) := by
    have hmm := hGtail (mh + 1) (by omega) s hs1
    have hnn : (0 : ℝ) ≤ CG * Real.exp (-(cG * s ^ β)) := by positivity
    rw [hA₁, Measure.real, ← ENNReal.toReal_ofReal hnn]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hmm
  have hb₂ : P.real A₂ ≤ CS * Real.exp (-(cS * min
      (s ^ 2 * (((mh + 1 : ℕ)) : ℝ) ^ (((d : ℝ) - 4) / 2))
      (s * (((mh + 1 : ℕ)) : ℝ) ^ (((d : ℝ) - 2) / 2)))) := by
    have hmm := hStail (mh + 1) (by omega) n s hs1
    have hnn : (0 : ℝ) ≤ CS * Real.exp (-(cS * min
        (s ^ 2 * (((mh + 1 : ℕ)) : ℝ) ^ (((d : ℝ) - 4) / 2))
        (s * (((mh + 1 : ℕ)) : ℝ) ^ (((d : ℝ) - 2) / 2)))) := by positivity
    rw [hA₂, Measure.real, ← ENNReal.toReal_ofReal hnn]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hmm
  -- both tails are at most the common bound
  have hβnn : (0 : ℝ) ≤ h ^ β := Real.rpow_nonneg hhpos.le _
  have hsβ : s ^ β = (7 / 16 : ℝ) ^ β * h ^ β := by
    rw [hsdef]; exact Real.mul_rpow (by norm_num) hhpos.le
  have hexpG : Real.exp (-(cG * s ^ β))
      ≤ Real.exp (-(min (cG * (7 / 16) ^ β) (cS * κ) * h ^ β)) := by
    refine Real.exp_le_exp.mpr ?_
    have hle : min (cG * (7 / 16) ^ β) (cS * κ) * h ^ β ≤ cG * (7 / 16) ^ β * h ^ β :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hβnn
    rw [hsβ]
    have h3 : cG * ((7 / 16 : ℝ) ^ β * h ^ β) = cG * (7 / 16) ^ β * h ^ β := by ring
    linarith [hle, h3.le, h3.ge]
  have hMge : ε * h ≤ (((mh + 1 : ℕ)) : ℝ) := by push_cast; linarith
  have hexpS : Real.exp (-(cS * min (s ^ 2 * (((mh + 1 : ℕ)) : ℝ) ^ (((d : ℝ) - 4) / 2))
        (s * (((mh + 1 : ℕ)) : ℝ) ^ (((d : ℝ) - 2) / 2))))
      ≤ Real.exp (-(min (cG * (7 / 16) ^ β) (cS * κ) * h ^ β)) := by
    refine Real.exp_le_exp.mpr ?_
    have hlow := smoothed_exponent_lower (d := d) hd (ε := ε) (h := h)
      (M := (((mh + 1 : ℕ)) : ℝ)) (β := β) hε hε1 hh1 hMge hβd
    rw [← hsdef] at hlow
    have h1 : min (cG * (7 / 16) ^ β) (cS * κ) * h ^ β ≤ cS * κ * h ^ β :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hβnn
    have h2 : cS * (κ * h ^ β)
        ≤ cS * min (s ^ 2 * (((mh + 1 : ℕ)) : ℝ) ^ (((d : ℝ) - 4) / 2))
            (s * (((mh + 1 : ℕ)) : ℝ) ^ (((d : ℝ) - 2) / 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hcS.le
      rw [hκdef]
      linarith [hlow]
    have h3 : cS * κ * h ^ β = cS * (κ * h ^ β) := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hunion : P.real {ζ : Site d → ℝ | u ≤ -(ζ 0) - avg (odometerOf ζ t) 0}
      ≤ P.real A₁ + P.real A₂ :=
    le_trans (measureReal_mono hsub) (measureReal_union_le _ _)
  calc P.real {ζ : Site d → ℝ | u ≤ -(ζ 0) - avg (odometerOf ζ t) 0}
      ≤ P.real A₁ + P.real A₂ := hunion
    _ ≤ (CG + CS) * Real.exp (-(min (cG * (7 / 16) ^ β) (cS * κ) * h ^ β)) := by
        have g1 := mul_le_mul_of_nonneg_left hexpG hCG.le
        have g2 := mul_le_mul_of_nonneg_left hexpS hCS.le
        have h3 : (CG + CS) * Real.exp (-(min (cG * (7 / 16) ^ β) (cS * κ) * h ^ β))
            = CG * Real.exp (-(min (cG * (7 / 16) ^ β) (cS * κ) * h ^ β))
              + CS * Real.exp (-(min (cG * (7 / 16) ^ β) (cS * κ) * h ^ β)) := by ring
        linarith [hb₁, hb₂, g1, g2, h3.le, h3.ge]

/-! ### A power of the logarithm is eventually linear -/

/-- For every `β > 0`, `K (log(t+2))^β ≤ L t` past an index. -/
theorem exists_log_rpow_le_linear {K L β : ℝ} (hK : 0 < K) (hL : 0 < L) (hβ : 0 < β) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → K * (Real.log ((t : ℝ) + 2)) ^ β ≤ L * (t : ℝ) := by
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  set A : ℝ := K * (2 * β) ^ β with hAdef
  have hA : 0 < A := by rw [hAdef]; positivity
  obtain ⟨T, hT⟩ : ∃ T : ℕ, ((4 : ℝ) ⊔ (2 * A / L) ^ 2) ≤ (T : ℝ) :=
    ⟨⌈(4 : ℝ) ⊔ (2 * A / L) ^ 2⌉₊, Nat.le_ceil _⟩
  refine ⟨T, fun t ht => ?_⟩
  have htT : ((4 : ℝ) ⊔ (2 * A / L) ^ 2) ≤ (t : ℝ) := le_trans hT (by exact_mod_cast ht)
  have ht4 : (4 : ℝ) ≤ (t : ℝ) := le_trans (le_max_left _ _) htT
  have htA : ((2 * A / L) ^ 2 : ℝ) ≤ (t : ℝ) := le_trans (le_max_right _ _) htT
  set x : ℝ := (t : ℝ) + 2 with hxdef
  have hx1 : (1 : ℝ) ≤ x := by rw [hxdef]; linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hstep1 : Real.log x ≤ 2 * β * x ^ (1 / (2 * β)) := by
    have h := log_le_rpow_div (2 / β) (by positivity) x hx1
    have he1 : (4 : ℝ) / (2 / β) = 2 * β := by rw [div_div_eq_mul_div]; ring
    have he2 : ((2 : ℝ) / β) / 4 = 1 / (2 * β) := by
      rw [div_div]
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    rwa [he1, he2] at h
  have hlognn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hstep2 : (Real.log x) ^ β ≤ (2 * β) ^ β * x ^ ((1 : ℝ) / 2) := by
    refine le_trans (Real.rpow_le_rpow hlognn hstep1 hβ.le) ?_
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le]
    have hmul : 1 / (2 * β) * β = 1 / 2 := by field_simp
    rw [hmul]
  have hsqrt : x ^ ((1 : ℝ) / 2) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  have hts : (0 : ℝ) < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hst : Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ) = (t : ℝ) := Real.mul_self_sqrt (by linarith)
  have hsq2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hfinal : Real.sqrt x ≤ 2 * Real.sqrt (t : ℝ) := by
    have hx2t : x ≤ 2 * (t : ℝ) := by rw [hxdef]; linarith
    refine le_trans (Real.sqrt_le_sqrt hx2t) ?_
    rw [Real.sqrt_mul (by norm_num) ((t : ℝ))]
    exact mul_le_mul_of_nonneg_right hsq2 (Real.sqrt_nonneg _)
  have h2AL : (2 * A / L) ≤ Real.sqrt (t : ℝ) := by
    have h := Real.sqrt_le_sqrt htA
    rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * A / L)] at h
  have hLs : 2 * A ≤ Real.sqrt (t : ℝ) * L := (div_le_iff₀ hL).mp h2AL
  calc K * (Real.log x) ^ β ≤ K * ((2 * β) ^ β * x ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hstep2 hK.le
    _ = A * Real.sqrt x := by rw [hAdef, hsqrt]; ring
    _ ≤ A * (2 * Real.sqrt (t : ℝ)) := mul_le_mul_of_nonneg_left hfinal hA.le
    _ ≤ L * (t : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_right hLs (Real.sqrt_nonneg (t : ℝ)), hst]

/-! ### The stretched-exponential integral -/

/-- The stretched-exponential density `x ↦ exp(-b x^p)` is integrable on `(0, ∞)` for `p ≥ 1`
and `b > 0`, obtained from `integrableOn_rpow_mul_exp_neg_mul_rpow` with exponent `s = 0` and
simplifying the resulting factor `x^0`. -/
theorem integrableOn_exp_neg_mul_rpow' {b p : ℝ} (hp : 1 ≤ p) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => Real.exp (-b * x ^ p)) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := p) (b := b)
    (by norm_num) hp hb
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_zero, one_mul]

/-- `∫_0^∞ e^{-c(u+m)^β} du ≤ e^{-c m^β} ∫_0^∞ e^{-c u^β} du` for `β ≥ 1`. -/
theorem integral_exp_neg_shift_le {c β m : ℝ} (hc : 0 < c) (hβ : 1 ≤ β) (hm : 0 ≤ m) :
    ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(c * (u + m) ^ β))
      ≤ Real.exp (-(c * m ^ β)) * (c ^ (-1 / β) * Real.Gamma (1 / β + 1)) := by
  have hβ0 : (0 : ℝ) < β := lt_of_lt_of_le one_pos hβ
  have hdom : IntegrableOn
      (fun u : ℝ => Real.exp (-(c * m ^ β)) * Real.exp (-c * u ^ β)) (Set.Ioi 0) :=
    (integrableOn_exp_neg_mul_rpow' hβ hc).const_mul _
  have hle : ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(c * (u + m) ^ β))
      ≤ ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(c * m ^ β)) * Real.exp (-c * u ^ β) := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le) hdom ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have hsuper : u ^ β + m ^ β ≤ (u + m) ^ β := Real.add_rpow_le_rpow_add hu0 hm hβ
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hsuper, hc]
  refine le_trans hle ?_
  rw [integral_const_mul, integral_exp_neg_mul_rpow hβ0 hc]

/-! ### The refined increment bound -/

set_option maxHeartbeats 1000000 in
/-- **The refined increment bound** `eq:dgt4-reduction-increment`:
`E u_{t+1}(0) - E u_t(0) ≤ C e^{-c (E u_t(0))^β}` with `β = min(γ, d/2)`. -/
theorem exists_refined_increment (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (γ : ℝ) (hγ : 1 ≤ γ) (hγd : γ ≠ (d : ℝ) / 2)
    (c₁ C₁ s₀ : ℝ) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hs₀ : 0 < s₀)
    (htailν : ∀ s : ℝ, s₀ ≤ s →
      ν (Set.Iic (-s)) ≤ ENNReal.ofReal (C₁ * Real.exp (-(c₁ * s ^ γ)))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℕ,
      (∫ ζ, odometerOf ζ (t + 1) 0 ∂(LatticeProb.iidLaw d ν))
          - ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)
        ≤ C * Real.exp (-(c * (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν))
            ^ min γ ((d : ℝ) / 2))) := by
  classical
  haveI := hprob
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hint : Integrable id ν := integrable_id_of_exp_moment ν θ₀ hθ₀ hexpint
  have hposν : Integrable (fun z : ℝ => max z 0) ν :=
    Integrable.mono' hint.abs (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  set P : Measure (Site d → ℝ) := LatticeProb.iidLaw d ν with hP
  set β : ℝ := min γ ((d : ℝ) / 2) with hβdef
  have hβ1 : (1 : ℝ) ≤ β := le_min hγ (by linarith)
  have hβ0 : (0 : ℝ) < β := lt_of_lt_of_le one_pos hβ1
  obtain ⟨cR, CR, ε, h₀, hcR, hCR, hε, hh₀, hRtail⟩ :=
    exists_refined_tail hGH hd ν hprob hmean hvar hvar' θ₀ K₀ hθ₀ hexpint hexp γ hγ hγd
      c₁ C₁ s₀ hc₁ hC₁ hs₀ htailν
  obtain ⟨cc, Cc, hcc, hCc, hctail⟩ :=
    exists_reflected_tail hGH hd ν hprob hmean hvar hvar' θ₀ K₀ hθ₀ hexpint hexp
  obtain ⟨C₀, hC₀, hlog⟩ :=
    exists_crude_log_upper hGH hd ν hprob hmean hvar hvar' θ₀ K₀ hθ₀ hexpint hexp
  set Λ : ℝ := cR ^ (-1 / β) * Real.Gamma (1 / β + 1) with hΛdef
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛdef]
    have h1 : (0 : ℝ) < cR ^ (-1 / β) := Real.rpow_pos_of_pos hcR _
    have h2 : (0 : ℝ) < Real.Gamma (1 / β + 1) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  obtain ⟨T₁, hT₁⟩ := exists_log_rpow_le_linear (K := cR * C₀ ^ β) (L := cc / (4 * ε))
    (β := β) (by positivity) (by positivity) hβ0
  set D : ℝ := ∫ ζ, max 0 (-(ζ 0)) ∂P with hDdef
  have hD0 : 0 ≤ D := integral_nonneg fun ζ => le_max_left _ _
  set R₀ : ℝ := max (max h₀ 2) (C₀ * Real.log ((T₁ : ℝ) + 2)) with hR₀def
  have hR₀0 : (0 : ℝ) ≤ R₀ :=
    le_trans (le_trans hh₀.le (le_max_left h₀ 2)) (le_max_left _ _)
  refine ⟨cR, max 1 (max (CR * Λ + 4 * Cc / cc) (D * Real.exp (cR * R₀ ^ β))), hcR,
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro t
  set mean : ℝ := ∫ ζ, odometerOf ζ t 0 ∂P with hmeandef
  have hmeannn : (0 : ℝ) ≤ mean := integral_nonneg fun ζ => odometerOf_nonneg ζ t 0
  by_cases hcase : 2 ≤ mean ∧ h₀ ≤ mean ∧ T₁ ≤ t
  · obtain ⟨hm2, hmh₀, htT₁⟩ := hcase
    set f : (Site d → ℝ) → ℝ := fun ζ => max 0 (-(ζ 0) - avg (odometerOf ζ t) 0) with hf
    have hfint : Integrable f P := integrable_reflected ν hint hposν t
    have hfnn : 0 ≤ᵐ[P] f := Filter.Eventually.of_forall fun ζ => le_max_left _ _
    have hlayer : ∫ ζ, f ζ ∂P = ∫ u in Set.Ioi (0 : ℝ), P.real {ζ | u ≤ f ζ} :=
      hfint.integral_eq_integral_meas_le hfnn
    set B : ℝ := Cc * Real.exp (-(cc / 4) * ((t : ℝ) / ε)) with hBdef
    have hB0 : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
    set g : ℝ → ℝ := fun u =>
      CR * (Real.exp (-(cR * mean ^ β)) * Real.exp (-cR * u ^ β))
        + B * Real.exp (-(cc / 4) * u) with hgdef
    have hg1 : IntegrableOn
        (fun u : ℝ => CR * (Real.exp (-(cR * mean ^ β)) * Real.exp (-cR * u ^ β)))
        (Set.Ioi (0 : ℝ)) :=
      ((integrableOn_exp_neg_mul_rpow' hβ1 hcR).const_mul _).const_mul _
    have hg2 : IntegrableOn (fun u : ℝ => B * Real.exp (-(cc / 4) * u)) (Set.Ioi (0 : ℝ)) :=
      (exp_neg_integrableOn_Ioi 0 (by positivity)).const_mul B
    have hgint : IntegrableOn g (Set.Ioi (0 : ℝ)) := hg1.add hg2
    -- the pointwise domination
    have hdom : ∀ u : ℝ, 0 < u → P.real {ζ | u ≤ f ζ} ≤ g u := by
      intro u hu
      have hset : {ζ : Site d → ℝ | u ≤ f ζ}
          = {ζ : Site d → ℝ | u ≤ -(ζ 0) - avg (odometerOf ζ t) 0} := by
        ext ζ
        simp only [Set.mem_setOf_eq, hf, le_max_iff]
        constructor
        · rintro (hc | hc)
          · linarith
          · exact hc
        · intro hc; exact Or.inr hc
      rw [hset]
      have hone : (0 : ℝ) ≤ B * Real.exp (-(cc / 4) * u) := by positivity
      have htwo : (0 : ℝ)
          ≤ CR * (Real.exp (-(cR * mean ^ β)) * Real.exp (-cR * u ^ β)) := by positivity
      rcases le_or_gt (ε * (u + mean)) ((t : ℝ)) with hle | hgt
      · have hR := hRtail t u hu.le (by rw [← hmeandef]; linarith) (by rw [← hmeandef]; exact hle)
        rw [← hmeandef] at hR
        refine le_trans hR ?_
        have hsuper : u ^ β + mean ^ β ≤ (u + mean) ^ β :=
          Real.add_rpow_le_rpow_add hu.le hmeannn hβ1
        have h1 : Real.exp (-(cR * (u + mean) ^ β))
            ≤ Real.exp (-(cR * mean ^ β)) * Real.exp (-cR * u ^ β) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          nlinarith [hsuper, hcR]
        have h2 := mul_le_mul_of_nonneg_left h1 hCR.le
        rw [hgdef]
        linarith
      · have hc := hctail t u hu.le (by rw [← hmeandef]; exact hm2)
        rw [← hmeandef] at hc
        refine le_trans hc ?_
        have h1 : (t : ℝ) / ε < u + mean := by
          rw [div_lt_iff₀ hε]; linarith
        have hkey : Real.exp (-(cc * ((u + mean) / 2)))
            ≤ Real.exp (-(cc / 4) * ((t : ℝ) / ε)) * Real.exp (-(cc / 4) * u) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          nlinarith [h1, hu.le, hmeannn, hcc]
        have h2 := mul_le_mul_of_nonneg_left hkey hCc.le
        rw [hgdef, hBdef]
        nlinarith [h2, htwo]
    have hdomin : ∫ u in Set.Ioi (0 : ℝ), P.real {ζ | u ≤ f ζ} ≤ ∫ u in Set.Ioi (0 : ℝ), g u := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun u => ENNReal.toReal_nonneg) hgint ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hdom u hu
    have hgval : ∫ u in Set.Ioi (0 : ℝ), g u
        = CR * (Real.exp (-(cR * mean ^ β)) * Λ) + B * (1 / (cc / 4)) := by
      rw [hgdef, integral_add hg1 hg2, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_exp_neg_mul_rpow hβ0 hcR,
        integral_exp_neg_mul_Ioi_zero (show (0 : ℝ) < cc / 4 by positivity), hΛdef]
    -- the crude tail contribution is smaller than the refined one
    have hmeanβ : cR * mean ^ β ≤ (cc / 4) * ((t : ℝ) / ε) := by
      have hml : mean ≤ C₀ * Real.log ((t : ℝ) + 2) := by rw [hmeandef]; exact hlog t
      have hlognn : (0 : ℝ) ≤ Real.log ((t : ℝ) + 2) :=
        Real.log_nonneg (by have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _; linarith)
      have h1 : mean ^ β ≤ (C₀ * Real.log ((t : ℝ) + 2)) ^ β :=
        Real.rpow_le_rpow hmeannn hml hβ0.le
      have h2 : (C₀ * Real.log ((t : ℝ) + 2)) ^ β
          = C₀ ^ β * (Real.log ((t : ℝ) + 2)) ^ β := Real.mul_rpow hC₀.le hlognn
      have h3 := hT₁ t htT₁
      have h4 : (cc / (4 * ε)) * (t : ℝ) = (cc / 4) * ((t : ℝ) / ε) := by
        field_simp
      rw [h2] at h1
      have h5 : cR * mean ^ β ≤ cR * C₀ ^ β * (Real.log ((t : ℝ) + 2)) ^ β := by
        have h6 := mul_le_mul_of_nonneg_left h1 hcR.le
        have h7 : cR * (C₀ ^ β * (Real.log ((t : ℝ) + 2)) ^ β)
            = cR * C₀ ^ β * (Real.log ((t : ℝ) + 2)) ^ β := by ring
        linarith [h6, h7.le, h7.ge]
      linarith [h3, h4.le, h4.ge, h5]
    have hcrudeexp : Real.exp (-(cc / 4) * ((t : ℝ) / ε)) ≤ Real.exp (-(cR * mean ^ β)) := by
      refine Real.exp_le_exp.mpr ?_
      linarith [hmeanβ]
    -- put it together
    have hincr : (∫ ζ, odometerOf ζ (t + 1) 0 ∂P) - mean = ∫ ζ, f ζ ∂P := by
      rw [hmeandef, hf]
      exact meanOdometerOf_succ_sub hd1 ν hint hmean hposν t
    rw [hincr, hlayer]
    refine le_trans hdomin ?_
    rw [hgval]
    have hfin1 : B * (1 / (cc / 4)) ≤ (4 * Cc / cc) * Real.exp (-(cR * mean ^ β)) := by
      rw [hBdef]
      have h1 := mul_le_mul_of_nonneg_left hcrudeexp hCc.le
      have h2 : Cc * Real.exp (-(cc / 4) * ((t : ℝ) / ε)) * (1 / (cc / 4))
          = (4 * Cc / cc) * Real.exp (-(cc / 4) * ((t : ℝ) / ε)) := by
        field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left hcrudeexp (by positivity)
    have hfin2 : CR * (Real.exp (-(cR * mean ^ β)) * Λ)
        = (CR * Λ) * Real.exp (-(cR * mean ^ β)) := by ring
    rw [hfin2]
    have hsum : (CR * Λ) * Real.exp (-(cR * mean ^ β))
        + (4 * Cc / cc) * Real.exp (-(cR * mean ^ β))
        = (CR * Λ + 4 * Cc / cc) * Real.exp (-(cR * mean ^ β)) := by ring
    have hle2 : (CR * Λ + 4 * Cc / cc)
        ≤ max 1 (max (CR * Λ + 4 * Cc / cc) (D * Real.exp (cR * R₀ ^ β))) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hfinal := mul_le_mul_of_nonneg_right hle2 (Real.exp_pos (-(cR * mean ^ β))).le
    linarith [hfin1, hsum.le, hsum.ge, hfinal]
  · -- the mean is bounded: the uniform one-step bound suffices
    have hbound : mean ≤ R₀ := by
      rcases not_and_or.mp hcase with h | h
      · exact le_trans (le_of_lt (not_le.mp h))
          (le_trans (le_max_right h₀ 2) (le_max_left _ _))
      rcases not_and_or.mp h with h' | h'
      · exact le_trans (le_of_lt (not_le.mp h'))
          (le_trans (le_max_left h₀ 2) (le_max_left _ _))
      · have hlt : t < T₁ := lt_of_not_ge h'
        have hml : mean ≤ C₀ * Real.log ((t : ℝ) + 2) := by rw [hmeandef]; exact hlog t
        refine le_trans hml (le_trans ?_ (le_max_right _ _))
        refine mul_le_mul_of_nonneg_left ?_ hC₀.le
        refine Real.log_le_log (by have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _; linarith) ?_
        have : (t : ℝ) ≤ (T₁ : ℝ) := by exact_mod_cast hlt.le
        linarith
    have hstep : (∫ ζ, odometerOf ζ (t + 1) 0 ∂P) - mean ≤ D := by
      rw [hmeandef, hDdef]
      exact meanOdometerOf_succ_sub_le hd1 ν hint hmean hposν t
    refine le_trans hstep ?_
    have hexp1 : Real.exp (-(cR * R₀ ^ β)) ≤ Real.exp (-(cR * mean ^ β)) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : mean ^ β ≤ R₀ ^ β := Real.rpow_le_rpow hmeannn hbound hβ0.le
      nlinarith [hcR]
    have hDeq : D * Real.exp (cR * R₀ ^ β) * Real.exp (-(cR * R₀ ^ β)) = D := by
      rw [mul_assoc, ← Real.exp_add]; simp
    calc D = D * Real.exp (cR * R₀ ^ β) * Real.exp (-(cR * R₀ ^ β)) := hDeq.symm
      _ ≤ D * Real.exp (cR * R₀ ^ β) * Real.exp (-(cR * mean ^ β)) :=
          mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ ≤ max 1 (max (CR * Λ + 4 * Cc / cc) (D * Real.exp (cR * R₀ ^ β)))
            * Real.exp (-(cR * mean ^ β)) :=
          mul_le_mul_of_nonneg_right
            (le_trans (le_max_right _ _) (le_max_right _ _)) (Real.exp_pos _).le

end Sandpile
