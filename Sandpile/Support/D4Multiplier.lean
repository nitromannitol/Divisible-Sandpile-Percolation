/-
The Fourier multiplier of the membrane field `V_t` and its superdiffusive limit,
Step 1 of `prop:d4-superdiffusive-limit` (`sandpile.tex:3345-3352`).

  `κ_t(λ) = ∑_{j<t} λ^j = (1-λ^t)/(1-λ)`,   `λ(θ) = d^{-1} ∑_i cos θ_i`,

and, for `α > 2` and every `ξ ≠ 0`,

  `R^{-2} κ_{⌊R^α⌋}(λ(ξ/R)) ⟶ 2d/|ξ|²`,

because `R²(1-λ(ξ/R)) → |ξ|²/(2d)` and `λ(ξ/R)^{⌊R^α⌋} → 0`.  In dimension four
the limit is `8/|ξ|²`, the multiplier of `𝒢_4`.  This is where `α > 2` enters
Step 1: the truncated multiplier sees the full Green function only because
`⌊R^α⌋/R² → ∞`.  Uniformly on the Brillouin box `[-πR, πR]^d \ {0}` the
multiplier is bounded by `π²d/|ξ|²`, the domination the paper's dominated
convergence needs.
-/
import Sandpile.Continuum.Kernel
import Mathlib

open Filter Topology

namespace Sandpile

/-- The Fourier symbol `λ(θ) = d^{-1} ∑_i cos θ_i` of the averaging operator `P`. -/
noncomputable def walkSymbol (d : ℕ) (θ : Continuum.Space d) : ℝ :=
  (∑ i : Fin d, Real.cos (θ i)) / d

/-- The Fourier multiplier `κ_t(λ) = ∑_{j<t} λ^j` of the membrane field `V_t`. -/
noncomputable def multiplierKappa (t : ℕ) (lam : ℝ) : ℝ := ∑ j ∈ Finset.range t, lam ^ j

lemma euclid_norm_sq {d : ℕ} (θ : Continuum.Space d) : ‖θ‖ ^ 2 = ∑ i : Fin d, θ i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

lemma one_sub_walkSymbol_eq {d : ℕ} (hd : 0 < d) (θ : Continuum.Space d) :
    1 - walkSymbol d θ = (∑ i : Fin d, (1 - Real.cos (θ i))) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [walkSymbol, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sub_div, div_self (ne_of_gt hd')]

lemma walkSymbol_le_one {d : ℕ} (hd : 0 < d) (θ : Continuum.Space d) :
    walkSymbol d θ ≤ 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [walkSymbol, div_le_one hd']
  calc ∑ i : Fin d, Real.cos (θ i) ≤ ∑ _i : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => Real.cos_le_one _)
    _ = d := by simp

lemma neg_one_le_walkSymbol {d : ℕ} (hd : 0 < d) (θ : Continuum.Space d) :
    -1 ≤ walkSymbol d θ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [walkSymbol, le_div_iff₀ hd']
  calc (-1 : ℝ) * d = ∑ _i : Fin d, (-1 : ℝ) := by simp
    _ ≤ ∑ i : Fin d, Real.cos (θ i) := Finset.sum_le_sum (fun i _ => Real.neg_one_le_cos _)

/-- `1 - λ(θ) ≤ |θ|²/(2d)`, from `1 - x²/2 ≤ cos x`. -/
lemma one_sub_walkSymbol_le {d : ℕ} (hd : 0 < d) (θ : Continuum.Space d) :
    1 - walkSymbol d θ ≤ ‖θ‖ ^ 2 / (2 * d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [one_sub_walkSymbol_eq hd, euclid_norm_sq, div_le_div_iff₀ hd' (by positivity)]
  have h : ∀ i : Fin d, (1 - Real.cos (θ i)) * (2 * d) ≤ θ i ^ 2 * d := by
    intro i
    have := Real.one_sub_sq_div_two_le_cos (x := θ i)
    nlinarith [hd']
  calc (∑ i : Fin d, (1 - Real.cos (θ i))) * (2 * d)
      = ∑ i : Fin d, (1 - Real.cos (θ i)) * (2 * d) := by rw [Finset.sum_mul]
    _ ≤ ∑ i : Fin d, θ i ^ 2 * d := Finset.sum_le_sum (fun i _ => h i)
    _ = (∑ i : Fin d, θ i ^ 2) * d := by rw [Finset.sum_mul]

/-- `2|θ|²/(π²d) ≤ 1 - λ(θ)` on the Brillouin box, from Jordan's inequality. -/
lemma le_one_sub_walkSymbol {d : ℕ} (hd : 0 < d) (θ : Continuum.Space d)
    (hθ : ∀ i, |θ i| ≤ Real.pi) :
    2 / (Real.pi ^ 2 * d) * ‖θ‖ ^ 2 ≤ 1 - walkSymbol d θ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have key : 2 / Real.pi ^ 2 * (∑ i : Fin d, θ i ^ 2) ≤ ∑ i : Fin d, (1 - Real.cos (θ i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hc := Real.cos_le_one_sub_mul_cos_sq (hθ i)
    linarith
  rw [one_sub_walkSymbol_eq hd, euclid_norm_sq,
    show 2 / (Real.pi ^ 2 * (d : ℝ)) * (∑ i : Fin d, θ i ^ 2)
      = (2 / Real.pi ^ 2 * ∑ i : Fin d, θ i ^ 2) / d by field_simp]
  gcongr

/-- `κ_t(λ) = (1-λ^t)/(1-λ)` for `λ ≠ 1`. -/
lemma multiplierKappa_eq (t : ℕ) (lam : ℝ) (hne : lam ≠ 1) :
    multiplierKappa t lam = (1 - lam ^ t) / (1 - lam) := by
  have h1 : lam - 1 ≠ 0 := sub_ne_zero_of_ne hne
  have h2 : (1 : ℝ) - lam ≠ 0 := fun h => h1 (by linarith [sub_eq_zero.mp h])
  rw [multiplierKappa, geom_sum_eq hne t, div_eq_div_iff h1 h2]
  ring

/-- `|R⁻¹ • ξ|² = |ξ|²/R²`. -/
lemma norm_smul_inv_sq {d : ℕ} (R : ℝ) (hR : 0 < R) (ξ : Continuum.Space d) :
    ‖(R⁻¹ : ℝ) • ξ‖ ^ 2 = ‖ξ‖ ^ 2 / R ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, mul_pow, inv_pow]
  field_simp

/-- `|κ_t(λ)| ≤ 2/(1-λ)` for `-1 ≤ λ < 1`. -/
lemma abs_multiplierKappa_le (t : ℕ) (lam : ℝ) (h1 : -1 ≤ lam) (h2 : lam < 1) :
    |multiplierKappa t lam| ≤ 2 / (1 - lam) := by
  have hlt : (0 : ℝ) < 1 - lam := by linarith
  have hne : lam - 1 ≠ 0 := by linarith
  have hgeom : multiplierKappa t lam = (1 - lam ^ t) / (1 - lam) :=
    multiplierKappa_eq t lam (ne_of_lt h2)
  have habs : |lam ^ t| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨h1, h2.le⟩)
  rw [hgeom, abs_div, abs_of_pos hlt]
  gcongr
  calc |1 - lam ^ t| ≤ |(1 : ℝ)| + |lam ^ t| := abs_sub _ _
    _ ≤ 2 := by rw [abs_one]; linarith

lemma smul_apply_space {d : ℕ} (c : ℝ) (ξ : Continuum.Space d) (i : Fin d) :
    (c • ξ) i = c * ξ i := by simp

/-- `R²(1 - cos(u/R)) → u²/2`, by the quartic remainder of the cosine. -/
lemma tendsto_R_sq_one_sub_cos (u : ℝ) :
    Tendsto (fun R : ℝ => R ^ 2 * (1 - Real.cos (u / R))) atTop (𝓝 (u ^ 2 / 2)) := by
  have hg : Tendsto (fun R : ℝ => 5 * u ^ 4 / 96 / R ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  have hsq : Tendsto (fun R : ℝ => R ^ 2 * (1 - Real.cos (u / R)) - u ^ 2 / 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [eventually_ge_atTop (max 1 |u|), eventually_gt_atTop (0 : ℝ)] with R hR hR0
    have hu : |u / R| ≤ 1 := by
      rw [abs_div, abs_of_pos hR0, div_le_one hR0]
      exact (le_max_right 1 |u|).trans hR
    have hb := Real.cos_bound hu
    have he : R ^ 2 * (1 - Real.cos (u / R)) - u ^ 2 / 2
        = R ^ 2 * (Real.cos (u / R) - (1 - (u / R) ^ 2 / 2)) * (-1) := by
      field_simp
      ring
    rw [Real.norm_eq_abs, he, abs_mul, abs_mul, abs_neg, abs_one, mul_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ R ^ 2)]
    calc R ^ 2 * |Real.cos (u / R) - (1 - (u / R) ^ 2 / 2)|
        ≤ R ^ 2 * (|u / R| ^ 4 * (5 / 96)) := by gcongr
      _ = 5 * u ^ 4 / 96 / R ^ 2 := by
          rw [abs_div, abs_of_pos hR0, div_pow, ← abs_pow,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 4)]
          field_simp
  have h := hsq.add_const (u ^ 2 / 2)
  rw [zero_add] at h
  exact h.congr (fun R => by ring)

/-- `R²(1 - λ(ξ/R)) → |ξ|²/(2d)`: the symbol is quadratic at the origin. -/
lemma tendsto_R_sq_one_sub_walkSymbol {d : ℕ} (hd : 0 < d) (ξ : Continuum.Space d) :
    Tendsto (fun R : ℝ => R ^ 2 * (1 - walkSymbol d (R⁻¹ • ξ))) atTop
      (𝓝 (‖ξ‖ ^ 2 / (2 * d))) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hsum : Tendsto
      (fun R : ℝ => (∑ i : Fin d, R ^ 2 * (1 - Real.cos (ξ i / R))) / (d : ℝ)) atTop
      (𝓝 ((∑ i : Fin d, ξ i ^ 2 / 2) / (d : ℝ))) :=
    (tendsto_finsetSum Finset.univ (fun i _ => tendsto_R_sq_one_sub_cos (ξ i))).div_const _
  have hlim : (∑ i : Fin d, ξ i ^ 2 / 2) / (d : ℝ) = ‖ξ‖ ^ 2 / (2 * d) := by
    rw [euclid_norm_sq, ← Finset.sum_div]
    field_simp
  rw [← hlim]
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R _
  rw [one_sub_walkSymbol_eq hd, mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_apply_space, inv_mul_eq_div]

/-- `λ(ξ/R)^{⌊R^α⌋} → 0` for `ξ ≠ 0` and `α > 2`: the time truncation washes out. -/
lemma tendsto_walkSymbol_pow {d : ℕ} (hd : 0 < d) (ξ : Continuum.Space d) (hξ : ξ ≠ 0)
    (α : ℝ) (hα : 2 < α) :
    Tendsto (fun R : ℝ => walkSymbol d (R⁻¹ • ξ) ^ ⌊R ^ α⌋₊) atTop (𝓝 0) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (0 : ℝ) < ‖ξ‖ ^ 2 := by positivity
  set c : ℝ := ‖ξ‖ ^ 2 / (2 * d) with hc
  have hcpos : 0 < c := by positivity
  have hR2 : Tendsto (fun R : ℝ => R ^ 2 * (1 - walkSymbol d (R⁻¹ • ξ))) atTop (𝓝 c) :=
    tendsto_R_sq_one_sub_walkSymbol hd ξ
  have hpow : ∀ R : ℝ, 0 < R → R ^ (α - 2) * R ^ (2 : ℕ) = R ^ α := by
    intro R hR
    rw [← Real.rpow_natCast R 2, ← Real.rpow_add hR]
    congr 1
    push_cast
    ring
  have hdiv : Tendsto (fun R : ℝ => c / 2 * (R ^ α - 1) / R ^ 2) atTop atTop := by
    have hlow : Tendsto (fun R : ℝ => c / 4 * R ^ (α - 2)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) (tendsto_rpow_atTop (by linarith))
    refine tendsto_atTop_mono' _ ?_ hlow
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (tendsto_rpow_atTop (show (0 : ℝ) < α by linarith)).eventually_ge_atTop 2] with R hR0 h2
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < R ^ 2)]
    nlinarith [hpow R hR0, h2, hcpos]
  have hmaj : Tendsto (fun R : ℝ => Real.exp (-(c / 2 * (R ^ α - 1) / R ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hdiv)
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hR2.eventually (eventually_gt_nhds (by linarith : c / 2 < c)),
    eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (c + 1)] with R hR hR1 hRc
  have hR0 : (0 : ℝ) < R := by linarith
  have hRsq : (0 : ℝ) < R ^ 2 := by positivity
  have hle : walkSymbol d (R⁻¹ • ξ) ≤ 1 - c / 2 / R ^ 2 := by
    rw [le_sub_comm, div_le_iff₀ hRsq, mul_comm]
    linarith
  have hnn : 0 ≤ walkSymbol d (R⁻¹ • ξ) := by
    have h := one_sub_walkSymbol_le hd ((R⁻¹ : ℝ) • ξ)
    rw [norm_smul_inv_sq R hR0 ξ,
      show ‖ξ‖ ^ 2 / R ^ 2 / (2 * (d : ℝ)) = c / R ^ 2 by rw [hc]; field_simp] at h
    have hcR : c / R ^ 2 ≤ 1 := by
      rw [div_le_one hRsq]; nlinarith
    linarith
  have hbase : |walkSymbol d (R⁻¹ • ξ)| ≤ Real.exp (-(c / 2 / R ^ 2)) := by
    have h1 : 1 - c / 2 / R ^ 2 ≤ Real.exp (-(c / 2 / R ^ 2)) := by
      have := Real.add_one_le_exp (-(c / 2 / R ^ 2)); linarith
    have h2 : (0 : ℝ) < Real.exp (-(c / 2 / R ^ 2)) := Real.exp_pos _
    exact abs_le.mpr ⟨by linarith, hle.trans h1⟩
  have hfl : R ^ α - 1 ≤ ((⌊R ^ α⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (R ^ α)
    linarith
  have hpos : (0 : ℝ) < c / 2 / R ^ 2 := by positivity
  calc ‖walkSymbol d (R⁻¹ • ξ) ^ ⌊R ^ α⌋₊‖
      = |walkSymbol d (R⁻¹ • ξ)| ^ ⌊R ^ α⌋₊ := by rw [Real.norm_eq_abs, abs_pow]
    _ ≤ Real.exp (-(c / 2 / R ^ 2)) ^ ⌊R ^ α⌋₊ := pow_le_pow_left₀ (abs_nonneg _) hbase _
    _ = Real.exp (-(c / 2 / R ^ 2) * ⌊R ^ α⌋₊) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ Real.exp (-(c / 2 * (R ^ α - 1) / R ^ 2)) := by
        refine Real.exp_le_exp.mpr ?_
        rw [show c / 2 * (R ^ α - 1) / R ^ 2 = c / 2 / R ^ 2 * (R ^ α - 1) by ring,
          neg_mul, neg_le_neg_iff]
        exact mul_le_mul_of_nonneg_left hfl hpos.le

/-- **The uniform multiplier bound on the Brillouin box** (`sandpile.tex:3352`).
For `ξ ≠ 0` in `[-πR, πR]^d`, `R^{-2}|κ_t(λ(ξ/R))| ≤ π²d/|ξ|²`, uniformly in `t`
and `R`.  This is the domination the dominated convergence of Step 1 uses. -/
theorem multiplier_uniform_bound {d : ℕ} (hd : 0 < d) (R : ℝ) (hR : 0 < R) (t : ℕ)
    (ξ : Continuum.Space d) (hξ : ξ ≠ 0) (hbox : ∀ i, |ξ i| ≤ Real.pi * R) :
    |multiplierKappa t (walkSymbol d (R⁻¹ • ξ)) / R ^ 2| ≤ Real.pi ^ 2 * d / ‖ξ‖ ^ 2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (0 : ℝ) < ‖ξ‖ ^ 2 := by positivity
  have hRsq : (0 : ℝ) < R ^ 2 := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hbox' : ∀ i, |((R⁻¹ : ℝ) • ξ) i| ≤ Real.pi := by
    intro i
    rw [smul_apply_space, abs_mul, abs_inv, abs_of_pos hR, inv_mul_eq_div, div_le_iff₀ hR]
    exact hbox i
  have hlb := le_one_sub_walkSymbol hd ((R⁻¹ : ℝ) • ξ) hbox'
  rw [norm_smul_inv_sq R hR ξ] at hlb
  have hgap : 0 < 2 / (Real.pi ^ 2 * d) * (‖ξ‖ ^ 2 / R ^ 2) := by positivity
  have hlt : walkSymbol d (R⁻¹ • ξ) < 1 := by linarith
  have hkap := abs_multiplierKappa_le t (walkSymbol d (R⁻¹ • ξ))
    (neg_one_le_walkSymbol hd _) hlt
  rw [abs_div, abs_of_pos hRsq, div_le_div_iff₀ hRsq hn]
  have hmul : 2 * ‖ξ‖ ^ 2 ≤ Real.pi ^ 2 * d * R ^ 2 * (1 - walkSymbol d (R⁻¹ • ξ)) := by
    have h := mul_le_mul_of_nonneg_left hlb
      (le_of_lt (by positivity : (0 : ℝ) < Real.pi ^ 2 * d * R ^ 2))
    calc 2 * ‖ξ‖ ^ 2
        = Real.pi ^ 2 * d * R ^ 2 * (2 / (Real.pi ^ 2 * d) * (‖ξ‖ ^ 2 / R ^ 2)) := by
          field_simp
      _ ≤ _ := h
  have hstep : |multiplierKappa t (walkSymbol d (R⁻¹ • ξ))| ≤ Real.pi ^ 2 * d * R ^ 2 / ‖ξ‖ ^ 2 := by
    refine hkap.trans ?_
    rw [div_le_div_iff₀ (by linarith) hn]
    linarith
  calc |multiplierKappa t (walkSymbol d (R⁻¹ • ξ))| * ‖ξ‖ ^ 2
      ≤ Real.pi ^ 2 * d * R ^ 2 / ‖ξ‖ ^ 2 * ‖ξ‖ ^ 2 := by gcongr
    _ = Real.pi ^ 2 * d * R ^ 2 := by field_simp

/-- **The superdiffusive multiplier limit** (`sandpile.tex:3345-3350`).
For `α > 2` and `ξ ≠ 0`, `R^{-2}κ_{⌊R^α⌋}(λ(ξ/R)) → 2d/|ξ|²`; in dimension four
this is `8/|ξ|²`, the multiplier of the continuum membrane model `𝒢_4`. -/
theorem tendsto_multiplier {d : ℕ} (hd : 0 < d) (ξ : Continuum.Space d) (hξ : ξ ≠ 0)
    (α : ℝ) (hα : 2 < α) :
    Tendsto (fun R : ℝ => multiplierKappa ⌊R ^ α⌋₊ (walkSymbol d (R⁻¹ • ξ)) / R ^ 2)
      atTop (𝓝 (2 * d / ‖ξ‖ ^ 2)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (0 : ℝ) < ‖ξ‖ ^ 2 := by positivity
  set c : ℝ := ‖ξ‖ ^ 2 / (2 * d) with hc
  have hcpos : 0 < c := by positivity
  have hR2 : Tendsto (fun R : ℝ => R ^ 2 * (1 - walkSymbol d (R⁻¹ • ξ))) atTop (𝓝 c) :=
    tendsto_R_sq_one_sub_walkSymbol hd ξ
  have hnum : Tendsto (fun R : ℝ => 1 - walkSymbol d (R⁻¹ • ξ) ^ ⌊R ^ α⌋₊) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_walkSymbol_pow hd ξ hξ α hα)
  have hquot := hnum.div hR2 (ne_of_gt hcpos)
  rw [show (1 : ℝ) / c = 2 * d / ‖ξ‖ ^ 2 by rw [hc, one_div_div]] at hquot
  refine hquot.congr' ?_
  filter_upwards [hR2.eventually (eventually_gt_nhds (by linarith : c / 2 < c)),
    eventually_gt_atTop (0 : ℝ)] with R hR hR0
  have hRsq : (0 : ℝ) < R ^ 2 := by positivity
  have hlt : walkSymbol d (R⁻¹ • ξ) < 1 := by nlinarith [hcpos]
  simp only [Pi.div_apply]
  rw [multiplierKappa_eq _ _ (ne_of_lt hlt), div_div, mul_comm (1 - walkSymbol d (R⁻¹ • ξ)) (R ^ 2)]

/-- The dimension-four multiplier limit: `R^{-2}κ_{⌊R^α⌋}(λ(ξ/R)) → 8/|ξ|²`. -/
theorem tendsto_multiplier_four (ξ : Continuum.Space 4) (hξ : ξ ≠ 0)
    (α : ℝ) (hα : 2 < α) :
    Tendsto (fun R : ℝ => multiplierKappa ⌊R ^ α⌋₊ (walkSymbol 4 (R⁻¹ • ξ)) / R ^ 2)
      atTop (𝓝 (8 / ‖ξ‖ ^ 2)) := by
  have h := tendsto_multiplier (by norm_num : 0 < 4) ξ hξ α hα
  norm_num at h
  exact h

end Sandpile
