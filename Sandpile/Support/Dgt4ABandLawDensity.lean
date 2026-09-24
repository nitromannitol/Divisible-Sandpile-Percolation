/-
The Step-1 density bound `eq:dgt4-band-density` of `thm:dgt4-many-limits`
(`sandpile.tex:5930-6055`) for the constructed one-site law.

The estimate is read on the band of the NEGATED variable: `eq:dgt4-band-density`
bounds the difference quotients of `t ↦ P(-ζ(0) ≤ t)` on `(ℓ_1 a_k, a_k]`, so the
mass to bound is the one the law puts on `[-(t+ε),-t]`.

There the components below the `k`th band contribute exactly nothing, because
their carriers end at `-a_j ≤ -ℓ_1 a_k < -t`.  Every component at or above the
`k`th band has density at most `2M/((1-ℓ_1)a_k)`, so together they contribute at
most that times their total weight, which is `(1+o(1))ω_k`.  The positive
summand's density there is at most `Ce^{-2a_k} = o(ω_k/a_k)`.
-/
import Sandpile.Support.Dgt4ABandLawParameters

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

variable {w0 mu : ℝ} {v : ℝ≥0} {l1 : ℝ} {a w θ : ℕ → ℝ} {m : ℕ → ℕ}

/-- The Gaussian density is below every exponential. -/
theorem exists_gaussianPDFReal_le_exp (hv : v ≠ 0) (lam : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, gaussianPDFReal mu v x ≤ C * Real.exp (-(lam * x)) := by
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  set c : ℝ := gaussianPDFReal mu v mu with hc
  have hcpos : 0 < c := gaussianPDFReal_pos mu v mu hv
  have key : ∀ x : ℝ,
      gaussianPDFReal mu v x = c * Real.exp (-(x - mu) ^ 2 / (2 * (v : ℝ))) := by
    intro x
    simp only [hc, gaussianPDFReal]
    simp
  refine ⟨c * Real.exp (lam ^ 2 * (v : ℝ) / 2 + lam * mu),
    mul_pos hcpos (Real.exp_pos _), fun x => ?_⟩
  rw [key x, mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hcpos.le
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (v : ℝ))]
  nlinarith [sq_nonneg (x - mu - lam * (v : ℝ))]

/-- The Gaussian density is below every increasing exponential, so it is
exponentially small far out on the negative axis. -/
theorem exists_gaussianPDFReal_le_exp_mul (hv : v ≠ 0) (lam : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, gaussianPDFReal mu v x ≤ C * Real.exp (lam * x) := by
  obtain ⟨C, hC, h⟩ := exists_gaussianPDFReal_le_exp (mu := mu) (v := v) hv (-lam)
  refine ⟨C, hC, fun x => ?_⟩
  have hx := h x
  rwa [show -(-lam * x) = lam * x by ring] at hx

/-- **The mass of the law on a measurable set, as a real number.** -/
theorem bandLaw_toReal (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 < θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hsum : Summable w)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (bandLaw w0 mu v l1 a w θ m S).toReal
      = w0 * (∫ x in S, gaussianPDFReal mu v x)
        + ∑' k, w k * ∫ x in S, bandComponent l1 (a k) (θ k) (m k) x := by
  have hcnn : ∀ k, 0 ≤ ∫ x in S, bandComponent l1 (a k) (θ k) (m k) x := fun k =>
    setIntegral_nonneg hS fun x _ => bandComponent_nonneg (hθ k).le hl1 (ha k) x
  have hcle : ∀ k, ∫ x in S, bandComponent l1 (a k) (θ k) (m k) x ≤ 1 := by
    intro k
    have h := setIntegral_le_integral (μ := (volume : Measure ℝ)) (s := S)
      (integrable_bandComponent (hm k) hl1 (ha k))
      (Filter.Eventually.of_forall fun x => bandComponent_nonneg (hθ k).le hl1 (ha k) x)
    rwa [integral_bandComponent_eq_one (hθ k) (hm k) hl0 hl1 (ha k)] at h
  have hnn : ∀ k, 0 ≤ w k * ∫ x in S, bandComponent l1 (a k) (θ k) (m k) x := fun k =>
    mul_nonneg (hw k) (hcnn k)
  have hsum' : Summable fun k => w k * ∫ x in S, bandComponent l1 (a k) (θ k) (m k) x := by
    refine hsum.of_nonneg_of_le hnn fun k => ?_
    calc w k * ∫ x in S, bandComponent l1 (a k) (θ k) (m k) x
        ≤ w k * 1 := mul_le_mul_of_nonneg_left (hcle k) (hw k)
      _ = w k := mul_one _
  have hgnn : 0 ≤ ∫ x in S, gaussianPDFReal mu v x :=
    setIntegral_nonneg hS fun x _ => gaussianPDFReal_nonneg mu v x
  rw [bandLaw_apply hw0 hw (fun k => (hθ k).le) hl0 hl1 ha hm hatop hS,
    ← ENNReal.ofReal_tsum_of_nonneg hnn hsum',
    ← ENNReal.ofReal_add (mul_nonneg hw0 hgnn) (tsum_nonneg hnn),
    ENNReal.toReal_ofReal (add_nonneg (mul_nonneg hw0 hgnn) (tsum_nonneg hnn))]

/-- The total weight of the bands from the `k`th on. -/
theorem tsum_weight_add_eq (hsum : Summable w) (k : ℕ) :
    ∑' i : ℕ, w (i + k) = w k + ∑' j : ℕ, w (k + 1 + j) := by
  have hshift : Summable fun i : ℕ => w (i + k) :=
    hsum.comp_injective (add_left_injective k)
  have h0 := hshift.tsum_eq_zero_add
  have hre : ∑' i : ℕ, w (i + 1 + k) = ∑' j : ℕ, w (k + 1 + j) := by
    refine tsum_congr fun i => ?_
    congr 1
    omega
  rw [h0, hre, zero_add]

/-- **The mass the law puts on the reflected band interval `[-(t+ε),-t]`.**
The components below the `k`th band contribute nothing there; every component at
or above it has density at most `2M/((1-ℓ_1)a_k)`. -/
theorem bandLaw_reflected_Icc_le (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k)
    (hθ1 : ∀ k, 1 ≤ θ k) (hθ2 : ∀ k, θ k ≤ 2)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hsum : Summable w)
    (hsep : ∀ i j : ℕ, i < j → a i ≤ l1 * a j)
    {M : ℝ} (hM : ∀ x : ℝ, |bandBump x| ≤ M)
    {Cg lam : ℝ} (hCg : 0 < Cg) (hlam : 0 < lam)
    (hCbound : ∀ x : ℝ, gaussianPDFReal mu v x ≤ Cg * Real.exp (lam * x))
    (k : ℕ) {t ε : ℝ} (htlow : l1 * a k < t) (hε : 0 < ε) :
    (bandLaw w0 mu v l1 a w θ m (Icc (-(t + ε)) (-t))).toReal
      ≤ w0 * (Cg * Real.exp (-(lam * t))) * ε
        + 2 * M / ((1 - l1) * a k) * (w k + ∑' j : ℕ, w (k + 1 + j)) * ε := by
  have hθpos : ∀ j, 0 < θ j := fun j => lt_of_lt_of_le one_pos (hθ1 j)
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hak : 0 < a k := ha k
  have ht : 0 < t := lt_trans (mul_pos hl0 hak) htlow
  have hle : -(t + ε) ≤ -t := by linarith
  have hvol : volume.real (Icc (-(t + ε)) (-t)) = ε := by
    rw [Real.volume_real_Icc_of_le hle]; ring
  -- the positive summand
  have hgauss : ∫ x in Icc (-(t + ε)) (-t), gaussianPDFReal mu v x
      ≤ Cg * Real.exp (-(lam * t)) * ε := by
    have hmono : ∀ x ∈ Icc (-(t + ε)) (-t),
        gaussianPDFReal mu v x ≤ Cg * Real.exp (-(lam * t)) := by
      intro x hx
      refine (hCbound x).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCg.le
      have := mul_le_mul_of_nonneg_left hx.2 hlam.le
      linarith
    have hint := setIntegral_mono_on ((integrable_gaussianPDFReal mu v).integrableOn)
      (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc hmono
    refine hint.trans (le_of_eq ?_)
    rw [setIntegral_const, smul_eq_mul, hvol]
    ring
  -- the band components
  have hcnn : ∀ j, 0 ≤ ∫ x in Icc (-(t + ε)) (-t), bandComponent l1 (a j) (θ j) (m j) x :=
    fun j => setIntegral_nonneg measurableSet_Icc fun x _ =>
      bandComponent_nonneg (hθpos j).le hl1 (ha j) x
  have hcle : ∀ j, ∫ x in Icc (-(t + ε)) (-t), bandComponent l1 (a j) (θ j) (m j) x ≤ 1 := by
    intro j
    have h := setIntegral_le_integral (μ := (volume : Measure ℝ)) (s := Icc (-(t + ε)) (-t))
      (integrable_bandComponent (hm j) hl1 (ha j))
      (Filter.Eventually.of_forall fun x => bandComponent_nonneg (hθpos j).le hl1 (ha j) x)
    rwa [integral_bandComponent_eq_one (hθpos j) (hm j) hl0 hl1 (ha j)] at h
  have hnn : ∀ j, 0 ≤ w j * ∫ x in Icc (-(t + ε)) (-t), bandComponent l1 (a j) (θ j) (m j) x :=
    fun j => mul_nonneg (hw j) (hcnn j)
  have hsum' : Summable fun j =>
      w j * ∫ x in Icc (-(t + ε)) (-t), bandComponent l1 (a j) (θ j) (m j) x := by
    refine hsum.of_nonneg_of_le hnn fun j => ?_
    calc w j * ∫ x in Icc (-(t + ε)) (-t), bandComponent l1 (a j) (θ j) (m j) x
        ≤ w j * 1 := mul_le_mul_of_nonneg_left (hcle j) (hw j)
      _ = w j := mul_one _
  set D : ℝ := 2 * M / ((1 - l1) * a k) with hD
  -- below the band nothing contributes
  have hlow : ∑ i ∈ Finset.range k,
      w i * ∫ x in Icc (-(t + ε)) (-t), bandComponent l1 (a i) (θ i) (m i) x = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hik : i < k := Finset.mem_range.mp hi
    have hai : a i ≤ l1 * a k := hsep i k hik
    have hzero : ∫ x in Icc (-(t + ε)) (-t), bandComponent l1 (a i) (θ i) (m i) x = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      exact bandComponent_eq_zero_of_le hl1 (ha i) (by have := hx.2; linarith)
    rw [hzero, mul_zero]
  -- at or above the band every component has density at most `D`
  have hhigh : ∀ i : ℕ,
      w (i + k) * ∫ x in Icc (-(t + ε)) (-t),
          bandComponent l1 (a (i + k)) (θ (i + k)) (m (i + k)) x
        ≤ w (i + k) * (D * ε) := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (hw (i + k))
    have hakj : a k ≤ a (i + k) := by
      rcases Nat.eq_or_lt_of_le (Nat.le_add_left k i) with h | h
      · exact le_of_eq (congrArg a h)
      · exact le_trans (hsep k (i + k) h) (by nlinarith [ha (i + k)])
    have hpk : (0 : ℝ) < (1 - l1) * a k := mul_pos (by linarith) hak
    have hkj : (1 - l1) * a k ≤ (1 - l1) * a (i + k) := by nlinarith
    have hDle : 2 * M / ((1 - l1) * a (i + k)) ≤ D :=
      div_le_div_of_nonneg_left (by linarith : (0 : ℝ) ≤ 2 * M) hpk hkj
    have hmono : ∀ x ∈ Icc (-(t + ε)) (-t),
        bandComponent l1 (a (i + k)) (θ (i + k)) (m (i + k)) x ≤ D := by
      intro x _
      refine le_trans (bandComponent_le (hθ1 _) (hθ2 _) (hm _) hl1 (ha _) hM x) ?_
      rw [bandWidth]
      exact hDle
    have hint := setIntegral_mono_on
      ((integrable_bandComponent (hm (i + k)) hl1 (ha (i + k))).integrableOn)
      (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc hmono
    refine hint.trans (le_of_eq ?_)
    rw [setIntegral_const, smul_eq_mul, hvol]
    ring
  have hshift : Summable fun i : ℕ => w (i + k) := hsum.comp_injective (add_left_injective k)
  have hbandsum : ∑' j,
      w j * ∫ x in Icc (-(t + ε)) (-t), bandComponent l1 (a j) (θ j) (m j) x
      ≤ D * (w k + ∑' j : ℕ, w (k + 1 + j)) * ε := by
    have hsplit := hsum'.sum_add_tsum_nat_add k
    have hshift' : Summable fun i : ℕ =>
        w (i + k) * ∫ x in Icc (-(t + ε)) (-t),
          bandComponent l1 (a (i + k)) (θ (i + k)) (m (i + k)) x := by
      have := hsum'.comp_injective (add_left_injective k)
      simpa [Function.comp_def] using this
    have hcmp : ∑' i : ℕ, w (i + k) * ∫ x in Icc (-(t + ε)) (-t),
          bandComponent l1 (a (i + k)) (θ (i + k)) (m (i + k)) x
        ≤ ∑' i : ℕ, w (i + k) * (D * ε) :=
      Summable.tsum_le_tsum hhigh hshift' (hshift.mul_right (D * ε))
    have hval : ∑' i : ℕ, w (i + k) * (D * ε) = (w k + ∑' j : ℕ, w (k + 1 + j)) * (D * ε) := by
      rw [tsum_mul_right, tsum_weight_add_eq hsum k]
    rw [← hsplit, hlow, zero_add]
    calc ∑' i : ℕ, w (i + k) * ∫ x in Icc (-(t + ε)) (-t),
            bandComponent l1 (a (i + k)) (θ (i + k)) (m (i + k)) x
        ≤ ∑' i : ℕ, w (i + k) * (D * ε) := hcmp
      _ = (w k + ∑' j : ℕ, w (k + 1 + j)) * (D * ε) := hval
      _ = D * (w k + ∑' j : ℕ, w (k + 1 + j)) * ε := by ring
  rw [bandLaw_toReal hw0 hw hθpos hl0 hl1 ha hm hatop hsum measurableSet_Icc]
  have hg : w0 * ∫ x in Icc (-(t + ε)) (-t), gaussianPDFReal mu v x
      ≤ w0 * (Cg * Real.exp (-(lam * t)) * ε) := mul_le_mul_of_nonneg_left hgauss hw0
  calc w0 * (∫ x in Icc (-(t + ε)) (-t), gaussianPDFReal mu v x)
        + ∑' j, w j * ∫ x in Icc (-(t + ε)) (-t), bandComponent l1 (a j) (θ j) (m j) x
      ≤ w0 * (Cg * Real.exp (-(lam * t)) * ε)
        + D * (w k + ∑' j : ℕ, w (k + 1 + j)) * ε := add_le_add hg hbandsum
    _ = w0 * (Cg * Real.exp (-(lam * t))) * ε
        + 2 * M / ((1 - l1) * a k) * (w k + ∑' j : ℕ, w (k + 1 + j)) * ε := by
        rw [hD]; ring

/-- **The Step-1 density bound** (`eq:dgt4-band-density`). -/
theorem bandDensity_law (P : BandParameters) (hA : P.A⁻¹ ≤ P.l1)
    (m : ℕ → ℕ) (hm : ∀ k, 0 < m k) (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (htot : ∑' k, P.weight k ≤ 1) :
    BandDensity P (P.law m mu v) := by
  classical
  set lam : ℝ := 2 / P.l1 with hlamdef
  have hl0 : 0 < P.l1 := P.hl1.1
  have hl1 : P.l1 < 1 := P.hl1.2
  have hl1' : (0 : ℝ) < 1 - P.l1 := by linarith
  have hlam : 0 < lam := by positivity
  have hlaml1 : lam * P.l1 = 2 := by
    simp only [hlamdef]
    field_simp
  set w0 : ℝ := 1 - ∑' k, P.weight k with hw0def
  have hw0 : 0 ≤ w0 := by simp only [hw0def]; linarith
  obtain ⟨Cg, hCg, hCbound⟩ := exists_gaussianPDFReal_le_exp_mul (mu := mu) (v := v) hv lam
  obtain ⟨M, hM1, hM⟩ := exists_bandBump_bound
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
  have hsep : ∀ i j : ℕ, i < j → P.level i ≤ P.l1 * P.level j := fun _ _ hij =>
    P.level_sep hA hij
  set K : ℝ := w0 * Cg with hK
  have hK0 : 0 ≤ K := mul_nonneg hw0 hCg.le
  have hCfin : (0 : ℝ) < 1 + 4 * M / (1 - P.l1) := by
    have h4 : (0 : ℝ) < 4 * M / (1 - P.l1) := div_pos (by linarith) hl1'
    linarith
  refine ⟨1 + 4 * M / (1 - P.l1), hCfin, ?_⟩
  have hlim : Tendsto (fun k : ℕ =>
      K * Real.exp (-(lam * (P.l1 * P.level k))) * P.level k / P.weight k) atTop (𝓝 0) := by
    have hrw : ∀ k : ℕ,
        K * Real.exp (-(lam * (P.l1 * P.level k))) * P.level k / P.weight k
          = (K / P.c0) * (P.level k * Real.exp (-(P.level k))) := by
      intro k
      rw [BandParameters.weight, show -(lam * (P.l1 * P.level k)) = -(2 * P.level k) by
        rw [← mul_assoc, hlaml1]]
      field_simp [P.hc0.ne', Real.exp_ne_zero]
      rw [show -(2 * P.level k) = -(P.level k) + -(P.level k) by ring, Real.exp_add]
      ring
    have hbase : Tendsto (fun s : ℝ => s * Real.exp (-s)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hcomp := (hbase.comp P.level_tendsto).const_mul (K / P.c0)
    rw [mul_zero] at hcomp
    exact hcomp.congr fun k => (hrw k).symm
  filter_upwards [hlim.eventually_lt_const one_pos,
    P.weight_tail_ratio_tendsto.eventually_lt_const one_pos] with k hk hktail t htlow hthigh ε hε
  have hak : 0 < P.level k := P.level_pos k
  have hwk : 0 < P.weight k := P.weight_pos k
  have ht : 0 < t := lt_trans (mul_pos hl0 hak) htlow
  have hmass := bandLaw_reflected_Icc_le (w0 := w0) (mu := mu) (v := v) (l1 := P.l1)
    (a := P.level) (w := P.weight) (θ := P.theta) (m := m) hw0
    (fun j => (P.weight_pos j).le) (fun j => (P.htheta j).1) (fun j => (P.htheta j).2)
    hl0 hl1 P.level_pos hm P.level_tendsto P.summable_weight hsep hM hCg hlam hCbound k htlow hε
  -- the positive summand is `o(ω_k/a_k)`
  have hdecay : Real.exp (-(lam * t)) ≤ Real.exp (-(lam * (P.l1 * P.level k))) := by
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left htlow.le hlam.le
    linarith
  have hKE : K * Real.exp (-(lam * (P.l1 * P.level k))) ≤ P.weight k / P.level k := by
    rw [le_div_iff₀ hak]
    have h1 := hk.le
    rw [div_le_one hwk] at h1
    exact h1
  have hgpart : w0 * (Cg * Real.exp (-(lam * t))) ≤ P.weight k / P.level k := by
    refine le_trans ?_ hKE
    have hrw : w0 * (Cg * Real.exp (-(lam * t))) = K * Real.exp (-(lam * t)) := by
      rw [hK]; ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hdecay hK0
  -- the bands at or above the `k`th carry at most `2ω_k`
  have htail : ∑' j : ℕ, P.weight (k + 1 + j) ≤ P.weight k := by
    have h1 := hktail.le
    rw [div_le_one hwk] at h1
    exact h1
  have hbpart : 2 * M / ((1 - P.l1) * P.level k) *
      (P.weight k + ∑' j : ℕ, P.weight (k + 1 + j))
      ≤ 4 * M / (1 - P.l1) * (P.weight k / P.level k) := by
    have hpk : (0 : ℝ) < (1 - P.l1) * P.level k := mul_pos hl1' hak
    have h2 : P.weight k + ∑' j : ℕ, P.weight (k + 1 + j) ≤ 2 * P.weight k := by linarith
    have h3 : 2 * M / ((1 - P.l1) * P.level k) * (P.weight k + ∑' j : ℕ, P.weight (k + 1 + j))
        ≤ 2 * M / ((1 - P.l1) * P.level k) * (2 * P.weight k) :=
      mul_le_mul_of_nonneg_left h2 (div_nonneg (by linarith) hpk.le)
    refine h3.trans (le_of_eq ?_)
    field_simp
    ring
  have hstep : (((P.law m mu v) (Icc (-(t + ε)) (-t))).toReal) / ε
      ≤ w0 * (Cg * Real.exp (-(lam * t)))
        + 2 * M / ((1 - P.l1) * P.level k) *
          (P.weight k + ∑' j : ℕ, P.weight (k + 1 + j)) := by
    rw [div_le_iff₀ hε]
    refine hmass.trans (le_of_eq ?_)
    ring
  calc (((P.law m mu v) (Icc (-(t + ε)) (-t))).toReal) / ε
      ≤ w0 * (Cg * Real.exp (-(lam * t)))
        + 2 * M / ((1 - P.l1) * P.level k) *
          (P.weight k + ∑' j : ℕ, P.weight (k + 1 + j)) := hstep
    _ ≤ P.weight k / P.level k + 4 * M / (1 - P.l1) * (P.weight k / P.level k) :=
        add_le_add hgpart hbpart
    _ = (1 + 4 * M / (1 - P.l1)) * P.weight k / P.level k := by ring

end Sandpile.Support
